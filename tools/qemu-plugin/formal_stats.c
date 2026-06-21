/*
 * formal_stats: a tiny QEMU TCG plugin for the `formal` integration tests.
 *
 * The QEMU-booting tests (tests/common/mod.rs) load this to measure, for a
 * guest run:
 *
 *   - the exact number of guest instructions executed (counted per-vCPU and
 *     summed, so multi-hart runs report the combined total), and
 *   - the guest memory working set over execution time: the set of distinct
 *     4 KiB pages the guest touches (instruction fetches + non-IO data
 *     accesses). Each time that set grows, a `grow` record (instructions so
 *     far, page count) is emitted, which fully describes the monotonic
 *     footprint curve. The host (the Rust harness) turns those records into
 *     the peak footprint and the time-weighted percentiles of memory usage.
 *
 * MMIO accesses (e.g. the UART at 0x10000000) are excluded from the footprint:
 * they touch device registers, not memory. Wall-clock execution time is
 * measured by the host around the QEMU invocation, not here.
 *
 * Output is written, one `key values...` line per record, to the file named by
 * the `out=<path>` argument (falling back to QEMU's plugin log if it cannot be
 * opened):
 *
 *   insns <total>
 *   vcpu <index> <insns>          (one per vCPU that executed anything)
 *   grow <insns_so_far> <pages>   (one per footprint growth, in order)
 *   peak_pages <count>
 *   page_size <bytes>
 *
 * It is plain C (no glib) so it builds against just qemu-plugin.h with gcc; the
 * matching header is fetched and the .so cached by the test harness. The plugin
 * only observes, so it never changes guest behaviour (the pinned serial output
 * and fault counts are unaffected).
 */
#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <qemu-plugin.h>

/*
 * The QEMU plugin API version this plugin advertises. It defaults to the
 * header's own version, but the test harness overrides it with
 * -DFORMAL_PLUGIN_VERSION=<n> to match whatever the locally installed QEMU
 * requires (some distributions, e.g. Debian's QEMU 8.2.2, backport the v2 API
 * and reject v1 plugins). Only the long-stable subset of the API is used here
 * (instruction/translate/memory callbacks, hwaddr queries, atexit), and those
 * signatures are identical across versions, so advertising a higher version
 * against this header is safe and avoids the newer header's glib dependency.
 */
#ifndef FORMAL_PLUGIN_VERSION
#define FORMAL_PLUGIN_VERSION QEMU_PLUGIN_VERSION
#endif

QEMU_PLUGIN_EXPORT int qemu_plugin_version = FORMAL_PLUGIN_VERSION;

/* 4 KiB pages: the granularity of "memory in use" (what an OS would map). */
#define PAGE_BITS 12

/* Per-vCPU instruction counters. Each slot is written only by its own vCPU
 * thread, so the counts need no atomics; the cap comfortably exceeds any hart
 * count these tests boot. */
#define MAX_VCPUS 64
static uint64_t vcpu_insns[MAX_VCPUS];

/* Open-addressing hash set of touched page numbers (stored as page+1 so 0 is
 * the empty sentinel; guest RAM sits at 0x80000000 so page 0 never appears).
 * The footprints here are tiny, so a fixed 2^18-slot table stays near-empty and
 * lookups stay O(1) without ever resizing.
 *
 * The slots are atomic so the (very hot, billions of calls under MTTCG) memory
 * callback can check membership lock-free: the overwhelmingly common case is a
 * page already in the set, which is just a relaxed atomic load. Only a genuine
 * miss takes `lock` to insert authoritatively (inserts are serialized, so
 * `page_count` and the growth curve stay exact). */
#define SET_CAP (1u << 18)
static _Atomic uint64_t *page_slots;
static uint64_t page_count;

/* The footprint growth curve: one entry each time a new page is touched. */
struct grow_event {
    uint64_t insns;
    uint64_t pages;
};
static struct grow_event *grow_events;
static size_t grow_len;
static size_t grow_cap;

static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static bool system_emulation;
static char *out_path;

static uint64_t total_insns(void)
{
    uint64_t total = 0;
    for (int i = 0; i < MAX_VCPUS; i++) {
        total += vcpu_insns[i];
    }
    return total;
}

static inline uint64_t mix64(uint64_t x)
{
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53ULL;
    x ^= x >> 33;
    return x;
}

/* Record a footprint growth. Caller holds `lock`. */
static void record_growth(void)
{
    if (grow_len == grow_cap) {
        grow_cap = grow_cap ? grow_cap * 2 : 64;
        grow_events = realloc(grow_events, grow_cap * sizeof(*grow_events));
        if (!grow_events) {
            return; /* out of memory: drop the curve but keep counting */
        }
    }
    grow_events[grow_len].insns = total_insns();
    grow_events[grow_len].pages = page_count;
    grow_len++;
}

/* Fold a page into the working set, recording a growth event on first sight.
 *
 * Hot path (page already present): a lock-free relaxed probe of the atomic
 * slots, no lock taken. Cold path (a genuinely new page, rare once the small
 * footprint is established): take `lock` and re-probe authoritatively so inserts
 * are serialized and `page_count`/the growth curve stay exact even under MTTCG. */
static void touch_page(uint64_t page)
{
    const uint64_t key = page + 1;
    const uint64_t mask = SET_CAP - 1;
    uint64_t i = mix64(page) & mask;
    for (;;) {
        uint64_t v = atomic_load_explicit(&page_slots[i], memory_order_relaxed);
        if (v == key) {
            return; /* already counted */
        }
        if (v == 0) {
            break; /* maybe new: confirm and insert under the lock */
        }
        i = (i + 1) & mask;
    }
    pthread_mutex_lock(&lock);
    uint64_t j = mix64(page) & mask;
    for (;;) {
        uint64_t v = atomic_load_explicit(&page_slots[j], memory_order_relaxed);
        if (v == key) {
            break; /* inserted by another thread in the meantime */
        }
        if (v == 0) {
            atomic_store_explicit(&page_slots[j], key, memory_order_release);
            page_count++;
            record_growth();
            break;
        }
        j = (j + 1) & mask;
    }
    pthread_mutex_unlock(&lock);
}

/* Per-TB execution: add the block's instruction count to this vCPU's tally.
 * The instruction count rides in `udata` (set at translation). */
static void on_tb_exec(unsigned int vcpu_index, void *udata)
{
    if (vcpu_index < MAX_VCPUS) {
        vcpu_insns[vcpu_index] += (uint64_t)(uintptr_t)udata;
    }
}

/* Per data access: fold the (non-IO) target page into the working set. */
static void on_mem(unsigned int vcpu_index, qemu_plugin_meminfo_t info,
                   uint64_t vaddr, void *udata)
{
    (void)vcpu_index;
    (void)udata;
    if (system_emulation) {
        struct qemu_plugin_hwaddr *hw = qemu_plugin_get_hwaddr(info, vaddr);
        if (hw && qemu_plugin_hwaddr_is_io(hw)) {
            return; /* device register, not memory */
        }
    }
    touch_page(vaddr >> PAGE_BITS);
}

/* Per translated block: arrange instruction counting, fold in the block's code
 * pages, and instrument each instruction's data accesses. */
static void on_tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
    (void)id;
    size_t n = qemu_plugin_tb_n_insns(tb);
    qemu_plugin_register_vcpu_tb_exec_cb(tb, on_tb_exec, QEMU_PLUGIN_CB_NO_REGS,
                                         (void *)(uintptr_t)n);
    for (size_t i = 0; i < n; i++) {
        struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
        touch_page(qemu_plugin_insn_vaddr(insn) >> PAGE_BITS);
        qemu_plugin_register_vcpu_mem_cb(insn, on_mem, QEMU_PLUGIN_CB_NO_REGS,
                                         QEMU_PLUGIN_MEM_RW, NULL);
    }
}

static void on_plugin_exit(qemu_plugin_id_t id, void *p)
{
    (void)id;
    (void)p;
    FILE *f = out_path ? fopen(out_path, "w") : NULL;
    if (!f) {
        /* Fall back to QEMU's plugin log, line by line. */
        char line[128];
        snprintf(line, sizeof(line), "insns %" PRIu64 "\n", total_insns());
        qemu_plugin_outs(line);
        snprintf(line, sizeof(line), "peak_pages %" PRIu64 "\n", page_count);
        qemu_plugin_outs(line);
        snprintf(line, sizeof(line), "page_size %d\n", 1 << PAGE_BITS);
        qemu_plugin_outs(line);
        return;
    }
    fprintf(f, "insns %" PRIu64 "\n", total_insns());
    for (int i = 0; i < MAX_VCPUS; i++) {
        if (vcpu_insns[i]) {
            fprintf(f, "vcpu %d %" PRIu64 "\n", i, vcpu_insns[i]);
        }
    }
    for (size_t i = 0; i < grow_len; i++) {
        fprintf(f, "grow %" PRIu64 " %" PRIu64 "\n", grow_events[i].insns,
                grow_events[i].pages);
    }
    fprintf(f, "peak_pages %" PRIu64 "\n", page_count);
    fprintf(f, "page_size %d\n", 1 << PAGE_BITS);
    fclose(f);
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
                                           const qemu_info_t *info, int argc,
                                           char **argv)
{
    system_emulation = info->system_emulation;
    page_slots = calloc(SET_CAP, sizeof(*page_slots));
    if (!page_slots) {
        return -1;
    }
    for (int i = 0; i < argc; i++) {
        if (strncmp(argv[i], "out=", 4) == 0) {
            free(out_path);
            out_path = strdup(argv[i] + 4);
        }
    }
    qemu_plugin_register_vcpu_tb_trans_cb(id, on_tb_trans);
    qemu_plugin_register_atexit_cb(id, on_plugin_exit, NULL);
    return 0;
}
