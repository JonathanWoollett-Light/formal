# Deploying `formal` as a cloud-portable remote-verification service

This directory holds the deployment target chosen in the HPC plan
(`../plan.md`, and the plan file under `~/.claude/plans/`): **Kubernetes + the
Kubeflow MPI Operator**, deployable unchanged to EKS / AKS / GKE / on-prem so the
job can chase the cheapest cloud. It works here precisely because the verifier is
**bandwidth-bound, not latency-bound** (coarse, idle-gated continuation steals; a
small control plane; one union all-reduce), so it needs only plain high-bandwidth
Ethernet pods, not a cloud-specific RDMA fabric.

## Status (what is and is not validated)

The **logic** the distributed backend needs is implemented and unit-tested in
`src/explore.rs` against the sequential oracle (`tests/parallel_oracle_crosscheck`):

- pointer-free, `serde`-serializable `Continuation`s;
- `verify_configuration_parallel` — a single configuration's frontier explored
  across a rayon pool, order-independent;
- `verify_configuration_distributed_sim` — the same search where every
  continuation crosses a `postcard` serialize/deserialize round-trip, exactly as
  it would migrating between nodes, with the commutative-union reduce;
- **`src/dist.rs` (real MPI, `--features hpc`)** — the outer configuration sweep
  across actual MPI ranks (rsmpi). `formal mpi-selftest` under `mpirun -n N`
  verifies `racy_store_inferred` and infers `value:Gu32` identically at 1, 4, and
  24 ranks, matching the sequential oracle. Build/run on Linux or under WSL:
  `cargo build --features hpc` then `mpirun -n <N> target/debug/formal mpi-selftest`
  (`build.rs` provisions the system MPI + libclang when `--features hpc` is set).

What remains, and **requires a multi-node cluster to validate** (so it is not
exercised by `cargo test`):

- real MPI migration of **continuations** for a single huge configuration
  (`rsmpi` point-to-point + a lifeline work-stealing overlay + a Mattern credit
  termination detector). The continuation bytes and the union reduce are already
  validated by `verify_configuration_distributed_sim`; only the byte *transport*
  differs from the working outer-sweep backend;
- this `deploy/` manifest set running on a real MPI Operator cluster.

So the MPI backend itself is implemented and exercised under `mpirun` on one
host; the manifests here are the ready-to-use multi-node target.

## Pieces

- `Dockerfile` — builds the `formal` binary into an MPI-enabled runtime image.
- `mpijob.yaml` — a Kubeflow `MPIJob` (Launcher + Workers) with Volcano gang
  scheduling, the production pattern (a partially-placed MPI job deadlocks, and
  Kueue does not gang natively, so Volcano provides the gang guarantee).

## Operating notes (from the plan)

- **Node profile:** AMD EPYC Genoa(-X) class, 64-192 vCPU, 2-4 GiB RAM/vCPU
  (large L3 + high memory bandwidth serve the clone/serialize/BTreeMap-merge hot
  paths), 50-100 GbE Ethernet, default CNI only. Pin one rank per NUMA socket.
- **Gang scheduling is mandatory** (Volcano); layer Kueue on top for quota.
- **Autoscale** a high-bandwidth node pool to zero between jobs (Karpenter on
  EKS/AKS; Node Auto-Provisioning on GKE). Keep a small warm pool for sub-5-minute
  jobs (cold start is 60-180 s).
- **On-demand, not spot:** with no in-algorithm fault tolerance a reclaimed node
  stalls the gang; idempotent whole-job retry makes spot correct only for short
  jobs.
- **Right-size** the node count from an estimated step count; **refuse provably
  infeasible jobs** (more nodes give a constant factor, never exponent relief).
