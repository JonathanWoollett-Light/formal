#!/bin/sh
# Builds the factory-default Windows guest image the `factory_default_windows`
# test boots (DEVELOPMENT.md 6.2). One-time, on a KVM host:
#
#   tests/setup_e2e/windows/build-image.sh <windows-server-eval.iso> <out.qcow2>
#
# The unattended install (autounattend.xml) leaves the OS factory-default
# except for what makes it drivable headlessly: OpenSSH with the keypair this
# script generates next to the image (<out>.key / <out>.key.pub - a throwaway
# for a loopback-bound VM, not a secret), silent UAC elevation, autologon, no
# sleep. The install ends by powering the VM off; that is when the image is
# ready. Expect 30-60 minutes.
#
# Then:  export FORMAL_E2E_WINDOWS_IMAGE=<out.qcow2>
set -eu

ISO="$1"
OUT="$2"
DIR="$(cd "$(dirname "$0")" && pwd)"

command -v qemu-system-x86_64 >/dev/null 2>&1 || { echo "missing qemu-system-x86_64:  sudo apt-get install -y qemu-system-x86"; exit 1; }
command -v qemu-img >/dev/null 2>&1 || { echo "missing qemu-img:  sudo apt-get install -y qemu-utils"; exit 1; }
MKISO="$(command -v genisoimage || command -v mkisofs)" || { echo "missing genisoimage:  sudo apt-get install -y genisoimage"; exit 1; }
[ -r /dev/kvm ] && [ -w /dev/kvm ] || { echo "no /dev/kvm access:  sudo usermod -aG kvm \$USER  (then re-login)"; exit 1; }

WORK="$(mktemp -d)"
# (chmod first: files extracted from the ISO are read-only.)
trap 'chmod -R u+w "$WORK" 2>/dev/null; rm -rf "$WORK"' EXIT
# A killed build must not be published: qemu exits 0 on SIGTERM (a graceful
# guest shutdown and an operator kill are indistinguishable by exit code), so
# killing the script cleans up the partial disk and aborts before the mv.
# (If you kill the qemu process directly instead, delete "$OUT.tmp" yourself.)
trap 'rm -f "$OUT.tmp"; exit 1' INT TERM

rm -f "$OUT.key" "$OUT.key.pub"
ssh-keygen -q -t ed25519 -N '' -f "$OUT.key"
sed "s|@PUBKEY@|$(cat "$OUT.key.pub")|" "$DIR/autounattend.xml" > "$WORK/autounattend.xml"

# The NetKVM (virtio network) driver rides on the answer CD and is installed
# by a first-logon command: Server 2022's in-box e1000e is unreliable under
# qemu (no DHCP), while virtio-net is proven against this host's slirp by the
# Linux e2e runs. The guest therefore boots with -device virtio-net-pci and
# has no network until that pnputil step - nothing before it needs any.
VIRTIO_ISO="${3:-$HOME/.cache/formal-e2e/images/virtio-win.iso}"
[ -r "$VIRTIO_ISO" ] || { echo "missing virtio-win.iso (NetKVM driver source):  curl -L -o '$VIRTIO_ISO' https://fedorapeople.org/groups/virt/virtio-win/direct-downloads/stable-virtio/virtio-win.iso"; exit 1; }
command -v bsdtar >/dev/null 2>&1 || { echo "missing bsdtar (extracts the driver from the iso):  sudo apt-get install -y libarchive-tools"; exit 1; }
mkdir -p "$WORK/extract"
# --exclude the Readme: the ISO stores it as a hard link into a directory
# outside this pattern, which bsdtar reports as an error.
bsdtar -xf "$VIRTIO_ISO" -C "$WORK/extract" --exclude '*.md' 'NetKVM/2k22/amd64'
[ -f "$WORK/extract/NetKVM/2k22/amd64/netkvm.inf" ] || { echo "netkvm.inf did not extract from $VIRTIO_ISO"; exit 1; }
# bsdtar preserves the ISO's read-only modes, which would break the
# answer-ISO build.
chmod -R u+w "$WORK/extract"
"$MKISO" -quiet -o "$WORK/answer.iso" -volid ANSWER -joliet -rock "$WORK/autounattend.xml" "$WORK/extract"

qemu-img create -q -f qcow2 "$OUT.tmp" 64G

# Headless: Windows Setup finds autounattend.xml on the answer CD, installs,
# provisions at first logon, and shuts down. QEMU's defaults are what we need:
# mid-install resets reboot the guest, and the final power-off exits qemu
# (-no-reboot is deliberately NOT passed; it would exit at the first
# mid-install reboot and leave a half-installed image). The longest quiet
# stretch is the first-logon `Add-WindowsCapability` for OpenSSH, which goes
# through Windows Update and alone can take 10-40 minutes. Watch it live via
# the serial log next to the image, or a VNC viewer on 127.0.0.1:5947.
echo "installing Windows (headless; 30-90 minutes; serial: $OUT.serial.log, vnc: 127.0.0.1:5947)..."
qemu-system-x86_64 -enable-kvm -machine q35 -cpu host -smp "$(nproc)" -m 8192 \
  -drive file="$OUT.tmp",if=ide,cache=unsafe \
  -drive file="$ISO",media=cdrom \
  -drive file="$WORK/answer.iso",media=cdrom \
  -netdev user,id=n0 -device virtio-net-pci,netdev=n0 \
  -display none -vnc 127.0.0.1:47 -serial file:"$OUT.serial.log"

mv "$OUT.tmp" "$OUT"
echo "image: $OUT"
echo "key:   $OUT.key"
echo "export FORMAL_E2E_WINDOWS_IMAGE=$OUT"
