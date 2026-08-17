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
trap 'rm -rf "$WORK"' EXIT

rm -f "$OUT.key" "$OUT.key.pub"
ssh-keygen -q -t ed25519 -N '' -f "$OUT.key"
sed "s|@PUBKEY@|$(cat "$OUT.key.pub")|" "$DIR/autounattend.xml" > "$WORK/autounattend.xml"
"$MKISO" -quiet -o "$WORK/answer.iso" -volid ANSWER -joliet -rock "$WORK/autounattend.xml"

qemu-img create -q -f qcow2 "$OUT.tmp" 64G

# Headless: Windows Setup finds autounattend.xml on the answer CD, installs,
# provisions at first logon, and shuts down. QEMU's defaults are what we need:
# mid-install resets reboot the guest, and the final power-off exits qemu
# (-no-reboot is deliberately NOT passed; it would exit at the first
# mid-install reboot and leave a half-installed image).
echo "installing Windows (headless; 30-60 minutes)..."
qemu-system-x86_64 -enable-kvm -machine q35 -cpu host -smp 4 -m 8192 \
  -drive file="$OUT.tmp",if=ide \
  -drive file="$ISO",media=cdrom \
  -drive file="$WORK/answer.iso",media=cdrom \
  -netdev user,id=n0 -device e1000e,netdev=n0 \
  -display none -serial null

mv "$OUT.tmp" "$OUT"
echo "image: $OUT"
echo "key:   $OUT.key"
echo "export FORMAL_E2E_WINDOWS_IMAGE=$OUT"
