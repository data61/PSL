#!/usr/bin/env bash
set -euo pipefail

SPEC_OUT="${1:-laptop_spec.txt}"
DMIDECODE_OUT="${2:-laptop_dmidecode.txt}"

echo "Writing basic hardware/software spec to: ${SPEC_OUT}"

{
  echo "=== OS ==="
  lsb_release -a 2>/dev/null || cat /etc/os-release
  uname -a

  echo
  echo "=== Machine ==="
  hostnamectl || true

  echo
  echo "=== CPU ==="
  lscpu || true

  echo
  echo "=== Memory ==="
  free -h || true
  grep MemTotal /proc/meminfo || true

  echo
  echo "=== Disk / Filesystems ==="
  lsblk -o NAME,MODEL,SIZE,TYPE,FSTYPE,MOUNTPOINTS || true
  df -h || true

  echo
  echo "=== GPU ==="
  lspci | grep -Ei 'vga|3d|display|nvidia|amd|intel' || true

  echo
  echo "=== Detailed GPU / PCI ==="
  lspci -nnk | grep -A3 -Ei 'vga|3d|display' || true

  echo
  echo "=== CPU frequency ==="
  cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || true
  cat /sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq 2>/dev/null || true
} > "${SPEC_OUT}"

echo
echo "Basic spec collected."
echo "Preview:"
echo "----------------------------------------"
cat "${SPEC_OUT}"
echo "----------------------------------------"

echo
echo "Trying to collect DMI/SMBIOS details into: ${DMIDECODE_OUT}"
echo "This may ask for your sudo password."

if command -v dmidecode >/dev/null 2>&1; then
  if sudo dmidecode -t system -t processor -t memory > "${DMIDECODE_OUT}"; then
    echo "DMI/SMBIOS details written to: ${DMIDECODE_OUT}"
  else
    echo "Could not collect dmidecode output. This is optional."
  fi
else
  echo "dmidecode is not installed. To install it on Ubuntu:"
  echo "  sudo apt update && sudo apt install dmidecode"
fi

echo
echo "Done."
echo "Please upload or paste:"
echo "  ${SPEC_OUT}"
echo "and, if it was created successfully:"
echo "  ${DMIDECODE_OUT}"
