#!/usr/bin/env bash
set -euo pipefail

SPEC_OUT="${1:-mac_spec.txt}"

echo "Writing macOS hardware/software specifications to: ${SPEC_OUT}"

{
  echo "=== macOS ==="
  sw_vers
  uname -a

  echo
  echo "=== Hardware Overview ==="
  system_profiler SPHardwareDataType

  echo
  echo "=== CPU ==="
  sysctl -n machdep.cpu.brand_string 2>/dev/null || true
  echo "Physical cores: $(sysctl -n hw.physicalcpu)"
  echo "Logical cores:  $(sysctl -n hw.logicalcpu)"

  echo
  echo "=== Memory ==="
  echo "Bytes: $(sysctl -n hw.memsize)"
  system_profiler SPMemoryDataType 2>/dev/null || true

  echo
  echo "=== Storage ==="
  system_profiler SPStorageDataType
  df -h

  echo
  echo "=== Graphics ==="
  system_profiler SPDisplaysDataType

  echo
  echo "=== Power ==="
  system_profiler SPPowerDataType
} > "${SPEC_OUT}"

echo
echo "Specification written to: ${SPEC_OUT}"
echo "----------------------------------------"
cat "${SPEC_OUT}"
echo "----------------------------------------"