#!/usr/bin/env bash
# Build the proved model/transport staging modules without the full certificate enumeration.
# Usage from any directory: bash k3_entropy/check_model.sh [output_directory]
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
model_build_dir="${1:-$(mktemp -d /tmp/grid-ecc-model.XXXXXX)}"
mkdir -p "$model_build_dir/k3_entropy"
model_build_dir="$(cd -- "$model_build_dir" && pwd)"
export LEAN_PATH="$model_build_dir${LEAN_PATH:+:$LEAN_PATH}"

lake build Grid3.Three.Cert.Parry Grid3.Main
for model_module in Grid3Entropy Grid3Model CertifiedEntropy KernelTransport ModelAssembly GraphBridge FinalModel ModelChecks; do
  printf 'Checking %s\n' "$model_module"
  lake env lean -o "$model_build_dir/k3_entropy/$model_module.olean" "k3_entropy/$model_module.lean"
done
printf 'Model checks passed. Build artifacts: %s\n' "$model_build_dir"
