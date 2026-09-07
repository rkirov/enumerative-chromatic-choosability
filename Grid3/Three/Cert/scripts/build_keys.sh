#!/bin/bash
# build Keys/K*.lean with index ≡ $1 (mod $2) sequentially; skip built ones; wait if RAM is low
cd "$(dirname "${BASH_SOURCE[0]}")/../../../.."
for i in $(seq 0 38); do
  if [ $((i % $2)) -ne $1 ]; then continue; fi
  b=$(printf 'K%02d' $i)
  if [ -f .lake/build/lib/lean/Grid3/Three/Cert/Keys/$b.olean ]; then echo "$b already built"; continue; fi
  if pgrep -f "Cert/Keys/$b.lean" > /dev/null; then echo "$b in progress elsewhere"; continue; fi
  while [ $(free -m | awk 'NR==2{print $7}') -lt 3000 ] || [ $(df --output=avail -m / | tail -1) -lt 150 ]; do sleep 20; done
  t0=$(date +%s)
  nice -n 5 lake build Grid3.Three.Cert.Keys.$b > ${TMPDIR:-/tmp}/build_$b.log 2>&1; rc=$?
  echo "$b exit=$rc $(( $(date +%s) - t0 ))s $(df --output=avail -m / | tail -1)MB-free"
done
echo "BUILDER $1 DONE"
