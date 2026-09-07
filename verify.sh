#!/usr/bin/env bash
# Run leanprover/comparator against this repository's `comparator/` workspace, mirroring
# lean-eval's own CI check: a Challenge.lean of placeholder statements, a Submission.lean that
# delegates to the real `ListColoring` library, and the real comparator (statement match +
# permitted-axiom check + kernel replay via lean4export, in a landrun sandbox).
#
# DEVIATION from lean-eval: the second, independent nanoda kernel is NOT run. lean-eval's
# WorkspaceTest harness forces `enable_nanoda := true`; here the comparator is invoked directly on
# `comparator/config.json`, which sets it to false. The k = 3 height-three certificate
# (`Grid3/Three/Cert/Data/`, 43,736 `decide +kernel` records) makes the export close to 1 GB, and
# the comparator replays it sequentially through each kernel; two replays plus the build exceed
# GitHub's six-hour job limit (run 34082945506, 2026-09-07). Lean's own kernel replay is kept.
#
# Tool pins below mirror lean-eval's .github/workflows/ci.yml (as of 2026-08-03). The
# comparator/lean4export repos are tagged per Lean *minor* release, so there is no
# v4.33.0 patch tag either; upstream pins lean4export by SHA and copies the workspace `lean-toolchain`
# over it, which is what makes lean4export able to read this toolchain's `.olean`s.
#
# Script adapted from github.com/rkirov/jacobian-fable (verify.sh), which in turn came from
# github.com/rkirov/jacobian-claude.
set -euo pipefail

# Upstream-pinned tool revisions (lean-eval ci.yml; bump only alongside upstream).
COMPARATOR_REV=71b52ec29e06d4b7d882726553b1ceb99a2499e0
LEAN4EXPORT_REV=15f6055e299ad5b89345e533cc2192f4cc00f659  # = refs/tags/v4.33.0
LANDRUN_REV=5ed4a3db3a4ad930d577215c6b9abaa19df7f99f

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS="$HERE/comparator"
TOOLCHAIN_TAG=$(sed -e 's/^leanprover\/lean4://' "$WS/lean-toolchain" | tr -d '[:space:]')
WORK="${COMPARATOR_WORK:-$HOME/.cache/graph-coloring-comparator/$TOOLCHAIN_TAG}"
mkdir -p "$WORK"

clone_at() { # repo dir rev
  if [ ! -d "$2" ]; then
    git clone "$1" "$2"
    (cd "$2" && git checkout --detach "$3")
  fi
}

clone_at https://github.com/leanprover/comparator "$WORK/comparator" "$COMPARATOR_REV"
clone_at https://github.com/leanprover/lean4export "$WORK/lean4export" "$LEAN4EXPORT_REV"
# lean4export must be built with the toolchain that produced the `.olean`s it reads
# (upstream does exactly this `cp`).
cp "$WS/lean-toolchain" "$WORK/lean4export/lean-toolchain"
# DEVIATION from upstream: upstream builds comparator with comparator's OWN pinned toolchain
# (v4.30.0-rc2 at $COMPARATOR_REV). We build it with the workspace toolchain instead, to avoid
# installing a third full Lean toolchain on a disk-constrained machine. comparator only reads
# the export produced by lean4export and replays it in-process, so its own build toolchain is
# not part of the check. Set COMPARATOR_OWN_TOOLCHAIN=1 to restore upstream's exact recipe.
if [ "${COMPARATOR_OWN_TOOLCHAIN:-0}" != "1" ]; then
  cp "$WS/lean-toolchain" "$WORK/comparator/lean-toolchain"
fi
(cd "$WORK/comparator" && lake build comparator)
(cd "$WORK/lean4export" && lake build lean4export)

# landrun sandbox binary, wrapped to grant the dynamic loader the read+exec paths its
# -ldd resolution can miss.
#
# lean-eval's README is explicit that landrun must come from the PINNED COMMIT, not from a
# tagged release: "tagged releases through v0.1.15 lack fixes comparator needs".
if [ ! -x "$WORK/landrun-bin" ]; then
  if command -v go >/dev/null 2>&1; then
    GOBIN="$WORK/gobin" go install "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_REV"
    cp "$WORK/gobin/landrun" "$WORK/landrun-bin"
  else
    echo "verify.sh: no 'go' toolchain found; falling back to the landrun v0.1.14 release." >&2
    echo "verify.sh: WARNING - upstream considers released landrun binaries insufficient, so" >&2
    echo "verify.sh: this run is NOT equivalent to lean-eval's. Install Go to fix." >&2
    curl -sL -o "$WORK/landrun-bin" \
      https://github.com/Zouuup/landrun/releases/download/v0.1.14/landrun-linux-amd64
  fi
  chmod +x "$WORK/landrun-bin"
fi
EXTRA=""
for d in /lib64 /lib /usr/lib /nix/store; do
  [ -e "$d" ] && EXTRA="$EXTRA --rox $d"
done
printf '#!/usr/bin/env bash\nexec "%s/landrun-bin"%s "$@"\n' "$WORK" "$EXTRA" \
  > "$WORK/landrun"
chmod +x "$WORK/landrun"
export COMPARATOR_LANDRUN="$WORK/landrun"
export PATH="$WORK/lean4export/.lake/build/bin:$WORK:$PATH"
export COMPARATOR_BIN="$WORK/comparator/.lake/build/bin/comparator"

# Reuse the root's package tree rather than materialising a second Mathlib. This has to be a
# symlink and not `packagesDir = "../.lake/packages"` in the workspace lakefile: a registry
# verifier prepares fresh build directories and confines the build's writes to the selected
# project, so a packagesDir pointing above it turns the first dependency fetch into a write
# outside the project. `.lake/` is git-ignored and a submitted snapshot excludes symbolic links,
# so this is local convenience only and never reaches a verifier.
if [ -d "$HERE/.lake/packages" ] && [ ! -e "$WS/.lake/packages" ]; then
  mkdir -p "$WS/.lake"
  ln -s ../../.lake/packages "$WS/.lake/packages"
fi

# Build the workspace (Challenge spec, Submission → library) and invoke the comparator directly
# on the committed config (`enable_nanoda: false`), the way lean-eval's WorkspaceTest would except
# for the nanoda override; `lake env` supplies LEAN_PATH for lean4export.
cd "$WS"
lake build Challenge Submission
exec lake env "$COMPARATOR_BIN" config.json
