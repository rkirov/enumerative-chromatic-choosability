# Grid ECC handoff — 2026-09-06

## Target and honest status

ECC means that every assignment of lists of size `k` has at least as many proper colourings
as the constant `k`-palette. The user wants a finished Lean proof and is especially interested
in full rectangles `P_n □ P_m` for every `k ≥ 5`, or a weaker dimension-independent threshold.
They also asked to reduce the computational cost and preserve notes for another agent.

Neither the full-rectangle theorem nor height-three `k = 3` is finished. Do not cite the
staging theorem `Grid3.Three.ecc_grid3_three` as proved: `k3_entropy/Assembly.lean` still has
one `sorry` in `entropy_half`. `GridGen.GeneralHeightConjecture` is a proposition, not a theorem.
`pathG r` has **r + 1 vertices**.

Already proved: ladders at `k ≥ 3`; height-three grids at `k ≥ 4`; the height-three all-uniform-
column case at `k = 3`. The arbitrary-height reduction in `GridGen/` still has open hypotheses.

## Other agent's progress, already present when this session resumed

Read `k3_entropy/REMAINING.md`'s September 6 progress log. It supersedes its older milestone text.

- `Grid3/Three/Cert/KeysCore.lean`, `Keys.lean`, `Types.lean`, `Keys/K00..K38.lean`, `Keys/All.lean`:
  formal enumeration completeness. `cert_complete` covers 43,737 maximal keys: 43,736 stored
  numerical records and the symbolic uniform-to-uniform case.
- `Complete.lean`: `seamOK_of_key` turns completeness into a real numerical seam package, or
  the statement that both types are uniform. It also returns the strong `(18/17)ρ` collision
  bound for a uniform left column in the numerical branch.
- `KeyExt.lean`: `exists_maximal` extends every valid packed key entrywise to a valid maximal key.
- `Parry.lean`: `parry_seam`, `parry_entropy`; the uniform-to-uniform kernel has conditional
  Shannon entropy **exactly** `log ρ`.

These files and the existing dirty `GridGen/`/`lakefile.toml` changes were preserved. The full
certificate corpus was not regenerated or rebuilt in this session.

## New proved work in this session

Everything below is in the staging directory, outside the default `Grid3` target. No new
`sorry`, `axiom`, or `native_decide` was added.

### Final consumer: `k3_entropy/FinalModel.lean`

`Grid3.Three.colConst_le_col_of_model` concludes the **actual graph count inequality**

    (pathG 2 □ pathG n).colConst 3 ≤ (pathG 2 □ pathG n).col L

from actual-colour laws/kernels on `Fin 3 → Fin C`. Its inputs are:

- nonnegative column laws and kernels, normalized initial law and stochastic kernel rows;
- the marginal step equation only for the used seams `k < n`;
- list membership and adjacent-row inequality on positive column-law states;
- horizontal compatibility on positive transitions;
- local row-entropy bounds `log ρ ≤ Σ_c law k c * rowH (K k) c`;
- either `log 12 ≤ H(law 0)`, or the root bound with deficit `log(18/17)` plus one seam
  contributing that bonus.

It discharges path positivity, support cardinality, positivity of the colouring count,
entropy assembly, graph relabelling, uniform recurrence identification, and the final cast
back to natural-number counts. **Constructing the input laws/kernels is still missing.**

### Entropy: `CertifiedEntropy.lean`

- `row_entropy_of_collision` and `row_entropy_of_fourth`: local, chain-independent entropy bounds.
- `Cert.EntropyCert.row_entropy`, `Cert.SeamOK.row_entropy`, `Cert.SeamOK.row_entropy_bonus`.
  Normalization `Σ lawR = 1` is an explicit input; it is not a field of `SeamOK`.
- `Cert.parry_row_entropy` puts the exact symbolic kernel into the same interface.
- `lastMarg_eq_law_upto` needs no marginal equations outside the finite chain.
- `entropy_from_row_bounds` and `_one_bonus` allow numerical and symbolic seams to mix freely.

Do not force a uniform-to-uniform seam into a strict `EntropyCert`. The old numerical-only
`entropy_half_from_card` wrapper is the wrong interface for mixed chains.

### Transport: `KernelTransport.lean`

Namespace `Grid3.Three.Transport`. Given independent injections `f : A → S`, `g : B → T`:

- `liftLaw` extends a law by zero along `f`;
- `liftKernel` extends target rows by zero along `g`, using an arbitrary stochastic fallback
  outside the source image;
- `liftKernel_nonneg`, `_rowsum`, `_step`, `_support` preserve the required seam properties;
- `entropy_liftLaw`, `liftKernel_entropy`, and the general `liftKernel_statistic` preserve
  entropy and every zero-preserving row statistic exactly.

This is a proved **generic** transport mechanism, not construction of the colour injections.
The maps must be injective on their entire source types. For packed `Fin 32768` states, one
possible route is to decode as three `Fin 32` labels, extend each active column colour map
to all 32 labels using enough unused global colours, and act coordinatewise. Alternatively,
first restrict to a supported state subtype and construct injections from that subtype.
Do not silently apply the theorem to a map injective only on positive states.

The source and destination maps are deliberately independent. A single global colour injection
cannot generally represent the extra identifications used in maximal extension. The remaining
law-invariance proof must show that the transported law depends only on the actual column,
not on which neighbouring seam produced its canonical labels.

### Model and count bridges

- `Grid3Model.lean` now aliases the entropy engine's `PState`, `lastCol`, and `mu`; the previous
  independent recursive definitions were not definitionally interchangeable at abstract width.
- Its `toColouring_mem_properC` now requires inequality only on adjacent rows, not on every
  pair of distinct rows. The old hypothesis incorrectly excluded legal `ABA` states from the
  intended application (the old implication itself was valid but too restrictive).
- `ModelAssembly.lean`: `mu_pos_column_law`, `positive_path_mem`, `support_card_le_properC`.
- `GraphBridge.lean`: `pathEquiv` (nested `Option` path vertices to `Fin`), `gridIso`,
  `col_eq_properC`, `a_eq_uniform_transfer`, `colConst_three_eq_a`.
- `ModelChecks.lean`: explicit `ABA` regression, path-end indexing examples, and axiom audits
  of ten main theorems, including `colConst_le_col_of_model`.

## Next Lean work, in dependency order

1. Connect concrete column types (`TypeClass.lean`, `BlockColour.lean`) to packed `validType`.
   Relate concrete state signatures to `sigOf`/`lawR`, and prove the uniform-type criterion.
2. From actual common colours, construct the effective partial block matching. Matches of
   disjoint row patterns have no horizontal effect and should be dropped. Prove validity of
   its packed matrix, and relate `KeyExt.exists_maximal` to an actual matching extension.
3. Construct within-pattern/joint-pattern permutations identifying an extended matching with
   `colours mL mR M`. Prove that canonical compatibility pulls back to actual compatibility.
   Prove law invariance under these maps. `KernelTransport` then handles the analytic transport.
4. Prove normalization and root collision bounds for the actual laws. The reflected record specs
   already contain nonuniform `sumC = 108`, `sumC2 ≤ 972`; turn these into real-law statements.
   The uniform bound is `Σ law² = 3/34`. Handle the zero-seam nonuniform column without assuming
   that an incident numerical record exists.
5. Use `Complete.seamOK_of_key`/`Parry.parry_seam`, then `CertifiedEntropy`, then the new
   `colConst_le_col_of_model`. Choose the first uniform-to-nonuniform seam for the bonus case.
6. Replace the single `Assembly.entropy_half` sorry, audit its transitive axioms, then promote
   the completed modules into `Grid3/` and its build. Do not promote a conditional theorem as ECC.

## Reproduction and resource caution

From the repository root:

    bash k3_entropy/check_model.sh

This builds `Grid3.Three.Cert.Parry` and `Grid3.Main`, then compiles the eight model modules in
dependency order into a fresh `/tmp/grid-ecc-model.*` directory, and runs the regression/axiom
checks. It does not import/recheck the 4,374 certificate-data modules. An optional output directory
can be supplied. Earlier individual development builds are under `/tmp/grid_ecc_review_build`.
The new main theorems' axiom audits report only `[propext, Classical.choice, Quot.sound]`.

Disk space was about 1.6 GB free at the end of development. Avoid rebuilding or copying the full
certificate corpus casually. No existing files were deleted, no git commits or staging were done.
The workspace sandbox helper fails with a `bwrap` loopback error; terminal checks worked with
the approval-reviewed `require_escalated` mode. `apply_patch` can add files but its update/read
path failed; edits used an exact read and a full-content `apply_patch` replacement.

## Earlier computational-cost work, still available

Detailed derivations, scripts, and measurements: `ai_research_notes/GRID_REVIEW_2026-09-05.md`.
That directory is partly gitignored: do not assume new scripts there will be committed by default.

- `RowCollision.lean`: apply collision entropy rowwise before averaging. For rational source
  law `c/D`, certify `ρ^D ∏_s (Σ_t K_st²)^c_s ≤ 1` exactly. It removes 46/50 old fourth-root
  fallbacks unchanged; exact reoptimization repaired two more. Two tested seams remain negative,
  which is not a proof of infeasibility. Not integrated into the frozen packed checker.
- Reversal audit: 22,000 existing couplings can potentially cover the 43,736 numerical keys,
  using a checked reverse inequality where needed. This is a witness-count reduction, not a
  demonstrated 49.7% runtime reduction. The Lean compression is not implemented.
- `seam_key_audit.py`: independent residual-capacity DP reproduced all 43,737 maximal keys in
  about 5.3 seconds; the other agent subsequently completed formal enumeration.
- `capped_seam_dp.py`: exact actual-Lean-cap horizon-zero test via palette-image inclusion–
  exclusion and row transfer. Cost `O(m 3^Q Q k)` integer operations for palette union size `Q`,
  not exponential in height at bounded `Q`. Tests through height 160 are nonnegative; no theorem.

## Full rectangles: still separate mathematics

`GridGen.Main` and `GridGen.Explicit` reduce ECC to initial and two-step inequalities at
**every horizon**. Only the height-three instance is supplied. Existing C tests use first-
occurrence colour ranks; Lean's `patCap` uses numerical ranks. Above `k` distinct colours
these differ. At `k=5`, `(4,3,2,1,0,5)` gives caps `(0,1,2,3,4,4)` versus `(4,3,2,1,0,4)` and
one-future counts 1320 versus 1423. This is a diagnostic mismatch, not an ECC counterexample.

The existing `ListColoring/Threshold.lean` theorem `ecc_of_two_pow_lt` gives a threshold
depending on edge count, not a constant for all rectangles. Do not use `OpenProblems.lean`
or the false general 2-degenerate conjecture to fill the gap.

### Unverified optional research lead: bounded-degree polymer interpolation

This was sketched in the preceding conversation, **not proved, not formalized, not novelty-
checked**, and should receive an adversarial mathematical audit before any theorem is claimed.

For connected vertex sets `S`, let `c(S)` be the alternating sum of connected spanning edge
sets of `G[S]`, and `d(S) = k - |intersection of the lists on S|`. Interpolate the Whitney
partition expansion with block weights `c(S) (k - t d(S))`, calling the result `Z_t(U)`.
At `t=0` this is the uniform count and at `t=1` the list count. Singletons have weight `k`.

If one can prove `Σ_{S∋v, |S|=r+1} |c(S)| ≤ B^r`, a proposed argument for
`k ≥ 2B²+2B`, `B ≥ 2`, sets `q=k/2` and inductively bounds vertex-removal ratios below by `q`.
The root recurrence's correction is bounded by `k B/(q-B) ≤ k/2`. In the derivative, edges
contribute positively; use `d(S) ≤ Σ_{e∈E(G[S])} d(e)` to charge all larger-block terms to edges.
The tail per edge is bounded by `B²/(q-B) ≤ 1`, suggesting `Z'_t(U) ≥ 0`.

The tree-graph inequality `|c(S)| ≤ number of spanning trees of G[S]` and a rooted-plane-tree
count suggest `B=4Δ`, hence the candidate threshold `32Δ²+8Δ` (544 for grids). All identities,
ratio induction, coefficient counting, and interpolation endpoints still need verification.
This is a possible route to a weaker dimension-independent theorem, **not a proved k≥544 result**.

## Coordination note (2026-09-06, evening session, second agent)

I am taking items 1–6 of "Next Lean work" (canonicalization and the assembly into
`colConst_le_col_of_model`), in new modules under `Grid3/Three/`: `Sig.lean` (law by signature,
sums over `stsOf`, nonuniform root facts), `Column.lean` (concrete columns, packed types, concrete
states and laws), `Glue.lean` (class-wise bijections), `Seam.lean` (keys, colour maps, transport
along `KernelTransport.liftKernel`), `Chain.lean` (assembly). I will not edit `k3_entropy/*` except
`REMAINING.md`/`README.md`; please avoid starting the same items in parallel.

## Completion (2026-09-06, late, second agent)

Items 1–6 of "Next Lean work" are done. `Grid3/Three/Main.lean` proves
`Grid3.Three.ecc_grid3_three : ∀ n, (pathG 2 □ pathG n).ECCAt 3` (and
`ecc_boxProd_pathG_two_of_three` for all `k ≥ 3`), axioms `[propext, Classical.choice, Quot.sound]`,
consuming `colConst_le_col_of_model` and `KernelTransport` through a new non-default Lake library
`k3_entropy`. `k3_entropy/Assembly.lean` is deleted. Module list and build instructions:
`k3_entropy/REMAINING.md`, progress log entry "2026-09-06 (late)".
