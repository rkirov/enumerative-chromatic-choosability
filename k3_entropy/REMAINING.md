# Closing `P₃ □ Pₙ` at list size three: exact remaining work

## Status

**The theorem is proved (2026-09-06): `Grid3.Three.ecc_grid3_three` in `Grid3/Three/Main.lean`.**
The analytic entropy half is proven and compiles without `sorry`.  On 2026-08-28 the independent
Python checker again verified all 43,737 maximal seam orbits and reproduced the recorded digest

    cd0d9a51369ed2e085274d08b97cbc84103309195f2e4b6401638de061cea147.

The previous `DEAD_END.md` retraction was based on applying the nonuniform-case bound to the
constant assignment and is incorrect.  The corrected capstones now present in
`Grid3Entropy.lean` are:

- `entropy_half_from_card`: a nonuniform root and basic `ρ` certificate on every seam;
- `entropy_half_from_card_one_bonus`: a uniform Parry root and one strong `(18/17)ρ` seam;
- `H_ge_log34_div3`: the exact endpoint collision budget.

This does **not** yet make a finished Lean theorem. The finite certificate, enumeration, and
analytic/model/count assembly are now proved (see the September 6 progress entries below).
Transport from arbitrary actual lists to the canonical seam keys, law invariance, and construction
of the actual-colour model remain. The all-uniform branch is done (`Grid3/AllU.lean`, in the
`Grid3` build). `HANDOFF_GRID_ECC.md` is the current cross-agent entry point.

## The corrected proof split

For a three-list assignment, encode each column by the multiplicities of the seven nonempty row
support patterns.  There are 39 types; `U` is the unique type with three blocks of pattern `111`.

1. **First column nonuniform.**  Its law has collision at most `1/12`; apply
   `entropy_half_from_card`.
2. **First column uniform, some later column nonuniform.**  Let `j+1` be the first nonuniform
   column.  The Parry root has collision `3/34`; the certificate for seam `j` has the strong
   factor `(18/17)ρ`.  Apply `entropy_half_from_card_one_bonus`.  The equality
   `(34/3)(18/17)=12` is exactly the endpoint bookkeeping.
3. **Every column has type `U`.**  Write its common three-colour palette as `A_j`.  Complete the
   partial identity on `A_j ∩ A_{j+1}` to a bijection `e_j : A_j ≃ A_{j+1}`.  Starting from an
   arbitrary `Fin 3 ≃ A_0`, recursively gauge by `e_j`.  Coordinatewise relabelling injects every
   constant-palette grid colouring into an `L`-colouring, so the listed count is at least the exact
   uniform count.

No global colour-component saturation is required.  For each actual seam independently, extend
its partial block matching to a maximal matching.  Added matches create extra prohibitions, hence
the maximal compatibility support is a subset of the actual support.  A certified coupling on the
maximal support is therefore valid for the original seam.  The fixed type laws make independently
chosen seam couplings concatenate.

## Progress log

- **2026-09-02, certificate built.** `Grid3/Three/Cert/Checker.lean` (frozen) is the kernel checker;
  `Grid3/Three/Cert/Data/C0000..C4373.lean` hold all 43,736 seam records (10 per module, 100 MB of
  source, 703 MB of oleans), every record a `decide +kernel` theorem depending only on `propext`.
  Build cost: 6–12 s per module, four sequential builders, about three hours; memory grows by
  ~36 MB per record inside one process, hence the 10-record modules. Formats: 42,951 rational
  collision, 735 `ℚ(√17)` collision, 41 rational fourth-root, 9 `ℚ(√17)` fourth-root.
- Reflection (`Grid3/Three/Cert/Digits.lean`, `Decode.lean`, Mathlib-free): `checkRecord_zero_spec`
  and `checkRecord_one_spec` turn a passing rational / `ℚ(√17)` collision record into exact
  integer facts (validity, nodup entries, support, row/column marginals against the signature
  laws, non-uniform column sums, the collision inequality as a `negQ17` sign test); all four
  formats have their spec theorems (`_two_spec`, `_three_spec` for the fourth-root records).
- Real-number bridge (`Grid3/Three/Cert/Bridge.lean`, Mathlib): `bridge_zero` and `bridge_one`
  turn a passing collision record into `SeamOK mL pL mR pR K` at packed states `Fin 32768`:
  the real law `lawR m pats` (signature formula, Parry on `U`), a kernel `K` (nonnegative rows
  summing to one), `∑_c lawR_L c · K c s = lawR_R s`, support inside `compat` and the state lists,
  and `(∑ law·K²)·ρ < 1` (plus the `(18/17)ρ` bound when the left column is uniform). Axioms:
  `[propext, Classical.choice, Quot.sound]`. `bridge_two`/`bridge_three` cover the fourth-root
  records (formats 2/3) with an `r`-witness package; `SeamOK.entropy` is the disjunction
  `EntropyCert` (collision bound, or witnesses with `law·K ≤ r⁴·law` and `(Σ law·K·r)⁴·ρ < 1`).
  So every one of the 43,736 records yields a seam package. Branch `k3-three`.

- **2026-09-06, enumeration completeness, key-level maximal extension, and the `U → U` seam.**
  `Grid3/Three/Cert/KeysCore.lean` (Mathlib-free) defines `validKey`/`keyMax` on packed keys and an
  enumerator `enumKeys mL mR` (rows from a literal table `rowVecsLit`, residual capacities as one
  base-8 packed `Nat` with a guard bit, so that "fits" is `((res + G8) - r8) &&& G8 = G8` and
  maximality a final `res &&& dead = 0`; about 9 s / 0.9 GB of kernel time for the worst pair,
  1365 → 1365). `Keys.lean` proves `enumKeys_complete` (structural: every valid maximal `M < 16384^7`
  is listed), with the table identified with the structural generator `comps` by `decide +kernel`
  and the two bitwise tests reduced to `Nat.testBit`. `Types.lean` fixes the 39 valid types
  (`validTypes_eq`). `Keys/K00..K38.lean` (generated by `ai_research_notes/cx/k3rev/gen_keys.py`,
  5.4 MB of source, 39 modules of 15–145 s each, ≤ 2.5 GB, ~125 MB of oleans) state
  `enumKeys mL mR = [stored keys]` for all 1,521 pairs by `decide +kernel` and tie every stored key to
  its `cNNNN_okK` record theorem; `Keys/All.lean` assembles `cert_complete`: every valid maximal key is
  the symbolic `U → U` key or has `∃ fmt ne blob, fmt < 4 ∧ checkRecord fmt mL mR M ne blob = true`
  (imports all 4,374 data modules; builds in 35 s at 1.2 GB). `Complete.lean` turns that into
  `seamOK_of_key`: `(mL = UTYPE ∧ mR = UTYPE) ∨ ∃ K, SeamOK … K ∧ (mL uniform → (18/17)ρ bound)`.
  Independent audit: `seam_key_audit.py` (residual-capacity DP) agrees, 43,737 keys.
  `KeyExt.lean` (Mathlib-free): `exists_maximal` — every valid key lies entrywise below a valid
  maximal key (greedy, one base-4 digit at a time). `Parry.lean`: the `U → U` seam package
  `parry_seam` — the Parry kernel `KU c s = v(s)/(ρ v(c))` on the twelve uniform states with
  `v = (1, (√17-1)/4)` is stochastic, stationary for `lawR UTYPE [7,7,7] = (17 ± √17)/204`, supported
  in `compat`, and its conditional entropy is exactly `log rhoR` (`parry_entropy`); this seam cannot
  carry a strict `EntropyCert`, so the assembly must feed `log ρ ≤ Σ law · rowH` to
  `entropy_bound_conditional` directly. Build: `lake build Grid3.Three.Cert.Keys.All` needs the
  `Data/` oleans; `ai_research_notes/cx/k3rev/build_keys.sh 0 2` / `1 2` build the 39 key modules
  with RAM and disk guards. All new theorems: axioms `[propext, Classical.choice, Quot.sound]`
  (the kernel-checked ones `[propext]`).

- **2026-09-06, continued: mixed-seam entropy, generic transport, and final model/count assembly.**
  `k3_entropy/CertifiedEntropy.lean` converts `EntropyCert` (either numerical format) and the
  exact Parry seam to local row-entropy bounds, including the strong-seam bonus.
  `entropy_from_row_bounds` / `_one_bonus` concatenate arbitrary mixtures, with marginal
  equations needed only on used seams. `KernelTransport.lean` transports laws and kernels
  along independent left/right injections, preserving normalization, marginals, support,
  entropy, and zero-preserving row statistics exactly. The colour injections themselves
  and law invariance under their choice remain to be constructed.
  `Grid3Model.lean` now shares the entropy engine's `PState`/`mu`/`lastCol`; its vertical
  support hypothesis was weakened to adjacent rows so legal `ABA` states are admitted.
  `ModelAssembly.lean` proves `support_card_le_properC` from local support.
  `GraphBridge.lean` proves `gridIso`, `col_eq_properC`, and `colConst_three_eq_a`.
  Finally, `FinalModel.lean`'s `colConst_le_col_of_model` concludes the actual `pathG`
  count inequality from colour-level laws/kernels, handling either a nonuniform root or
  a root deficit paid by one strong seam. This is conditional on the model data, **not**
  an unconditional ECC theorem; `Assembly.entropy_half` still has its original sorry.
  Build/regression/axiom audit: `bash k3_entropy/check_model.sh` (does not rebuild all
  certificate data). The ten audited consumer/transport theorems have only
  `[propext, Classical.choice, Quot.sound]`. See root `HANDOFF_GRID_ECC.md`.

- **2026-09-06 (late), THEOREM DONE.** `Grid3/Three/Main.lean` proves
  `Grid3.Three.ecc_grid3_three : ∀ n, (pathG 2 □ pathG n).ECCAt 3` and the corollary
  `ecc_boxProd_pathG_two_of_three : 3 ≤ k → (pathG 2 □ pathG n).ECCAt k`, axioms
  `[propext, Classical.choice, Quot.sound]`, no `sorry` under `Grid3/`. The chain of modules:
  `Sig.lean` (law by signature, sums over `stsOf`, root facts from `Σ count = 108`, `≤ 972`),
  `Column.lean` (concrete columns, `packType`, `validType_packType`, concrete states `IsCol`,
  `sigC`, `lawC`), `Glue.lean` (class-wise bijections), `Seam.lean` (`commonI`, `Mact`,
  `validKey_Mact`, `exists_Mmax`), `Slots.lean` (counts of the canonical colour list),
  `ColourMaps.lean` (`exists_colourMaps`: pattern-preserving colour injections agreeing on the
  intersecting common colours, with inverses on active slots), `Transport.lean` (state maps
  `fL`/`fR : Fin SB → (Fin 3 → Fin C)`, `liftLaw_fL : liftLaw fL (lawR mL pL) = lawC Lc`,
  `compat_fL_fR`), `Package.lean` (`seam_package` = `seamOK_of_key` plus `cols.length ≤ 32` and the
  nonuniform root facts), `UCol.lean` (uniform columns: `packType_U`, `lawC_U_facts` via the
  column's seam with itself and `MUU`), `SeamData.lean` (`seam_exists`: one kernel per seam with
  step, support, `log ρ` bound, bonus, root facts; Parry kernel on the `U → U` seam),
  `Main.lean` (the chain, `colConst_le_col_of_model` from `k3_entropy/FinalModel.lean`, the first
  nonuniform column for the bonus, `n = 0` via `ecc_pathG` and `ecc_iso`). The other session's
  `k3_entropy/{CertifiedEntropy,KernelTransport,ModelAssembly,GraphBridge,FinalModel}.lean` are
  consumed through the new non-default Lake library `k3_entropy` (`lakefile.toml`).
  `k3_entropy/Assembly.lean` (the old `sorry`) is deleted. Build: `lake build Grid3.Three.Main`
  (needs the `Grid3/Three/Cert/Data/` oleans and the `Keys/` modules; ~1 min once those exist).

## What is left, precisely (2026-09-06)

Nothing. All items below are done (2026-09-06); the sections that follow are kept as the
record of the route. Remaining housekeeping is storage: the 100 MB `Grid3/Three/Cert/Data/` tree
and the generated `Keys/K*.lean` are uncommitted, and `Grid3.lean` deliberately does not import
`Grid3.Three.Main` so that CI does not need the certificate data.

## Formal milestones

### 1. Column types and the uniform type

Build on `TypeClass.lean` and `BlockColour.lean`:

- define the finite subtype of `m : Fin 7 → Fin 4` satisfying the three row sums;
- give a checked 39-entry enumeration and a lookup theorem;
- define `U` and prove `colType L = U ↔ L 0 = L 1 ∧ L 1 = L 2` for three-element row lists;
- package canonical blocks, proper block states, and the pattern-preserving block/colour
  equivalence already proved in `BlockColour.lean`.

### 2. Seam matching and local maximalization

Represent an orbit by its `7 × 7` matrix of match counts.  Prove:

- an actual common colour induces an injective partial block matching and a valid count matrix;
- every valid matrix extends to a maximal one (finite maximal-cardinality choice suffices);
- canonical block matchings with the same matrix are related by within-pattern permutations;
- compatibility is antitone under extension: `q ≤ q' → Me q' ⊆ Me q`.

This replaces the former global `Saturated` construction and avoids proving that repeated colour
identifications commute across the whole strip.

### 3. The all-`U` injection — DONE (2026-08-28)

Completed in `Grid3/AllU.lean` (part of the real `Grid3` build, sorry-free, native_decide-free,
axioms `[propext, Classical.choice, Quot.sound]`):

- `Grid3.AllU.gauge` extends the identity on `C ∩ B` to a bijection `C → B` (via `gEquiv` on the
  symmetric differences); `gauge_mem`, `gauge_fix`, `gauge_notmem`, `gauge_inj` are its facts.
- `Grid3.AllU.exists_gauge` builds the compatible per-column gauge family along `pathG n` by
  induction on `n` (each seam only constrains its own adjacent palettes — no global saturation).
- `Grid3.AllU.col_ge_of_gauge` turns a gauge family into the count inequality via coordinatewise
  relabelling and `Finset.card_le_card_of_injOn`.
- `Grid3.AllU.colConst_le_col_of_allU (n) (L) (h3 : IsNListAssignment L 3)
  (hU : ∀ r c, L (r, c) = L (rowT, c)) : colConst 3 ≤ col L` is milestone 3.

### 4. Certificate format (revised 2026-09-02; see `ai_research_notes/GRID_REVIEW_2026-09-02.md` §2)

The final record must include a key `(leftType, rightType, matchMatrix)` and must check key
validity and maximality, both coupling marginals, zero entries outside `Me` and nonnegativity,
and one seam inequality. Two formats, chosen per seam:

- **collision** (the default, ≈ 43,690 seams): `ρ · Σ_{s,t} X(s,t)²/α_A(s) < 1`, using
  `seam_collision_bound` / `seamterm_ge_logrho_collision` in `Grid3Entropy.lean`; no per-entry
  witnesses. On `U → X` seams also the strong form `(18/17)ρ · Σ X²/α < 1` — these 372 seams are
  the only place the formalized split (case B) needs the strong bound, and all of them pass it.
- **fourth-root** (the ≤ 130 seams whose max-entropy coupling fails the collision bound and the
  ≈ 45 that still fail after re-optimizing the coupling for the quadratic objective): the
  per-entry witness `r_st` with `r⁴ ≥ X/α` and `(Σ X r)⁴ ρ < 1`, as in `SeamBridge.lean`.

Seams incident with `U` (745 of them) have laws and flows in `Q(√17)` (rational base denominator
`108000`, quadratic coefficient denominator `204000`); their inequality is a sign test on
`a + b√17`, decided by squaring. The unique `U → U` seam is symbolic (Perron vector).

Flip-symmetrize the laws first (6 of the 12 flipped type pairs currently carry non-mirror laws),
regenerate the seams of those 12 types, and store one representative per flip orbit: this halves
the certificate. Generate the data from
`ai_research_notes/grid_3xn_dinitz_parry_exact_certificate.py` (`exact_flow`, 27 min for all
seams) plus `cx/k3rev/qp_fix.py` for the re-optimized ones.

### 5. Kernel-checked finite verification (revised 2026-09-02)

The final theorem lives under `Grid3/`, where CI rejects `native_decide`. The tool is
`decide +kernel`, which adds no axiom, on **packed big-`Nat` literals**: one `Nat` per seam
(entries `(s, t, v)` packed in fixed-width decimal fields, laws packed base `1000`), decoded in
the kernel by `%` and `/` (GMP-accelerated), checked by one structural pass that accumulates the
row and column marginals as packed sums `Σ v·B^s`, `Σ v·B^t` and the quadratic sum
`Σ v²·(L/cA[s])` (`L` = lcm of the law counts). Measured: 0.08 s per seam (collision), 0.16 s
(fourth-root), no Mathlib import needed for the checker modules. Whole certificate: ~1 CPU-h,
~30 CPU-min after flip symmetry, in ~50 modules with one `decide +kernel` theorem each.

Do not use the elaborator's `decide` (times out at whnf), `norm_num` per inequality (7M facts),
or `native_decide`. Each chunk exposes an existential `SeamGood key`; downstream code recovers the
witness with `Classical.choose`, so the literals never enter the Markov model.

The checker's own proof obligation (verified reflection) is one lemma: packed equality with all
block sums below the base `B` implies per-index equality; the rest is the arithmetic already in
`SeamBridge.lean`, plus the collision analogue.

### 6. Orbit transport and Markov model

For each concrete column, transport the certified type law through a pattern-preserving
block/colour equivalence and pad it to one fixed finite state type (for example functions
`Fin 3 → {c // c ∈ globalColors L}`).  For each seam:

- transport the representative coupling through the within-pattern permutations;
- then transport through the two block/colour equivalences;
- fill zero-law rows with an arbitrary normalized kernel;
- prove both marginals, support in concrete horizontal compatibility, and the basic/strong
  `hentry` and `hRp` facts.

The already-proved `mu_pos_trace`, `toColouring_mem_properC`, `toColouring_injective`, and
`hcard_from_inj` then give the support-cardinality bound.

### 7. Graph-level assembly

Relate `Grid3.Three.a n` to `Grid3.colConst_eq` at `k=3`, split on the three cases above, cast the
real inequality back to naturals, and expose

    theorem ecc_grid3_three (n : ℕ) :
      (ListColoring.pathG 2 □ ListColoring.pathG n).ECCAt 3

from `Grid3/Statements.lean`.

## What not to pursue

- Do not replace the entropy proof by the exact eigenfunctional `C1` telescoping in
  `Telescope.lean`; actual `k=3` chains violate its termwise inequality.
- Do not attempt to instantiate `entropy_half_from_card` for the constant assignment; that is the
  precise mistake behind the old retraction.
- Do not claim the 300-seam string pilot or the rational-only bridge proves enumeration
  completeness.
