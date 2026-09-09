# Height-three grids at list size three

`Grid3.Three.ecc_grid3_three : ∀ n, (pathG 2 □ pathG n).ECCAt 3`, in `Main.lean`, together with
`ListColoring.ecc_boxProd_pathG_two_of_three` for every `k ≥ 3`. Axioms
`[propext, Classical.choice, Quot.sound]`; every proof is complete and kernel-checked (CI greps the
directory for placeholders).

`Grid3.lean` does **not** import `Main.lean`: the proof rests on 22,157 kernel-checked seam
records (`Cert/Data/`, 46 MB of source, about four CPU-hours of `decide +kernel`), which the
default build and CI do not rebuild. The comparator submission (`comparator/Submission.lean`)
imports it directly.

## The argument

Split on the columns of the `3 × (n+1)` grid. If every column is *uniform* (its three lists
agree), `Grid3/AllU.lean` injects the constant-list colourings into the list colourings by a
gauge relabelling. If `n = 0` the grid is the path `P₃`, which is ECC. Otherwise the count of
list colourings is bounded below by entropy:

* Each column has one of 39 *types* (the multiplicities of the seven row-support patterns among
  its colours) and a *signature law* on its proper colourings, depending only on the type and on
  the patterns of the three colours used (`Column.lean`, `Sig.lean`).
* Each seam (two adjacent columns) has a *key* `(mL, mR, M)`: the two types and the matrix of
  common colours by pattern pair (`Seam.lean`); extending the matching to a maximal one
  (`Cert/KeyExt.lean`) only adds prohibitions, and every valid maximal key has a certified
  coupling (`Cert/Keys/`, `Cert/Complete.lean`) whose conditional entropy is at least `log ρ`,
  `ρ = (5 + √17)/2` the Perron root of the transfer matrix, or the `(18/17)ρ` bonus when the left
  column is uniform. The uniform-to-uniform seam is the Parry kernel, with entropy exactly `log ρ`
  (`Cert/Parry.lean`).
* The concrete seam is canonicalized onto its record: pattern-preserving colour injections into
  the canonical slots, agreeing on the common colours (`Glue.lean`, `Slots.lean`,
  `ColourMaps.lean`), then state maps along which the canonical law and coupling transport exactly
  and canonical compatibility implies actual compatibility (`Transport.lean`,
  `KernelTransport.lean`, `Package.lean`, `UCol.lean`, `SeamData.lean`).
* Only one key per *row-reflection orbit* has a record. Swapping rows `0` and `2` reverses every
  pattern, permutes the digits of a packed type and the cells of a packed key
  (`Cert/Mirror.lean`: `rtype`, `rM`, `rsig`), and the law table is reflection-equivariant (a
  kernel check, `table_rsig`), so the concrete law is invariant, `lawC (mirror Lc) (rs c) =
  lawC Lc c`. When only the reflected key has a record, the seam is built between the reflected
  columns and carried back along the state bijection (`Reflect.lean`, `seam_transport`).
* The Markov chain with these laws and kernels has entropy at least `log 12 + n·log ρ` (a
  nonuniform first column has collision mass at most `1/12`; a uniform one has `3/34`, and the
  first seam into a nonuniform column repays the deficit), and at most the log of the number of
  list colourings (`Entropy.lean`, `Model.lean`, `CertifiedEntropy.lean`, `ModelAssembly.lean`,
  `GraphBridge.lean`, `FinalModel.lean`, `Main.lean`).

The route is the Parry–Rényi entropy certificate of
`ai_research_notes/GRID_HEIGHT3_COMPLETE_2026-08-16.md` (not part of the repository); the
uniform count is `12, 54, 246, …` (`Grid3/Transfer.lean`), and `12 ρⁿ` dominates it.

## The certificate (`Cert/`)

`Checker.lean` is the kernel checker: a record `(fmt, mL, mR, M, ne, blob)` packs one coupling
into a big `Nat` literal (`ℚ(√17)` entries, four formats: collision or fourth-root bound, rational
or with `√17`), and `checkRecord` recomputes the canonical columns from the key and checks support,
marginals, nonnegativity and the seam inequality with integer arithmetic. `Data/C0000..C0553.lean`
hold the records, forty per module, each a `decide +kernel` theorem; the key of a stored record is
the smaller member of its reflection orbit, `(mL, mR, M) ≤ (rtype mL, rtype mR, rM M)`, and 578
orbits are singletons. `Digits.lean` and `Decode.lean` reflect a passing check into integer facts;
`Bridge.lean` turns those into the real-number seam package `SeamOK`. `KeysCore.lean`, `Keys.lean`,
`Types.lean`, `Keys/K00..K38.lean`, `Keys/All.lean` prove enumeration completeness: an enumerator
of the valid maximal keys is complete (`enumKeys_complete`), and for each of the 1,521 type pairs
it equals the list of the keys by `decide +kernel`, each tied to its own record or, by a
`decide` of `rM`, to the record of its reflection, so `cert_complete` covers every key up to
reflection.

The column laws (`LAWTABLE` in `Checker.lean`) were made reflection-symmetric before the records
were generated: nine of the 39 laws differed from their mirror image by one count on a few states,
a rounding artefact, and were replaced by the per-orbit average with the totals kept at `108`; the
whole record set was regenerated against the symmetric laws. Nothing depends on how the table was
produced: the checker verifies every record against it, and `table_rsig` verifies its symmetry.

## Building and regenerating

```sh
lake build Grid3.Three.Cert.Data.C0000      # one record module (~30 s, ~1.9 GB)
Grid3/Three/Cert/scripts/build_keys.sh 0 2   # the key modules, two builders, ~25 min
Grid3/Three/Cert/scripts/build_keys.sh 1 2
lake build Grid3.Three.Main                  # everything else, ~15 min from scratch
```

Build the record modules a few at a time (each takes ~1.9 GB; three in parallel is the limit on an
8 GB machine, about two and a half hours for all 554). `scripts/gen_data.py` writes `Data/` from
the generator's record files, keeping one record per reflection orbit; `scripts/gen_keys.py`
regenerates `Types.lean`, `Keys/K*.lean` and `Keys/All.lean` from `Data/` (its Python replica of
the enumerator, `scripts/enum_replica.py`, is checked against the stored keys first, and
`scripts/mirror.py` is the Python `rtype`/`rM`). The record data itself was generated by the
exact-flow computation of the research notes
(`ai_research_notes/grid_3xn_dinitz_parry_exact_certificate.py` and `cx/k3rev/gen_cert.py` with
the symmetrized laws of `cx/k3rev/symmetrize.py`, not part of the repository) and is verified, not
trusted: the checker recomputes everything it uses.
