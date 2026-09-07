# k=3 grid ECC — the entropy route (staging area, outside the `Grid3` build)

Everything here is either sorry-free and axiom-clean or explicitly marked as a staging `sorry`.
`Grid3/AllU.lean` (the all-uniform case, milestone 3) already lives in the real `Grid3` build.

| file | status | content |
|---|---|---|
| `Grid3Entropy.lean` | sorry-free, `[propext, Classical.choice, Quot.sound]` | the entire §4–5 analytic half: Jensen, `seam_bound` (Rényi-5/4) **and** `seam_collision_bound` (Rényi-2), chain rule, marginal consistency, capstones `entropy_half_from_card` / `_one_bonus` |
| `SeamBridge.lean` | sorry-free | integer certificate data (fourth-root format) ⇒ the per-seam hypotheses of the capstone |
| `TypeClass.lean`, `BlockColour.lean`, `FiberCard.lean`, `BlockCount.lean` | sorry-free | column → type classification, block ↔ colour bijection, state → colouring map |
| `Grid3Model.lean` | sorry-free | path → colouring injection (`hcard`) |
| `CertifiedEntropy.lean` | sorry-free | mixed numerical/symbolic local entropy bounds and finite-chain assembly |
| `KernelTransport.lean` | sorry-free | exact law/kernel/entropy transport along independent injections |
| `ModelAssembly.lean`, `GraphBridge.lean` | sorry-free | local support → colouring count; indexed grid isomorphism; uniform recurrence bridge |
| `FinalModel.lean` | sorry-free | actual `colConst ≤ col` from actual-colour model data; the data is constructed in `Grid3/Three/{Column,Seam,ColourMaps,Transport,SeamData,Main}.lean`, which prove `Grid3.Three.ecc_grid3_three` |
| `ModelChecks.lean`, `check_model.sh` | regression/axiom checks | `ABA` regression, path indexing, ten transitive axiom audits |
| `Assembly.lean` | **one `sorry`** (`entropy_half`) | the three-case split; Case C wired to `Grid3.AllU` |
| `archive/` | superseded | `native_decide` pilots (`PilotCert`, `StringCert`, `AugCert`), `Telescope.lean` (the eigenfunctional route, not for k=3), `blob300.txt` (300 real seams — still the test data for checker timings), `gen_full_blob.py` |

Compile the complete proved model/transport layer: `bash k3_entropy/check_model.sh`.
This uses a fresh temporary build directory and does not recheck the full certificate corpus.
For current proof gaps and the next agent's entry points, read [`../HANDOFF_GRID_ECC.md`](../HANDOFF_GRID_ECC.md).

Compile the independent entropy engine alone: `lake env lean k3_entropy/Grid3Entropy.lean`.

The exact Python checker `ai_research_notes/grid_3xn_dinitz_parry_exact_certificate.py` was rerun
on 2026-08-28 (all 43,737 orbits, digest `cd0d9a51…cea147`); an independent verifier reproduced
every number. The work-list, with the 2026-09-02 cost measurements and the collision
simplification, is `REMAINING.md`. The review that produced them is
`ai_research_notes/GRID_REVIEW_2026-09-02.md`.

Two things that were once claimed here and are wrong: "the entropy route overshoots the uniform
count" (it applied the nonuniform-root bound to the constant assignment; Case C handles that
assignment by a direct injection), and "kernel `decide` cannot check a seam" (the elaborator's
`decide` cannot; `decide +kernel` on packed big-`Nat` literals checks a seam in under 0.2 s).
