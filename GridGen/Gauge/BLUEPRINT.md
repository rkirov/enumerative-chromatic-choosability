# Gauge route: every grid is k-ECC for k ≥ 10 (Lean blueprint)

The mathematics is in `ai_research_notes/GRID_ALL_HEIGHTS_GAUGE_2026-10-15.md`. That note proves
k ≥ 9 with sharper constants. This first formalization proves **k ≥ 10**, with bounds chosen to be
easy to state:

- **Box bound.** γ_k = (k−4)²(k−5)²/(k²(k−3)⁴). Every pair (a,b) is bounded by the worst
  case, and each of the four "neighbour factors" by its own ratio.
- **Path bound.** ε_k = Σ_{L=2}^{7} 2c_L/((k−3)^{L+1}(k−4)) + Σ_{L≥8} 2(L−1)3^{L−1}/((k−3)^{L+1}(k−4)).
  The exact counts c_L = 1, 2, 4, 10, 31, 76 are non-backtracking crossing shapes, checked by
  `decide`.
- **Seam condition.** γ_k ≥ 2ε_k, which gives (1−ε)² ≥ 1−γ. At k = 10 the margin is 16%.

## Modules (all under `GridGen/Gauge/`)

1. `CSP.lean` — generic finite constraint systems: a vertex type, domains, an adjacency and
   conflict relations. It provides Ω and fibres over the complement of a set U (`cls`), with:
   - the fibre-sum lemmas;
   - the chain lower bound #cls ≥ Π(|D c_i| − #non-later neighbours);
   - the chain upper bound (prescribed values give ≤ 1 per fibre);
   - their combination: #{chain prescribed} · Π ≤ #Ω.
2. `Slab.lean` — the slab Fin (i+3) × Fin m. Column 0 is the past column (lists P), column 1 is
   the seam column (k-lists A), and columns ≥ 2 are the future (labels < k). Seam keys
   M : Fin m → ℕ → ℕ, where a key ≥ k means unpaired. Contents: Valid ↔ explicit conditions,
   and #Ω(M) = Σ_{p,s} F(i+1)(M∘s) (`Z`).
3. `Star.lean` — the star identity Ω(M) ⊆ Ω(M⁺) with complement {f(1,v)=c ∧ f(2,v)=x}, and the
   box bound #Ω(M⁺)·Λ ≤ Λ·#hit… precisely, k²(k−3)⁴·#hit ≥ (k−4)²(k−5)²·#Ω(M⁺).
4. `Kempe.lean` — the lower-part transposition move, the swap map on {x,y}-components of the
   future, #Ω(Mρ) ≥ #Ω(M) − #bad, and bad ⊆ ⋃ prescribed chains, giving #bad ≤ ε·#Ω(M).
5. `Paths.lean` — crossing paths → shapes (start offset, step directions). It provides the exact
   counts for L ≤ 7 (decide), the 3^{L−1} tail, and the series bound.
6. `Labelling.lean` — vertically consistent labellings:
   - partial injections are realized by ≤ r transpositions;
   - the glueing construction β' = π∘β̃, with π_{v+1} = ρ_v∘π_v;
   - the moves list, and T ≤ 2H.
7. `Seam.lean` — stage (a): VC gives F-sum ≥ F(i+1)(M'∘s). Stage (b): stars, then moves, then
   the arithmetic of γ_k ≥ 2ε_k. Plus the column-dependent telescope, Init and the end condition.
8. `Main.lean` — `ecc_boxProd_pathG_of_ten : 10 ≤ k → (pathG n □ pathG m).ECCAt k`, transported
   along pathG r ≃g pathGraph (r+1).

Rows are `Fin m` with `pathGraph m`, so v ± 1 and "rows > w" are arithmetic.
