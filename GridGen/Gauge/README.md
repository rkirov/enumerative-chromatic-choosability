# `GridGen/Gauge/` — every grid is `k`-ECC for `k ≥ 7`

`ListColoring.ecc_boxProd_pathG_of_seven : 7 ≤ k → (pathG r □ pathG n).ECCAt k`, for every height
and width (`ecc_boxProd_pathG_of_eight` and `ecc_boxProd_pathG_of_nine` are the `k ≥ 8` and
`k ≥ 9` steps). For `k ≥ 10` the proof uses the generic constants of `Seam.lean`
(`ecc_rowG_boxProd`), for `k = 9` the sharper ones of `Nine/`, for `k = 8` the relaxed telescope of
`Eight/`, and for `k = 7` the absorbing telescope of `Seven/`. It is complete (no unproved steps),
its axioms are `[propext, Classical.choice, Quot.sound]`, and the comparator claims the `k ≥ 7`
form (§18).

## The argument

GridGen's column telescope compares the actual chain of list columns with uniform futures through
a *reference*. The older references ranked colours by value (`patCap`). Their errors were not
local, and the weights they average were not a Gibbs measure.

Here the reference is a *gauge*. Each column's rows get bijections from their lists onto
`{0, …, k-1}` that are vertically consistent (VC): a colour shared by adjacent rows gets one label.
The telescoped quantity is

  `W j = ∑_{s ∈ column j} vec j s · F_{n-j}(gauge j ∘ s)`.

That is the number of correspondence (DP) colourings of an explicit cover of the whole grid.

* `W 0` is at least the uniform count: a VC labelling pulls uniform states back (`init_le`).
* `W n` is the list count.
* Each seam satisfies `W j ≤ W (j+1)` (`W_le_succ`):
  * **Stage (a).** The new column maps onto uniform states by its gauge (`stage_a`).
  * **Stage (b).** Expand the chain one or two columns back into *slabs*: a past column, the seam
    column, and the future (`Slab.lean`, `stage_b`). On each slab the old gauge's seam keys become
    the new gauge's keys in two phases (`slab_core`):
    * **Stars** (`Star.lean`, `Box.lean`). Each colour leaving its row deletes one seam pair. A
      fibre-by-fibre bound on the 2 + 6 cells around the pair shows that a
      `γ_k = (k-4)²(k-5)²/(k²(k-3)⁴)` fraction of solutions realizes the new pair.
    * **Moves** (`Kempe.lean`, `Bad.lean`, `Paths.lean`). The new gauge is glued from the old one
      by at most `2H` label transpositions on the rows below a row edge (`Labelling.lean`; `H` is
      the number of stars). A transposition loses at most the solutions in which an `x/y`-coloured
      component of the future joins seam cells on both sides of the edge. Swapping the remaining
      components is an injection (Kempe). The bad event needs an alternating crossing path. Each
      path is a chain whose prescribed colours cost `(k-3)^{L+1}(k-4)` (`CSP.lean`'s chain bound).
      Crossing paths are counted by their step shapes: `1, 2, 4, 10, 31, 76` exactly for `L ≤ 7`
      (`decide +kernel`), and at most `(L-1)3^{L-1}` beyond.
* **Threshold.** `2ε_k ≤ γ_k` for every `k ≥ 10` (`two_epsK_le_gammaK`). After substituting
  `k = 10 + u`, the difference is a polynomial in `u` with positive coefficients.

## Modules

| file | content |
|---|---|
| `CSP.lean` | finite constraint systems, fibres, the chain bound |
| `Slab.lean` | the slab model of a seam; `#Ω = ∑_p ∑_s F(keys ∘ s)` |
| `Star.lean` | deleting a seam pair adds exactly the solutions that use it |
| `Box.lean` | the box bound |
| `Kempe.lean` | the Kempe swap and the wall lemma |
| `Bad.lean` | bad solutions realize prescribed chains; union bound |
| `Paths.lean` | crossing-path shapes, their enumerator and counts, the series |
| `Labelling.lean` | transposition realization, glueing VC labellings, the move list |
| `Seam.lean` | `γ_k`, `ε_k`, the threshold, star and move steps, `slab_core` |
| `Main.lean` | gauges of a chain, stages (a) and (b), the telescope, `ecc_rowG_boxProd` |
| `Grid.lean` | `pathG r ≃g rowG (r+1)` |
| `Nine/` | the sharper constants and `ecc_boxProd_pathG_of_nine` |
| `Eight/` | relaxation gains, holes, exact counts to 18 cells, and `ecc_boxProd_pathG_of_eight` |
| `Seven/` | absorption into fresh stars, chordless paths, joint boxes, drift, and `ecc_boxProd_pathG_of_seven` |

## `k = 9` (`Nine/`)

The seam machinery is generic in the constants (`SlabBounds`, `GaugeBounds`). At `k = 9`:

* **Box** (`Nine/Box9.lean`). The fibre is split by the centre values `(a, b)`. The `y₁` factors
  sum to at most `53/5` lower-bound factors. For each label `b`, the `y₆` factor has ratio `1`
  or `6/5`, and each domino factor has ratio `9/7` or `3/2`, depending on whether `b` is
  available at that cell. At most `3, 2, 2` labels are unavailable, so the nine labels contribute
  at most `8478/490`. The result is `γ₉ = 2450/449334`, against `400/104976` for the uniform
  bound.
* **Paths** (`Nine/Bad9.lean`, `Nine/Counts.lean`). A 2-cell crossing path closes a 4-cycle with
  its seam cells; its first cell has two later neighbours, so its chain costs `7 · 6² · 5`. The
  other chains cost `5 · 6^{L+1}`. Shape counts are exact up to twelve cells:
  `212, 552, 1607, 4250, 12296` for `L = 8, …, 12`, by kernel evaluation of a count-only
  enumerator (about 2.5 minutes). The `(L-1)3^{L-1}` tail covers longer paths.
* **Threshold.** `(1 - ε₉)² ≥ 1 - γ₉` with a margin of about 3%.

## `k = 8` (`Eight/`)

At `k = 8` the method above fails: it needs `2ε ≤ γ`, and the path loss alone is about `0.0076`.
Three changes bring the condition to `ε ≤ γ`, `ε ≤ γ_V`:

* **Relaxation** (`SlabR.lean`, `BoxV.lean`). The next column's states are coloured from lists, so
  read through its (vertically consistent) gauge two adjacent cells may share any label that no
  shared colour carries. `slabR` allows those diagonal pairs; each one gains at least
  `γ_V = 152/27675` (a vertical box: the cells above and below, a list domino and a future domino).
* **Accounting** (`Holes.lean`, `Core8.lean`). A mismatched colour at an edge is new in the lower
  row or lies in the old column's vertical difference, so the transpositions number at most
  `H + D_A`. With the potential `(1 − ε)^{D_j} W_j` (`Main8.lean`) each column's vertical
  difference is charged once, to its own relaxation.
* **Holes** (`Holes.lean`, `Bad8.lean`). Every mismatch has an endpoint label that the deleted
  pairs leave unmatched in one of the two rows. `realizeH` builds the transpositions through these
  holes, and a move through a hole leaves the two-cell crossing path one phase, so the 4-cycle term
  is `1/600` instead of `2/600`.

The star gain is the `k = 9` box at `k = 8`, `γ₈ = 5184/960375` (`Box8.lean`). Crossing paths are
counted exactly up to eighteen cells (`Counts8.lean`): a level-by-level dynamic program for `cntW`
on a grid with a clamped bottom row, about 20 seconds of kernel evaluation. Then
`ε₈ ≈ 0.00474 ≤ γ₈ ≈ 0.00540, γ_V ≈ 0.00549` (`Seam8.lean`). At `k = 7` this accounting fails by
a factor of about four: the union bound over paths with `1/(k−3)` per step is the obstacle.

## `k = 7` (`Seven/`)

The seam machinery of `k = 8` is kept (relaxation, holes, the potential `(1 − γ_V)^{D} W`), with
four changes.

* **Absorption** (`Core7.lean`, `Seam7.lean`, `Order7.lean`). A star is deleted *just before* the
  moves through its hole, so a move's losses are compared with the fresh star's hit event
  `{(1, r) = a₀, (2, r) = h}` in the same cover, not with the whole count. The transpositions are
  processed in a lookahead order (`proc`, `runEdge`), and a doubly designated colour's two moves
  are pooled with its star (`step_slab_double`). The conditions are those of `Bounds7`.
* **Chordless witnesses** (`Chordless.lean`, `Short7.lean`, `Counts7.lean`). A shortest
  alternating path is chordless, and through the hole its phase at the hole row is forced. Paths
  with an end at the hole row are *absorbed* (charged to the hit event), the others *residual*.
  Chordless crossing paths are counted by a window-3 dynamic program up to twenty cells
  (`A7_vals`, `R7_vals`, kernel evaluation), with a `√7` growth tail beyond. Short chordless
  crossing paths are vertical (`vert_two`, `vert_three`).
* **Boxes against the star.**
  * The star itself: `γ₇ = 432/69101` (`Box7.lean`). The relaxation gain: `γ_V = 27/5075`
    (`BoxV7.lean`).
  * The two-cell absorbed path (the 4-cycle with the seam): `θ₂ ≤ 512/3969` (`BoxT2.lean`), with
    the last-row orientation by reflecting rows (`Reflect7.lean`).
  * Longer absorbed paths: a swap comparison at the seam (`SwapSlab7.lean`, factor `64/27`) and the
    chain bound inside the hit event (`AbsChain7.lean`, `Cond7.lean`).
  * The three-cell residual path runs through the star's own future cell, and is charged to the
    hit event too: `7/81` per phase (`BoxJ3.lean`). Longer residual paths take the chain bound
    against the whole count.

  Summed (`MoveB7.lean`): a move through a fresh hole loses at most `θ · #Hit + ε · Z` with
  `θ = 189/500`, `ε = 1/337`.
* **Drift** (`Drift7.lean`). Between a double's two moves the hit event can grow. Running the first
  move backwards is a Kempe injection that keeps the hit event unless the solution is bad or
  `(2, r)` is swapped. Both are crossing chains read off cells other than `(1, r)` and `(2, r)`, so
  the chain bound holds inside the hit event. This gives the factor `1 + 7/50`.

With these constants every condition of `Bounds7` holds (`Final7.lean`); the tightest, the pooled
double, by about `5.6 · 10⁻⁴`. `Assemble7.lean` gives `ecc_boxProd_pathG_of_seven`.

## Credit

The route and its proof are new in this development, worked out by Claude (Anthropic) on
2026-10-15 to 18 (`k ≥ 8`) and 2026-10-18 to 22 (`k = 7`). The building blocks are classical:
* DP-colourings are Dvořák–Postle's;
* the swap is Kempe's;
* the column telescope is GridGen's (`GridGen/Telescope.lean`), used here with a column-dependent
  reference.
