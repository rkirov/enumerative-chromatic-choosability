/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring
import Mathlib.Data.Fintype.Perm

/-!
# A clique times a star is not enumeratively chromatic-choosable

**Kirov–Naimi 2016, §6, Question 1** asks whether the Cartesian product of two `n`-monophilic
graphs is `n`-monophilic, for `n ≥ 3`. The answer is **no**, and the witness is the standard
example of a Cartesian product that is not chromatic-choosable.

## The construction

For `k ≥ 2` let `G = K_k`, the complete graph on `Fin k`, and let `H` be the star whose leaves are
the `k!` permutations of `Fin k`. Both are chordal, so both are enumeratively chromatic-choosable
at every list size (Kostochka–Sidorenko, `SimpleGraph.ecc_of_isChordal`). In `G □ H`:

* the vertex `(j, centre)` gets the list `{0, …, k-1}`;
* the vertex `(j, leaf σ)` gets the list `{σ j} ∪ {k, …, 2k-2}`.

Every list has `k` colours. A proper colouring from these lists restricts on the centre copy of
`K_k` to a bijection onto `{0, …, k-1}`, that is, to a permutation `τ`. In the leaf copy indexed
by that same `τ`, the vertex `(j, leaf τ)` is adjacent to `(j, centre)`, which already carries
`τ j`; so all `k` pairwise adjacent vertices of that copy must be coloured from the `k - 1`
colours `{k, …, 2k-2}`, which is impossible. Hence there is **no** colouring from these lists,
while `K_k □ H` is `k`-colourable. So `K_k □ H` is not even `k`-choosable, let alone
enumeratively chromatic-choosable at `k`.

## Provenance

**The mathematics is not ours.** The construction — a clique times a star with one leaf per
bijection, with exactly these lists — is the standard proof that a Cartesian product with a
large enough star is not chromatic-choosable: Borowiecki, Jendrol', Král' and Miškuf, *List
coloring of Cartesian products of graphs*, Discrete Math. **306** (2006), who prove
`χ_ℓ(G □ K_{a,b}) = χ_ℓ(G) + a` once `b ≥ (χ_ℓ(G) + a - 1)^{a|V(G)|}`, and Kaul and Mudrock, *List
coloring a Cartesian product with a complete bipartite factor*
([arXiv:1811.02420](https://arxiv.org/abs/1811.02420)), who sharpen the number of leaves needed
using the list color function. The only thing recorded here as new is the observation
(2026-11-09) that this well-known example answers Kirov–Naimi's Question 1.

## Main statements

* `ProductCounterexample.isChordal_starG`, `ecc_starG`, `ecc_top` — both factors are ECC at
  every list size;
* `ProductCounterexample.col_badList` — there is no colouring from the lists above;
* `ProductCounterexample.not_ecc_top_boxProd_star` — `K_k □ star` is not ECC at `k`, for `k ≥ 2`;
* `ProductCounterexample.ProductQuestion`, `not_productQuestion` — Question 1, verbatim, and its
  negation.
-/

open Finset SimpleGraph

namespace ProductCounterexample

/-! ### The star -/

/-- The **star** with centre `none` and one leaf `some i` for each `i : ι`. Two vertices are
adjacent exactly when one of them is the centre and the other is not. -/
def starG (ι : Type*) : SimpleGraph (Option ι) where
  Adj a b := (a = none ∧ b ≠ none) ∨ (a ≠ none ∧ b = none)
  symm := ⟨fun _ _ h => h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.2 h.1) (fun h => h.1 h.2)⟩

instance (ι : Type*) [DecidableEq ι] : DecidableRel (starG ι).Adj := fun a b =>
  inferInstanceAs (Decidable ((a = none ∧ b ≠ none) ∨ (a ≠ none ∧ b = none)))

lemma starG_adj {ι : Type*} {a b : Option ι} :
    (starG ι).Adj a b ↔ (a = none ∧ b ≠ none) ∨ (a ≠ none ∧ b = none) := Iff.rfl

/-- **A star is chordal** — it has no cycle of length `4` or more at all. Along any walk the
centre occupies every other position, so a closed walk of length at least `4` visits the centre
twice among its first four vertices, and a cycle cannot. -/
theorem isChordal_starG (ι : Type*) : (starG ι).IsChordal := by
  intro u c hc hlen _
  have hinj := hc.getVert_injOn'
  have h01 := c.adj_getVert_succ (i := 0) (by omega)
  have h12 := c.adj_getVert_succ (i := 1) (by omega)
  have h23 := c.adj_getVert_succ (i := 2) (by omega)
  simp only [starG_adj] at h01 h12 h23
  have e02 : c.getVert 0 = c.getVert 2 → False := fun h => by
    have := hinj (show 0 ≤ c.length - 1 by omega) (show 2 ≤ c.length - 1 by omega) h
    omega
  have e13 : c.getVert 1 = c.getVert 3 → False := fun h => by
    have := hinj (show 1 ≤ c.length - 1 by omega) (show 3 ≤ c.length - 1 by omega) h
    omega
  rcases h01 with ⟨a, b⟩ | ⟨a, b⟩
  · rcases h12 with ⟨a', _⟩ | ⟨_, b'⟩
    · exact b a'
    · exact e02 (a.trans b'.symm)
  · rcases h12 with ⟨a', b'⟩ | ⟨a', _⟩
    · rcases h23 with ⟨a'', _⟩ | ⟨_, b''⟩
      · exact b' a''
      · exact e13 (b.trans b''.symm)
    · exact a' b

/-- A star is enumeratively chromatic-choosable at every list size (Kostochka–Sidorenko, since it
is chordal). -/
theorem ecc_starG (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) : (starG ι).ECCAt n :=
  ecc_of_isChordal _ (isChordal_starG ι) n

/-- A complete graph is enumeratively chromatic-choosable at every list size
(Kostochka–Sidorenko, since it is chordal). -/
theorem ecc_top (α : Type) [Fintype α] [DecidableEq α] (n : ℕ) :
    (⊤ : SimpleGraph α).ECCAt n :=
  ecc_of_isChordal _ isChordal_top n

/-! ### The product and its bad lists -/

/-- The star with one leaf for each permutation of `Fin k`. -/
abbrev star (k : ℕ) : SimpleGraph (Option (Equiv.Perm (Fin k))) := starG (Equiv.Perm (Fin k))

/-- The list assignment of Borowiecki–Jendrol'–Král'–Miškuf and Kaul–Mudrock on `K_k □ star`:
`{0, …, k-1}` on the centre copy, and `{σ j} ∪ {k, …, 2k-2}` at `(j, σ)` in the leaf copy of the
permutation `σ`. -/
def badList (k : ℕ) : ListAssignment (Fin k × Option (Equiv.Perm (Fin k)))
  | (_, none) => range k
  | (j, some σ) => insert (σ j : ℕ) (Ico k (2 * k - 1))

theorem isNListAssignment_badList (k : ℕ) : IsNListAssignment (badList k) k := by
  rintro ⟨j, _ | σ⟩
  · exact card_range k
  · have hj := (σ j).isLt
    change (insert (σ j : ℕ) (Ico k (2 * k - 1))).card = k
    rw [card_insert_of_notMem (by simp), Nat.card_Ico]
    omega

/-- **No colouring from the bad lists.** The centre copy of `K_k` is coloured by a permutation
`τ`; the leaf copy indexed by `τ` then has `k` pairwise adjacent vertices and only the `k - 1`
colours `{k, …, 2k-2}` left. -/
theorem col_badList (k : ℕ) (hk : 0 < k) :
    ((⊤ : SimpleGraph (Fin k)) □ star k).col (badList k) = 0 := by
  rw [col_eq_zero_iff]
  intro f hf hp
  -- the colouring of the centre copy, as a map `Fin k → Fin k`
  let g : Fin k → Fin k := fun j => ⟨f (j, none), mem_range.mp (hf (j, none))⟩
  have hg : Function.Injective g := by
    intro a b hab
    by_contra hne
    exact hp (v := (a, none)) (w := (b, none))
      (boxProd_adj_left.mpr ((top_adj a b).mpr hne)) (congrArg Fin.val hab)
  let τ : Equiv.Perm (Fin k) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
  have hτ : ∀ j, (τ j : ℕ) = f (j, none) := fun _ => rfl
  -- in the leaf copy of `τ` only the colours `k, …, 2k-2` are available
  have hmem : ∀ j ∈ (univ : Finset (Fin k)), f (j, some τ) ∈ Ico k (2 * k - 1) := by
    intro j _
    have h1 : f (j, some τ) ∈ insert (τ j : ℕ) (Ico k (2 * k - 1)) := hf (j, some τ)
    have h2 : f (j, none) ≠ f (j, some τ) :=
      hp (v := (j, none)) (w := (j, some τ))
        (boxProd_adj_right.mpr (Or.inl ⟨rfl, Option.some_ne_none τ⟩))
    rcases mem_insert.mp h1 with h | h
    · exact absurd (h.trans (hτ j)).symm h2
    · exact h
  have hcard : (Ico k (2 * k - 1)).card < (univ : Finset (Fin k)).card := by
    rw [Nat.card_Ico, card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, _, b, _, hne, hab⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmem
  exact hp (v := (a, some τ)) (w := (b, some τ))
    (boxProd_adj_left.mpr ((top_adj a b).mpr hne)) hab

/-- `K_k □ star` is `k`-colourable when `k ≥ 2`: colour `(j, centre)` by `j` and every `(j, leaf)`
by `j + 1` modulo `k`. -/
theorem colConst_pos (k : ℕ) (hk : 2 ≤ k) :
    0 < ((⊤ : SimpleGraph (Fin k)) □ star k).colConst k := by
  rw [colConst, col_pos_iff]
  refine ⟨fun v => match v with
    | (j, none) => (j : ℕ)
    | (j, some _) => if (j : ℕ) + 1 < k then (j : ℕ) + 1 else 0, ?_⟩
  rw [mem_colorings]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, _ | σ⟩
    · exact mem_range.mpr j.isLt
    · have := j.isLt
      simp only [constList_apply, mem_range]
      split_ifs <;> omega
  · rintro ⟨a, x⟩ ⟨b, y⟩ hadj
    have ha := a.isLt
    have hb := b.isLt
    rw [boxProd_adj] at hadj
    rcases hadj with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · have hne : (a : ℕ) ≠ b := fun e => (top_adj a b).mp h (Fin.ext e)
      rcases x with _ | σ
      · exact hne
      · simp only
        split_ifs <;> omega
    · dsimp only at h ha hb ⊢
      rcases x with _ | σ <;> rcases y with _ | ρ
      · exact absurd h (by simp)
      · simp only
        split_ifs <;> omega
      · simp only
        split_ifs <;> omega
      · exact absurd h (by simp [starG_adj])

/-- **A clique times a star is not enumeratively chromatic-choosable** (Borowiecki–Jendrol'–
Král'–Miškuf 2006; Kaul–Mudrock, arXiv:1811.02420). For every `k ≥ 2` the product of `K_k` with
the star on `k!` leaves is not ECC at `k`, although both factors are ECC at every list size
(`ecc_top`, `ecc_starG`): it is `k`-colourable and has a `k`-list assignment with no colouring. -/
theorem not_ecc_top_boxProd_star (k : ℕ) (hk : 2 ≤ k) :
    ¬ ((⊤ : SimpleGraph (Fin k)) □ star k).ECCAt k := by
  intro h
  have h1 := h (badList k) (isNListAssignment_badList k)
  rw [col_badList k (by omega)] at h1
  have h2 := colConst_pos k hk
  omega

/-! ### The question it settles -/

/-- **Kirov–Naimi 2016, §6, Question 1**, verbatim: *is the product of two `n`-monophilic graphs
`n`-monophilic*, for `n ≥ 3`?

A copy of `ListColoring.OpenProblem.Question1`. It is restated rather than imported so that this
library never depends on `OpenProblems.lean`, which carries an unproved statement. -/
def ProductQuestion : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (G : SimpleGraph α) [DecidableRel G.Adj] (H : SimpleGraph β) [DecidableRel H.Adj],
      G.ECCAt n → H.ECCAt n → (G □ H).ECCAt n

/-- **The answer: no.** `K₃` and the star with six leaves are both enumeratively
chromatic-choosable at `3` (indeed at every list size), and their Cartesian product is not.

The construction is Borowiecki–Jendrol'–Král'–Miškuf's and Kaul–Mudrock's; see the module
docstring. -/
theorem not_productQuestion : ¬ ProductQuestion := fun h =>
  not_ecc_top_boxProd_star 3 (by norm_num)
    (h 3 le_rfl (⊤ : SimpleGraph (Fin 3)) (star 3) (ecc_top (Fin 3) 3) (ecc_starG _ 3))

/-! ### Axiom audit -/

/-- info: 'ProductCounterexample.not_ecc_top_boxProd_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_ecc_top_boxProd_star

/-- info: 'ProductCounterexample.not_productQuestion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_productQuestion

end ProductCounterexample
