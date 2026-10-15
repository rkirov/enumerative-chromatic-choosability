/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Relabel

/-!
# Height four: the uniform transfer and its invariant box

**Counting.** On a proper column the pattern weight is an affine combination of the indicators
of `r1 = r3`, `r2 = r4`, both, and `r1 = r4` (`gw_split`), so `G w A B C D` is a combination of
five counts (`G_split`). Each count has an exact inclusion–exclusion form in the sizes of the
lists and their intersections (`card_sts_formula` from `Defs`, `card_eq13`, `card_eq24`,
`card_eq1324`, `card_eq14`), via one counting lemma: a colour from `S` avoiding two colours of a
tail (`card_pairAvoid`).

**The uniform transfer.** On punctured ranges these become polynomials in `ℓ = k - 2`: for the
five canonical patterns `0101, 0102, 0121, 0120, 0123`, `GU k w` is the corresponding row of the
reduced matrix of `ai_research_notes/CODEX_H4_SEAM_BOUNDS_2026-10-15.md` §1 (eq. (3)) applied to
`(1, a, b, c)` (`GU_0101`, …, `GU_0123`; rows `vA`, `vB`, `vC`, `vD`, with `0102` and `0121`
sharing `vB`). So the uniform transfer of a pattern weight is again a pattern weight:
`GU k w s = vA · gw (nextW k w) s` (`GU_eq`).

**The box.** For `k ≥ 5` the transfer maps the box `ρ ≤ a, b, c ≤ 1`, `ρ = 1 - 2/(k-2)³`, into
itself (`nextW_inBox`): `ρ·vA ≤ vX ≤ vA` is affine in the weights, so it suffices at the eight
corners (`aff_nonneg`), and there, with `ℓ = m + 3`, it is a polynomial in `m` with nonnegative
coefficients after clearing `ℓ³` or `ℓ⁶`.

**The uniform futures.** `Fu k i` — the weighted uniform futures of a column — is
`fseq k i · gw (wseq k i)` on proper uniform columns, with `wseq k i` in the box and
`fseq k i > 0` (`Fu_eq`, `wseq_inBox`, `fseq_pos`), by induction from `Fu k 0 = 1`.
-/


namespace GridGen.Four

open Finset

/-! ### Counting colourings by their non-consecutive equalities -/

theorem cast_card_erase (s : Finset ℕ) (a : ℕ) :
    ((s.erase a).card : ℤ) = s.card - if a ∈ s then 1 else 0 := by
  split_ifs with h
  · have := Finset.card_erase_add_one h; omega
  · rw [Finset.erase_eq_of_notMem h]; simp

/-- Avoiding two colours `x, y` in a list. -/
theorem card_filter_ne_ne (S : Finset ℕ) (x y : ℕ) :
    ((S.filter (fun a => a ≠ x ∧ a ≠ y)).card : ℤ) =
      S.card - (if x ∈ S then 1 else 0) - (if y ∈ S then 1 else 0)
        + (if x ∈ S ∧ x = y then 1 else 0) := by
  have h : S.filter (fun a => a ≠ x ∧ a ≠ y) = (S.erase x).erase y := by
    ext a; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  rw [h, cast_card_erase, cast_card_erase]
  simp only [Finset.mem_erase]
  by_cases hxy : x = y
  · subst hxy; by_cases hx : x ∈ S <;> simp [hx]
  · by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy, hxy, Ne.symm hxy]

/-- A colour of a list that avoids the two colours `f r`, `g r` of a tail `r`. -/
theorem card_pairAvoid {β : Type*} [DecidableEq β] (S : Finset ℕ) (R : Finset β) (f g : β → ℕ) :
    (((S ×ˢ R).filter (fun p => p.1 ≠ f p.2 ∧ p.1 ≠ g p.2)).card : ℤ) =
      S.card * R.card - (R.filter (fun r => f r ∈ S)).card - (R.filter (fun r => g r ∈ S)).card
        + (R.filter (fun r => f r ∈ S ∧ f r = g r)).card := by
  have h := card_filter_prod S R (fun _ => True) (fun a r => a ≠ f r ∧ a ≠ g r)
  simp only [true_and, Finset.filter_true] at h
  rw [h]
  have hswap : ∑ a ∈ S, (R.filter (fun r => a ≠ f r ∧ a ≠ g r)).card =
      ∑ r ∈ R, (S.filter (fun a => a ≠ f r ∧ a ≠ g r)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  push_cast
  rw [Finset.sum_congr rfl (fun r _ => card_filter_ne_ne S (f r) (g r))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole]
  ring

/-- The diagonal of a product, restricted to a list. -/
theorem card_diag (S X Y : Finset ℕ) :
    ((X ×ˢ Y).filter (fun r => r.1 ∈ S ∧ r.1 = r.2)).card = (X ∩ Y ∩ S).card := by
  refine Finset.card_nbij' (fun r => r.1) (fun x => (x, x)) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hr
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hr
    exact ⟨⟨h1, h4 ▸ h2⟩, h3⟩
  · intro x hx
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hx
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq]
    exact ⟨⟨hx.1.1, hx.1.2⟩, hx.2, trivial⟩
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hr
    obtain ⟨r1, r2⟩ := r
    simp only at hr ⊢
    rw [hr.2.2]
  · intro x _; rfl

/-- A star: a centre from `S` avoiding two leaves from `X` and `Y`. -/
theorem card_star (S X Y : Finset ℕ) :
    (((S ×ˢ (X ×ˢ Y)).filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2)).card : ℤ) =
      S.card * X.card * Y.card - (X ∩ S).card * Y.card - X.card * (Y ∩ S).card
        + (X ∩ Y ∩ S).card := by
  have h := card_pairAvoid S (X ×ˢ Y) Prod.fst Prod.snd
  rw [Finset.filter_product_left (fun x => x ∈ S), Finset.filter_product_right (fun y => y ∈ S),
    card_diag, Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter] at h
  rw [h]; push_cast; ring

/-- A triangle with lists `S`, `X`, `Y`. -/
theorem card_triangle (S X Y : Finset ℕ) :
    (((S ×ˢ sts2 X Y).filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2)).card : ℤ) =
      S.card * (X.card * Y.card - (X ∩ Y).card) - ((X ∩ S).card * Y.card - (X ∩ S ∩ Y).card)
        - (X.card * (Y ∩ S).card - (X ∩ (Y ∩ S)).card) := by
  have h := card_pairAvoid S (sts2 X Y) Prod.fst Prod.snd
  have e1 : (sts2 X Y).filter (fun r => r.1 ∈ S) = sts2 (X ∩ S) Y := by
    ext p; simp only [Finset.mem_filter, mem_sts2, Finset.mem_inter]; tauto
  have e2 : (sts2 X Y).filter (fun r => r.2 ∈ S) = sts2 X (Y ∩ S) := by
    ext p; simp only [Finset.mem_filter, mem_sts2, Finset.mem_inter]; tauto
  have e3 : (sts2 X Y).filter (fun r => r.1 ∈ S ∧ r.1 = r.2) = ∅ := by
    ext p; simp only [Finset.mem_filter, mem_sts2, Finset.notMem_empty, iff_false]; tauto
  rw [e1, e2, e3, Finset.card_empty, card_sts2, card_sts2, card_sts2] at h
  rw [h]; push_cast; ring

/-- Colourings with `r1 = r3`. -/
theorem card_eq13 (A B C D : Finset ℕ) :
    (((sts A B C D).filter (fun t => r1 t = r3 t)).card : ℤ) =
      (A ∩ C).card * B.card * D.card - (B ∩ (A ∩ C)).card * D.card
        - B.card * (D ∩ (A ∩ C)).card + (B ∩ D ∩ (A ∩ C)).card := by
  rw [← card_star]
  congr 1
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r4 t)) (fun p => (p.1, p.2.1, p.1, p.2.2))
    ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, mem_sts, Set.mem_ofPred_eq] at ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_inter, Set.mem_ofPred_eq]
    obtain ⟨⟨h1, h2, h3, h4, p1, p2, p3⟩, e⟩ := ht
    exact ⟨⟨⟨h1, e ▸ h3⟩, h2, h4⟩, p1, e ▸ p3⟩
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_inter, Set.mem_ofPred_eq] at hp
    simp only [Finset.coe_filter, mem_sts, Set.mem_ofPred_eq]
    obtain ⟨⟨⟨h1, h3⟩, h2, h4⟩, p1, p2⟩ := hp
    exact ⟨⟨h1, h2, h3, h4, p1, Ne.symm p1, p2⟩, trivial⟩
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht
    obtain ⟨t1, t2, t3, t4⟩ := t
    simp only [r1, r3] at ht ⊢
    rw [ht.2]
  · intro p _; rfl

/-- Colourings with `r2 = r4`. -/
theorem card_eq24 (A B C D : Finset ℕ) :
    (((sts A B C D).filter (fun t => r2 t = r4 t)).card : ℤ) =
      (B ∩ D).card * A.card * C.card - (A ∩ (B ∩ D)).card * C.card
        - A.card * (C ∩ (B ∩ D)).card + (A ∩ C ∩ (B ∩ D)).card := by
  rw [← card_star]
  congr 1
  refine Finset.card_nbij' (fun t => (r2 t, r1 t, r3 t)) (fun p => (p.2.1, p.1, p.2.2, p.1))
    ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, mem_sts, Set.mem_ofPred_eq] at ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_inter, Set.mem_ofPred_eq]
    obtain ⟨⟨h1, h2, h3, h4, p1, p2, p3⟩, e⟩ := ht
    exact ⟨⟨⟨h2, e ▸ h4⟩, h1, h3⟩, Ne.symm p1, p2⟩
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_inter, Set.mem_ofPred_eq] at hp
    simp only [Finset.coe_filter, mem_sts, Set.mem_ofPred_eq]
    obtain ⟨⟨⟨h2, h4⟩, h1, h3⟩, p1, p2⟩ := hp
    exact ⟨⟨h1, h2, h3, h4, Ne.symm p1, p2, Ne.symm p2⟩, trivial⟩
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht
    obtain ⟨t1, t2, t3, t4⟩ := t
    simp only [r2, r4] at ht ⊢
    rw [ht.2]
  · intro p _; rfl

/-- Colourings with `r1 = r3` and `r2 = r4`. -/
theorem card_eq1324 (A B C D : Finset ℕ) :
    (((sts A B C D).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℤ) =
      (A ∩ C).card * (B ∩ D).card - ((A ∩ C) ∩ (B ∩ D)).card := by
  rw [← card_sts2]
  congr 1
  refine Finset.card_nbij' (fun t => (r1 t, r2 t)) (fun p => (p.1, p.2, p.1, p.2)) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, mem_sts, Set.mem_ofPred_eq] at ht
    simp only [Finset.mem_coe, mem_sts2, Finset.mem_inter]
    obtain ⟨⟨h1, h2, h3, h4, p1, p2, p3⟩, e, e'⟩ := ht
    exact ⟨⟨h1, e ▸ h3⟩, ⟨h2, e' ▸ h4⟩, p1⟩
  · intro p hp
    simp only [Finset.mem_coe, mem_sts2, Finset.mem_inter] at hp
    simp only [Finset.coe_filter, mem_sts, Set.mem_ofPred_eq]
    obtain ⟨⟨h1, h3⟩, ⟨h2, h4⟩, p1⟩ := hp
    exact ⟨⟨h1, h2, h3, h4, p1, Ne.symm p1, p1⟩, trivial, trivial⟩
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht
    obtain ⟨t1, t2, t3, t4⟩ := t
    simp only [r1, r2, r3, r4] at ht ⊢
    rw [ht.2.1, ht.2.2]
  · intro p _; rfl

/-- Colourings with `r1 = r4`. -/
theorem card_eq14 (A B C D : Finset ℕ) :
    (((sts A B C D).filter (fun t => r1 t = r4 t)).card : ℤ) =
      (A ∩ D).card * (B.card * C.card - (B ∩ C).card)
        - ((B ∩ (A ∩ D)).card * C.card - (B ∩ (A ∩ D) ∩ C).card)
        - (B.card * (C ∩ (A ∩ D)).card - (B ∩ (C ∩ (A ∩ D))).card) := by
  rw [← card_triangle]
  congr 1
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r3 t)) (fun p => (p.1, p.2.1, p.2.2, p.1))
    ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, mem_sts, Set.mem_ofPred_eq] at ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_inter, mem_sts2,
      Set.mem_ofPred_eq]
    obtain ⟨⟨h1, h2, h3, h4, p1, p2, p3⟩, e⟩ := ht
    exact ⟨⟨⟨h1, e ▸ h4⟩, h2, h3, p2⟩, p1, fun h => p3 (h ▸ e)⟩
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_inter, mem_sts2,
      Set.mem_ofPred_eq] at hp
    simp only [Finset.coe_filter, mem_sts, Set.mem_ofPred_eq]
    obtain ⟨⟨⟨h1, h4⟩, h2, h3, p2⟩, p1, p3⟩ := hp
    exact ⟨⟨h1, h2, h3, h4, p1, p2, Ne.symm p3⟩, trivial⟩
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht
    obtain ⟨t1, t2, t3, t4⟩ := t
    simp only [r1, r4] at ht ⊢
    rw [ht.2]
  · intro p _; rfl

/-! ### The weighted count from the counts -/

/-- The pattern weight as a combination of the indicators of `r1 = r3`, `r2 = r4`, both, and
`r1 = r4` (on a proper column the last excludes the first two). -/
theorem gw_split (w : Wt) {t : T4} (ht : Proper t) :
    gw w t = w.c + (w.a - w.c) * ((if r1 t = r3 t then 1 else 0) + (if r2 t = r4 t then 1 else 0))
      + (1 - 2 * w.a + w.c) * (if r1 t = r3 t ∧ r2 t = r4 t then 1 else 0)
      + (w.b - w.c) * (if r1 t = r4 t then 1 else 0) := by
  obtain ⟨p1, p2, p3⟩ := ht
  unfold gw
  by_cases h13 : r1 t = r3 t
  · have h14 : r1 t ≠ r4 t := fun h => p3 (h13 ▸ h)
    by_cases h24 : r2 t = r4 t
    · simp [eq_true h13, eq_true h24, eq_false h14]; ring
    · simp [eq_true h13, eq_false h24, eq_false h14]
  · by_cases h24 : r2 t = r4 t
    · have h14 : r1 t ≠ r4 t := fun h => p1 (h ▸ h24.symm ▸ rfl)
      simp [eq_false h13, eq_true h24, eq_false h14]
    · by_cases h14 : r1 t = r4 t
      · simp [eq_false h13, eq_false h24, eq_true h14]
      · simp [eq_false h13, eq_false h24, eq_false h14]

/-- **The weighted count in terms of four counts.** -/
theorem G_split (w : Wt) (A B C D : Finset ℕ) :
    G w A B C D = w.c * (((sts A B C D).card : ℤ) : ℝ)
      + (w.a - w.c) * ((((sts A B C D).filter (fun t => r1 t = r3 t)).card : ℤ)
          + (((sts A B C D).filter (fun t => r2 t = r4 t)).card : ℤ) : ℝ)
      + (1 - 2 * w.a + w.c)
          * ((((sts A B C D).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℤ) : ℝ)
      + (w.b - w.c) * ((((sts A B C D).filter (fun t => r1 t = r4 t)).card : ℤ) : ℝ) := by
  unfold G
  rw [Finset.sum_congr rfl (fun t ht => gw_split w (proper_of_mem_sts ht))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole, Int.cast_natCast]
  ring

/-! ### The uniform transfer on the five patterns -/

theorem cast_card_erase_real (s : Finset ℕ) (a : ℕ) :
    ((s.erase a).card : ℝ) = s.card - if a ∈ s then 1 else 0 := by
  have h := cast_card_erase s a
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- An affine function of the weights. -/
def aff (p0 p1 p2 p3 : ℝ) (w : Wt) : ℝ := p0 + p1 * w.a + p2 * w.b + p3 * w.c

/-- The reduced uniform transfer: row `0101`, on the weights `(1, a, b, c)`, `ℓ = k - 2`. -/
def vA (l : ℝ) (w : Wt) : ℝ :=
  aff (l ^ 2 + l + 1) (2 * l ^ 3 + 2 * l) (l ^ 3 - l ^ 2 + l) (l ^ 4 - 2 * l ^ 3 + 3 * l ^ 2 - 2 * l) w

/-- Row `0102` (and `0121`). -/
def vB (l : ℝ) (w : Wt) : ℝ :=
  aff (l ^ 2 + 1) (2 * l ^ 3 - l ^ 2 + 4 * l - 1) (l ^ 3 - l ^ 2 + 2 * l - 1)
    (l ^ 4 - 2 * l ^ 3 + 4 * l ^ 2 - 5 * l + 2) w

/-- Row `0120`. -/
def vC (l : ℝ) (w : Wt) : ℝ :=
  aff (l ^ 2 - l + 1) (2 * l ^ 3 - 2 * l ^ 2 + 4 * l - 2) (l ^ 3 + 2 * l - 1)
    (l ^ 4 - 2 * l ^ 3 + 4 * l ^ 2 - 5 * l + 2) w

/-- Row `0123`. -/
def vD (l : ℝ) (w : Wt) : ℝ :=
  aff (l ^ 2 - l + 2) (2 * l ^ 3 - 2 * l ^ 2 + 6 * l - 4) (l ^ 3 - l ^ 2 + 3 * l - 2)
    (l ^ 4 - 2 * l ^ 3 + 5 * l ^ 2 - 8 * l + 5) w

/-- The uniform successors of a canonical column, as a weighted count over punctured ranges. -/
theorem GU_of_canon {k : ℕ} (w : Wt) {s : T4} (hs : canon s = s) :
    GU k w s = G w ((range k).erase (r1 s)) ((range k).erase (r2 s)) ((range k).erase (r3 s))
      ((range k).erase (r4 s)) := by
  unfold GU; rw [hs]

/-- The uniform transfer from `0101`. -/
theorem GU_0101 {k : ℕ} (hk : 4 ≤ k) (w : Wt) : GU k w (0, 1, 0, 1) = vA ((k : ℝ) - 2) w := by
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  rw [GU_of_canon w (by decide), G_split, card_sts_formula, card_eq13, card_eq24, card_eq1324,
    card_eq14]
  simp only [Finset.erase_inter, Finset.inter_erase, Finset.inter_self]
  push_cast
  simp only [cast_card_erase_real, Finset.mem_erase, Finset.mem_range, Finset.card_range]
  norm_num [h0, h1, vA, aff]
  ring

/-- The uniform transfer from `0102`. -/
theorem GU_0102 {k : ℕ} (hk : 4 ≤ k) (w : Wt) : GU k w (0, 1, 0, 2) = vB ((k : ℝ) - 2) w := by
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  have h2 : 2 < k := by omega
  rw [GU_of_canon w (by decide), G_split, card_sts_formula, card_eq13, card_eq24, card_eq1324,
    card_eq14]
  simp only [Finset.erase_inter, Finset.inter_erase, Finset.inter_self]
  push_cast
  simp only [cast_card_erase_real, Finset.mem_erase, Finset.mem_range, Finset.card_range]
  norm_num [h0, h1, h2, vB, aff]
  ring

/-- The uniform transfer from `0121`. -/
theorem GU_0121 {k : ℕ} (hk : 4 ≤ k) (w : Wt) : GU k w (0, 1, 2, 1) = vB ((k : ℝ) - 2) w := by
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  have h2 : 2 < k := by omega
  rw [GU_of_canon w (by decide), G_split, card_sts_formula, card_eq13, card_eq24, card_eq1324,
    card_eq14]
  simp only [Finset.erase_inter, Finset.inter_erase, Finset.inter_self]
  push_cast
  simp only [cast_card_erase_real, Finset.mem_erase, Finset.mem_range, Finset.card_range]
  norm_num [h0, h1, h2, vB, aff]
  ring

/-- The uniform transfer from `0120`. -/
theorem GU_0120 {k : ℕ} (hk : 4 ≤ k) (w : Wt) : GU k w (0, 1, 2, 0) = vC ((k : ℝ) - 2) w := by
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  have h2 : 2 < k := by omega
  rw [GU_of_canon w (by decide), G_split, card_sts_formula, card_eq13, card_eq24, card_eq1324,
    card_eq14]
  simp only [Finset.erase_inter, Finset.inter_erase, Finset.inter_self]
  push_cast
  simp only [cast_card_erase_real, Finset.mem_erase, Finset.mem_range, Finset.card_range]
  norm_num [h0, h1, h2, vC, aff]
  ring

/-- The uniform transfer from `0123`. -/
theorem GU_0123 {k : ℕ} (hk : 4 ≤ k) (w : Wt) : GU k w (0, 1, 2, 3) = vD ((k : ℝ) - 2) w := by
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  have h2 : 2 < k := by omega
  have h3 : 3 < k := by omega
  rw [GU_of_canon w (by decide), G_split, card_sts_formula, card_eq13, card_eq24, card_eq1324,
    card_eq14]
  simp only [Finset.erase_inter, Finset.inter_erase, Finset.inter_self]
  push_cast
  simp only [cast_card_erase_real, Finset.mem_erase, Finset.mem_range, Finset.card_range]
  norm_num [h0, h1, h2, h3, vD, aff]
  ring

/-! ### The uniform transfer is pattern-diagonal -/

/-- The canonical realisation of a proper column is one of the five patterns. -/
theorem canon_cases {s : T4} (hs : Proper s) :
    canon s = (0, 1, 0, 1) ∨ canon s = (0, 1, 0, 2) ∨ canon s = (0, 1, 2, 1) ∨
      canon s = (0, 1, 2, 0) ∨ canon s = (0, 1, 2, 3) := by
  obtain ⟨p1, p2, p3⟩ := hs
  unfold canon
  simp only [r1, r2, r3, r4] at *
  split_ifs <;> simp_all

theorem GU_eq_of_canon {k : ℕ} (w : Wt) {s c : T4} (h : canon s = c) (hc : canon c = c) :
    GU k w s = GU k w c := by
  unfold GU; rw [h, hc]

/-- The next weights of the uniform transfer, normalised by the `0101` row. -/
noncomputable def nextW (k : ℕ) (w : Wt) : Wt :=
  ⟨vB ((k : ℝ) - 2) w / vA ((k : ℝ) - 2) w, vC ((k : ℝ) - 2) w / vA ((k : ℝ) - 2) w,
    vD ((k : ℝ) - 2) w / vA ((k : ℝ) - 2) w⟩

/-- **The uniform transfer maps a pattern weight to a pattern weight**: the weighted number of
uniform successors of a proper column is `vA · gw (nextW k w)`. -/
theorem GU_eq {k : ℕ} (hk : 4 ≤ k) (w : Wt) (hA : vA ((k : ℝ) - 2) w ≠ 0) {s : T4}
    (hs : Proper s) : GU k w s = vA ((k : ℝ) - 2) w * gw (nextW k w) s := by
  rw [gw_congr _ (samePat_canon hs)]
  rcases canon_cases hs with h | h | h | h | h <;> rw [GU_eq_of_canon w h (by decide), h] <;>
    simp only [GU_0101 hk, GU_0102 hk, GU_0121 hk, GU_0120 hk, GU_0123 hk] <;>
    simp [gw, nextW, r1, r2, r3, r4, mul_div_cancel₀ _ hA]

/-! ### The invariant box -/

/-- Differences of affine functions are affine. -/
theorem aff_sub (p0 p1 p2 p3 q0 q1 q2 q3 : ℝ) (w : Wt) :
    aff p0 p1 p2 p3 w - aff q0 q1 q2 q3 w = aff (p0 - q0) (p1 - q1) (p2 - q2) (p3 - q3) w := by
  unfold aff; ring

theorem mul_aff (r p0 p1 p2 p3 : ℝ) (w : Wt) :
    r * aff p0 p1 p2 p3 w = aff (r * p0) (r * p1) (r * p2) (r * p3) w := by
  unfold aff; ring

/-- An affine function nonnegative at the eight corners of the box `[r, 1]³` is nonnegative on
it. -/
theorem aff_nonneg {r p0 p1 p2 p3 : ℝ} {w : Wt} (ha : r ≤ w.a) (ha' : w.a ≤ 1) (hb : r ≤ w.b)
    (hb' : w.b ≤ 1) (hc : r ≤ w.c) (hc' : w.c ≤ 1)
    (h : ∀ x y z : ℝ, (x = r ∨ x = 1) → (y = r ∨ y = 1) → (z = r ∨ z = 1) →
      0 ≤ aff p0 p1 p2 p3 ⟨x, y, z⟩) : 0 ≤ aff p0 p1 p2 p3 w := by
  have ea : p1 * r ≤ p1 * w.a ∨ p1 * 1 ≤ p1 * w.a := by
    rcases le_total 0 p1 with h1 | h1
    · left; exact mul_le_mul_of_nonneg_left ha h1
    · right; exact mul_le_mul_of_nonpos_left ha' h1
  have eb : p2 * r ≤ p2 * w.b ∨ p2 * 1 ≤ p2 * w.b := by
    rcases le_total 0 p2 with h1 | h1
    · left; exact mul_le_mul_of_nonneg_left hb h1
    · right; exact mul_le_mul_of_nonpos_left hb' h1
  have ec : p3 * r ≤ p3 * w.c ∨ p3 * 1 ≤ p3 * w.c := by
    rcases le_total 0 p3 with h1 | h1
    · left; exact mul_le_mul_of_nonneg_left hc h1
    · right; exact mul_le_mul_of_nonpos_left hc' h1
  unfold aff at h ⊢
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rcases ec with ec | ec
  · linarith [h r r r (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  · linarith [h r r 1 (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)]
  · linarith [h r 1 r (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)]
  · linarith [h r 1 1 (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)]
  · linarith [h 1 r r (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)]
  · linarith [h 1 r 1 (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)]
  · linarith [h 1 1 r (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)]
  · linarith [h 1 1 1 (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)]

theorem nonneg_of_scaled {x E : ℝ} (hx : 0 < x) (h : 0 ≤ x * E) : 0 ≤ E := by
  by_contra hE
  linarith [mul_neg_of_pos_of_neg hx (not_le.mp hE)]

/-- The box `[r, 1]³`. -/
def BoxR (r : ℝ) (w : Wt) : Prop := r ≤ w.a ∧ w.a ≤ 1 ∧ r ≤ w.b ∧ w.b ≤ 1 ∧ r ≤ w.c ∧ w.c ≤ 1

/-! The six corner certificates: for `ℓ = m + 3` (that is, `k ≥ 5`) and `r = 1 - 2/ℓ³`, at
every corner of the box, `r · vA ≤ vX ≤ vA` for `X = B, C, D`. After clearing `ℓ³` (resp. `ℓ⁶`)
each is a polynomial in `m` with nonnegative coefficients. -/

theorem vB_le_vA {m : ℕ} {r : ℝ} (hr : r = 1 - 2 / ((m : ℝ) + 3) ^ 3) {w : Wt} (h : BoxR r w) :
    vB ((m : ℝ) + 3) w ≤ vA ((m : ℝ) + 3) w := by
  have hl : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := h
  rw [← sub_nonneg, vA, vB, aff_sub]
  refine aff_nonneg ha ha' hb hb' hc hc' ?_
  rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) <;>
    (refine nonneg_of_scaled (pow_pos hl 3) ?_; simp only [aff]; subst hr; field_simp; ring_nf
     positivity)

theorem le_vB {m : ℕ} {r : ℝ} (hr : r = 1 - 2 / ((m : ℝ) + 3) ^ 3) {w : Wt} (h : BoxR r w) :
    r * vA ((m : ℝ) + 3) w ≤ vB ((m : ℝ) + 3) w := by
  have hl : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := h
  rw [← sub_nonneg, vA, vB, mul_aff, aff_sub]
  refine aff_nonneg ha ha' hb hb' hc hc' ?_
  rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) <;>
    (refine nonneg_of_scaled (pow_pos hl 6) ?_; simp only [aff]; subst hr; field_simp; ring_nf
     positivity)

theorem vC_le_vA {m : ℕ} {r : ℝ} (hr : r = 1 - 2 / ((m : ℝ) + 3) ^ 3) {w : Wt} (h : BoxR r w) :
    vC ((m : ℝ) + 3) w ≤ vA ((m : ℝ) + 3) w := by
  have hl : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := h
  rw [← sub_nonneg, vA, vC, aff_sub]
  refine aff_nonneg ha ha' hb hb' hc hc' ?_
  rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) <;>
    (refine nonneg_of_scaled (pow_pos hl 3) ?_; simp only [aff]; subst hr; field_simp; ring_nf
     positivity)

theorem le_vC {m : ℕ} {r : ℝ} (hr : r = 1 - 2 / ((m : ℝ) + 3) ^ 3) {w : Wt} (h : BoxR r w) :
    r * vA ((m : ℝ) + 3) w ≤ vC ((m : ℝ) + 3) w := by
  have hl : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := h
  rw [← sub_nonneg, vA, vC, mul_aff, aff_sub]
  refine aff_nonneg ha ha' hb hb' hc hc' ?_
  rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) <;>
    (refine nonneg_of_scaled (pow_pos hl 6) ?_; simp only [aff]; subst hr; field_simp; ring_nf
     positivity)

theorem vD_le_vA {m : ℕ} {r : ℝ} (hr : r = 1 - 2 / ((m : ℝ) + 3) ^ 3) {w : Wt} (h : BoxR r w) :
    vD ((m : ℝ) + 3) w ≤ vA ((m : ℝ) + 3) w := by
  have hl : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := h
  rw [← sub_nonneg, vA, vD, aff_sub]
  refine aff_nonneg ha ha' hb hb' hc hc' ?_
  rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) <;>
    (refine nonneg_of_scaled (pow_pos hl 3) ?_; simp only [aff]; subst hr; field_simp; ring_nf
     positivity)

theorem le_vD {m : ℕ} {r : ℝ} (hr : r = 1 - 2 / ((m : ℝ) + 3) ^ 3) {w : Wt} (h : BoxR r w) :
    r * vA ((m : ℝ) + 3) w ≤ vD ((m : ℝ) + 3) w := by
  have hl : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := h
  rw [← sub_nonneg, vA, vD, mul_aff, aff_sub]
  refine aff_nonneg ha ha' hb hb' hc hc' ?_
  rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) <;>
    (refine nonneg_of_scaled (pow_pos hl 6) ?_; simp only [aff]; subst hr; field_simp; ring_nf
     positivity)

theorem rho_pos {m : ℕ} {r : ℝ} (hr : r = 1 - 2 / ((m : ℝ) + 3) ^ 3) : 0 < r := by
  have hl : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  have h27 : (27 : ℝ) ≤ ((m : ℝ) + 3) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
      (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)] : (3 : ℝ) ≤ (m : ℝ) + 3) 3
    norm_num at this; linarith
  rw [hr, sub_pos, div_lt_one (by positivity)]
  linarith

theorem vA_pos {m : ℕ} {r : ℝ} (hr : r = 1 - 2 / ((m : ℝ) + 3) ^ 3) {w : Wt} (h : BoxR r w) :
    0 < vA ((m : ℝ) + 3) w := by
  have hr0 := rho_pos hr
  obtain ⟨ha, -, hb, -, hc, -⟩ := h
  have c1 : (0 : ℝ) ≤ 2 * ((m : ℝ) + 3) ^ 3 + 2 * ((m : ℝ) + 3) := by positivity
  have c2 : (0 : ℝ) ≤ ((m : ℝ) + 3) ^ 3 - ((m : ℝ) + 3) ^ 2 + ((m : ℝ) + 3) := by
    ring_nf; positivity
  have c3 : (0 : ℝ) ≤ ((m : ℝ) + 3) ^ 4 - 2 * ((m : ℝ) + 3) ^ 3 + 3 * ((m : ℝ) + 3) ^ 2
      - 2 * ((m : ℝ) + 3) := by
    ring_nf; positivity
  have c0 : (0 : ℝ) < ((m : ℝ) + 3) ^ 2 + ((m : ℝ) + 3) + 1 := by positivity
  unfold vA aff
  nlinarith [mul_nonneg c1 (hr0.le.trans ha), mul_nonneg c2 (hr0.le.trans hb),
    mul_nonneg c3 (hr0.le.trans hc)]

theorem rho_eq {m : ℕ} : rho (m + 5) = 1 - 2 / ((m : ℝ) + 3) ^ 3 := by
  unfold rho; push_cast; ring_nf

theorem cast_sub_two (m : ℕ) : (((m + 5 : ℕ) : ℝ) - 2) = (m : ℝ) + 3 := by
  push_cast; ring

/-- **Box invariance**: for `k ≥ 5` the uniform transfer maps the box `[ρ, 1]³` into itself. -/
theorem nextW_inBox {k : ℕ} (hk : 5 ≤ k) {w : Wt} (hw : InBox k w) : InBox k (nextW k w) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  have hb : BoxR (rho (m + 5)) w := hw
  have hpos := vA_pos rho_eq hb
  unfold InBox nextW
  simp only [cast_sub_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hpos]; exact le_vB rho_eq hb
  · rw [div_le_one hpos]; exact vB_le_vA rho_eq hb
  · rw [le_div_iff₀ hpos]; exact le_vC rho_eq hb
  · rw [div_le_one hpos]; exact vC_le_vA rho_eq hb
  · rw [le_div_iff₀ hpos]; exact le_vD rho_eq hb
  · rw [div_le_one hpos]; exact vD_le_vA rho_eq hb

/-- The `0101` row is positive on the box. -/
theorem vA_pos_of_inBox {k : ℕ} (hk : 5 ≤ k) {w : Wt} (hw : InBox k w) :
    0 < vA ((k : ℝ) - 2) w := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  rw [cast_sub_two]
  exact vA_pos rho_eq hw

theorem rho_le_one (k : ℕ) (hk : 5 ≤ k) : rho k ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  rw [rho_eq]
  have : (0 : ℝ) ≤ 2 / ((m : ℝ) + 3) ^ 3 := by positivity
  linarith

/-! ### The uniform futures -/

/-- The weighted uniform futures of a column: `Fu k (i+1) s` sums `Fu k i` over the uniform
successors of `s`. -/
noncomputable def Fu (k : ℕ) : ℕ → T4 → ℝ
  | 0 => fun _ => 1
  | i + 1 => fun s => ∑ t ∈ sts ((range k).erase (r1 s)) ((range k).erase (r2 s))
      ((range k).erase (r3 s)) ((range k).erase (r4 s)), Fu k i t

/-- The pattern weights of the uniform futures. -/
noncomputable def wseq (k : ℕ) : ℕ → Wt
  | 0 => ⟨1, 1, 1⟩
  | i + 1 => nextW k (wseq k i)

/-- The `0101` value of the uniform futures. -/
noncomputable def fseq (k : ℕ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => fseq k i * vA ((k : ℝ) - 2) (wseq k i)

theorem wseq_inBox {k : ℕ} (hk : 5 ≤ k) : ∀ i, InBox k (wseq k i)
  | 0 => by
      have := rho_le_one k hk
      exact ⟨this, le_rfl, this, le_rfl, this, le_rfl⟩
  | i + 1 => nextW_inBox hk (wseq_inBox hk i)

theorem fseq_pos {k : ℕ} (hk : 5 ≤ k) : ∀ i, 0 < fseq k i
  | 0 => one_pos
  | i + 1 => mul_pos (fseq_pos hk i) (vA_pos_of_inBox hk (wseq_inBox hk i))

theorem rowsIn_of_mem_sts_erase {k : ℕ} {s t : T4}
    (ht : t ∈ sts ((range k).erase (r1 s)) ((range k).erase (r2 s)) ((range k).erase (r3 s))
      ((range k).erase (r4 s))) : RowsIn t (range k) := by
  rw [mem_sts] at ht
  exact ⟨Finset.mem_of_mem_erase ht.1, Finset.mem_of_mem_erase ht.2.1,
    Finset.mem_of_mem_erase ht.2.2.1, Finset.mem_of_mem_erase ht.2.2.2.1⟩

/-- **The uniform futures by pattern**: on proper uniform columns, `Fu k i = fseq k i · gw (wseq k i)`,
with `wseq k i` in the box and `fseq k i > 0`. -/
theorem Fu_eq {k : ℕ} (hk : 5 ≤ k) :
    ∀ i (s : T4), Proper s → RowsIn s (range k) → Fu k i s = fseq k i * gw (wseq k i) s
  | 0, s, _, _ => by simp [Fu, fseq, wseq, gw_one]
  | i + 1, s, hs, hP => by
      have hA := (vA_pos_of_inBox hk (wseq_inBox hk i)).ne'
      have hsum : Fu k (i + 1) s = fseq k i * GU k (wseq k i) s := by
        simp only [Fu]
        rw [Finset.sum_congr rfl (fun t ht => Fu_eq hk i t (proper_of_mem_sts ht)
          (rowsIn_of_mem_sts_erase ht)), ← Finset.mul_sum,
          ← G_erase_eq_GU (wseq k i) (by omega) hs (card_range k) hP]
        rfl
      rw [hsum, GU_eq (by omega) _ hA hs]
      simp only [fseq, wseq]
      ring

/-- One step of the uniform futures, as the uniform successor count `GU`. -/
theorem Fu_succ_eq {k : ℕ} (hk : 5 ≤ k) (i : ℕ) {s : T4} (hs : Proper s)
    (hP : RowsIn s (range k)) : Fu k (i + 1) s = fseq k i * GU k (wseq k i) s := by
  rw [Fu_eq hk (i + 1) s hs hP, GU_eq (by omega) _
    (vA_pos_of_inBox hk (wseq_inBox hk i)).ne' hs]
  simp only [fseq, wseq]
  ring

end GridGen.Four
