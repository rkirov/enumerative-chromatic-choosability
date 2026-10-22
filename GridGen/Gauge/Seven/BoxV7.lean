/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Eight.Seam8

/-!
# The vertical box and the relaxation step at `k = 7`

The `k = 7` version of `Eight/BoxV.lean`. The box, its upper and lower bounds and the neighbour
counts there are generic in `k`; only the ratios change. In the relaxed slab at `k = 7`, at least a
`γ_V = 27/5075` fraction of the solutions puts a relaxed label `ℓ` on both cells of its vertical
edge (`boxV_bound_seven`).

* `μ, δ` (the first-future-column cells above and below the centre pair) have at least `4`
  available labels, so their ratio is at most `4/3` (`ratio_U7`, `ratio_D7`).
* The list domino's available sets have at least `5` colours each and one colour per row is
  keyed `ℓ`. The diagonal pairs excluded with `ℓ` number at most the overlap `i ≤ 5` of the rows
  and at most the size of either row after dropping its `ℓ`-keyed colour, so the ratio is at most
  `(25 - 4)/(16 - 4) = 7/4` (`ratio_L7`). (The overlap bound alone gives `20/11`.)
* The future domino's ratio is `13/12, 16/12` or `20/12` as `a, b` are available at `ρ₁, ρ₂` or
  not (`ratio_R7`). At most two labels are unavailable at each, so the sum over the `49` centre
  values is at most `25 · 13 + 20 · 16 + 4 · 20 = 725` twelfths (`sum_gR7`).

Hence `1/γ_V = (4/3)² · (7/4) · 725/12 = 5075/27`. The relaxation steps `relax_step7` and
`relax_all7` follow as at `k = 8` (`Eight/Seam8.lean`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ} {N : Fin m → ℕ → ℕ} {R : Fin m → Finset ℕ}

/-! ### The ratios at `k = 7` -/

section Seven

variable (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) {g : Cell c m → ℕ}
  (hg : (slabR c m 7 P A N R).Valid g) (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m)
include hK hg

theorem ratio_U7 (ℓ : ℕ) :
    3 * (optUv c 7 P A N R hc v g).card ≤ 4 * (optUv' c 7 P A N R hc v ℓ g).card := by
  unfold optUv optUv'
  split_ifs with h
  · rw [card_map, card_map]
    have hav := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (uC_inYV hc h).1
      (show 2 ≤ (uC hc h).1.val from le_rfl)
    have hn := nbrsOut_uC (k := 7) (P := P) (A := A) (N := N) (R := R) hc h
    have := pred_card_le_card_erase (s := (slabR c m 7 P A N R).avail (boxBV c v) g (uC hc h))
      (a := ℓ)
    omega
  · simp

theorem ratio_D7 (ℓ : ℕ) :
    3 * (optDv c 7 P A N R hc v g).card ≤ 4 * (optDv' c 7 P A N R hc v ℓ g).card := by
  unfold optDv optDv'
  split_ifs with h
  · rw [card_map, card_map]
    have hav := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (dC_inYV hc h).1
      (show 2 ≤ (dC hc h).1.val from le_rfl)
    have hn := nbrsOut_dC (k := 7) (P := P) (A := A) (N := N) (R := R) hc h
    have := pred_card_le_card_erase (s := (slabR c m 7 P A N R).avail (boxBV c v) g (dC hc h))
      (a := ℓ)
    omega
  · simp

omit hK hg in
/-- The list domino's arithmetic at `k = 7`: rows of `5 + p` and `5 + q` colours, at most one
dropped from each, and at most `min (i, b₁, b₂)` diagonal pairs excluded on the right. -/
theorem L_arith7 {p q i j E E' O b₁ b₂ : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (e1 : E + i = (5 + p) * (5 + q)) (e2 : E' + j = b₁ * b₂)
    (hb₁ : b₁ = 4 + p ∨ b₁ = 5 + p) (hb₂ : b₂ = 4 + q ∨ b₂ = 5 + q)
    (hj : j ≤ i) (hj₁ : j ≤ b₁) (hj₂ : j ≤ b₂) (hO : O ≤ E) : 4 * O ≤ 7 * E' := by
  have hpq := mul_nonneg hp hq
  rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;> linarith

include hA in
theorem ratio_L7 {ℓ : ℕ} (hℓ : ℓ < 7) (a b : ℕ) :
    4 * (optLv c 7 P A N R hv g a b).card ≤ 7 * (optLv c 7 P A N R hv g ℓ ℓ).card := by
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  have hα1 : 5 ≤ ((slabR c m 7 P A N R).avail (boxBV c v) g (lA v)).card := by
    have := avail_list_ge (P := P) (A := A) (N := N) (R := R) hK hg hA (lA_inYV v).1 h1v
    have := nbrsOut_lA (k := 7) (P := P) (A := A) (N := N) (R := R) (c := c) v
    omega
  have hα2 : 5 ≤ ((slabR c m 7 P A N R).avail (boxBV c v) g (lB hv)).card := by
    have := avail_list_ge (P := P) (A := A) (N := N) (R := R) hK hg hA (lB_inYV hv).1 h1v
    have := nbrsOut_lB (k := 7) (P := P) (A := A) (N := N) (R := R) (c := c) hv
    omega
  set C := slabR c m 7 P A N R
  set A1 := C.avail (boxBV c v) g (lA v)
  set A2 := C.avail (boxBV c v) g (lB hv)
  -- at most one colour of a row is keyed `ℓ`
  have hkey : ∀ (X : Finset ℕ) (w : Fin m), X ⊆ A w →
      X.card ≤ (X.filter (fun p => N w p ≠ ℓ)).card + 1 := by
    intro X w hX
    have hle : (X.filter (fun p => ¬ N w p ≠ ℓ)).card ≤ 1 := by
      refine card_le_one.mpr fun p hp p' hp' => ?_
      rw [mem_filter, not_not] at hp hp'
      exact hK w p p' (hX hp.1) (hX hp'.1) (hp.2.trans hp'.2.symm) (by rw [hp.2]; exact hℓ)
    have := card_filter_add_card_filter_not (s := X) (fun p => N w p ≠ ℓ)
    omega
  have hA1 : A1 ⊆ A v := fun p hp => by
    have := (C.mem_avail.mp hp).1; rwa [slabR_D, slab_D_one h1v] at this
  have hA2 : A2 ⊆ A ⟨v.val + 1, hv⟩ := fun p hp => by
    have := (C.mem_avail.mp hp).1; rwa [slabR_D, slab_D_one h1v] at this
  have hb1 := hkey A1 v hA1
  have hb2 := hkey A2 ⟨v.val + 1, hv⟩ hA2
  set B1 := A1.filter (fun p => N v p ≠ ℓ)
  set B2 := A2.filter (fun p => N ⟨v.val + 1, hv⟩ p ≠ ℓ)
  have hup : (optLv c 7 P A N R hv g a b).card ≤ (offd A1 A2).card :=
    card_le_card (offd_mono (filter_subset _ _) (filter_subset _ _))
  have e1 := card_offd A1 A2
  have e2 := card_offd B1 B2
  have hi : (B1 ∩ B2).card ≤ (A1 ∩ A2).card :=
    card_le_card (inter_subset_inter (filter_subset _ _) (filter_subset _ _))
  have hB1 : B1.card ≤ A1.card := card_le_card (filter_subset _ _)
  have hB2 : B2.card ≤ A2.card := card_le_card (filter_subset _ _)
  -- the pairs excluded on the right are diagonal, so at most `min |B₁| |B₂|` of them
  have hj1 : (B1 ∩ B2).card ≤ B1.card := card_le_card inter_subset_left
  have hj2 : (B1 ∩ B2).card ≤ B2.card := card_le_card inter_subset_right
  change 4 * (optLv c 7 P A N R hv g a b).card ≤ 7 * (offd B1 B2).card
  obtain ⟨p, hp⟩ : ∃ p, A1.card = 5 + p := ⟨A1.card - 5, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, A2.card = 5 + q := ⟨A2.card - 5, by omega⟩
  rw [hp, hq] at e1
  have hc1 : B1.card = 4 + p ∨ B1.card = 5 + p := by omega
  have hc2 : B2.card = 4 + q ∨ B2.card = 5 + q := by omega
  have key := L_arith7 (p := p) (q := q) (i := (A1 ∩ A2).card) (j := (B1 ∩ B2).card)
    (E := (offd A1 A2).card) (E' := (offd B1 B2).card) (O := (optLv c 7 P A N R hv g a b).card)
    (b₁ := B1.card) (b₂ := B2.card) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast e1) (by exact_mod_cast e2)
    (hc1.imp (fun h => by rw [h]; push_cast; ring) (fun h => by rw [h]; push_cast; ring))
    (hc2.imp (fun h => by rw [h]; push_cast; ring) (fun h => by rw [h]; push_cast; ring))
    (by exact_mod_cast hi) (by exact_mod_cast hj1) (by exact_mod_cast hj2) (by exact_mod_cast hup)
  exact_mod_cast key

/-- The future domino's ratio numerator at `k = 7`: `13`, `16` or `20` by availability of the
centre values. -/
noncomputable def gR7 (hv : v.val + 1 < m) (g : Cell c m → ℕ) (a b : ℕ) : ℕ :=
  if h : 2 ≤ c then
    13 + 3 * (if a ∈ (slabR c m 7 P A N R).avail (boxBV c v) g (rA h v) then 0 else 1) +
      3 * (if b ∈ (slabR c m 7 P A N R).avail (boxBV c v) g (rB hv h) then 0 else 1) +
        (if a ∈ (slabR c m 7 P A N R).avail (boxBV c v) g (rA h v) then 0 else 1) *
          (if b ∈ (slabR c m 7 P A N R).avail (boxBV c v) g (rB hv h) then 0 else 1)
  else 13

omit hK hg in
/-- The future domino's arithmetic at `k = 7`. -/
theorem R_arith7 {α₁ α₂ i E I E' I' x y x' y' : ℤ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (hx' : x' = 0 ∨ x' = 1) (hy' : y' = 0 ∨ y' = 1) (h1 : E + I = (α₁ - x) * (α₂ - y))
    (h2 : i ≤ I + x + y) (h3 : E' + I' = (α₁ - x') * (α₂ - y')) (h4 : I' + x' * y' = i)
    (hα₁ : 5 ≤ α₁) (hα₂ : 5 ≤ α₂) (hi₁ : i ≤ α₁) :
    12 * E ≤ (13 + 3 * (1 - x) + 3 * (1 - y) + (1 - x) * (1 - y)) * E' := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hx' with rfl | rfl <;>
    rcases hy' with rfl | rfl <;> nlinarith

set_option maxHeartbeats 800000 in
theorem ratio_R7 (ℓ a b : ℕ) :
    12 * (optRv c 7 P A N R hv g a b).card ≤
      gR7 (P := P) (A := A) (N := N) (R := R) hv g a b * (optRv c 7 P A N R hv g ℓ ℓ).card := by
  unfold optRv gR7
  by_cases h : 2 ≤ c
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left h, card_map, card_map]
    have hα1 : 5 ≤ ((slabR c m 7 P A N R).avail (boxBV c v) g (rA h v)).card := by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rA_inYV h v).1
        (show 2 ≤ (rA (c := c) h v).1.val by simp [rA])
      have := nbrsOut_rA (k := 7) (P := P) (A := A) (N := N) (R := R) h v
      omega
    have hα2 : 5 ≤ ((slabR c m 7 P A N R).avail (boxBV c v) g (rB hv h)).card := by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rB_inYV h hv).1
        (show 2 ≤ (rB (c := c) hv h).1.val by simp [rB])
      have := nbrsOut_rB (k := 7) (P := P) (A := A) (N := N) (R := R) h hv
      omega
    set A1 := (slabR c m 7 P A N R).avail (boxBV c v) g (rA h v)
    set A2 := (slabR c m 7 P A N R).avail (boxBV c v) g (rB hv h)
    have ea := card_erase_ind A1 a
    have eb := card_erase_ind A2 b
    have ea' := card_erase_ind A1 ℓ
    have eb' := card_erase_ind A2 ℓ
    have e1 := card_offd (A1.erase a) (A2.erase b)
    have e2 := card_offd (A1.erase ℓ) (A2.erase ℓ)
    have hS := erase_inter_erase A1 A2 a b
    have hS' : (A1.erase ℓ) ∩ (A2.erase ℓ) = (A1 ∩ A2).erase ℓ := by
      rw [erase_inter_erase, erase_eq_of_notMem (notMem_erase ℓ _)]
    have f1 := card_erase_ind (A1 ∩ A2) a
    have f2 := card_erase_ind ((A1 ∩ A2).erase a) b
    have f3 := card_erase_ind (A1 ∩ A2) ℓ
    have g1 : (if a ∈ A1 ∩ A2 then 1 else 0) ≤ (if a ∈ A1 then 1 else 0) :=
      ind_le_of_imp fun h => (mem_inter.mp h).1
    have g2 : (if b ∈ (A1 ∩ A2).erase a then 1 else 0) ≤ (if b ∈ A2 then 1 else 0) :=
      ind_le_of_imp fun h => (mem_inter.mp (mem_of_mem_erase h)).2
    have g3 := ind_inter A1 A2 ℓ
    have hiA1 : (A1 ∩ A2).card ≤ A1.card := card_le_card inter_subset_left
    have hiA2 : (A1 ∩ A2).card ≤ A2.card := card_le_card inter_subset_right
    rw [hS] at e1
    rw [hS'] at e2
    have b01 : ∀ (P : Prop) [Decidable P], ((if P then 1 else 0 : ℕ) : ℤ) = 0 ∨
        ((if P then 1 else 0 : ℕ) : ℤ) = 1 := by
      intro P _; split_ifs <;> simp
    have h2n : (A1 ∩ A2).card ≤ (((A1 ∩ A2).erase a).erase b).card + (if a ∈ A1 then 1 else 0) +
        (if b ∈ A2 then 1 else 0) := by omega
    have key := R_arith7 (α₁ := A1.card) (α₂ := A2.card) (i := (A1 ∩ A2).card)
      (E := (offd (A1.erase a) (A2.erase b)).card) (I := (((A1 ∩ A2).erase a).erase b).card)
      (E' := (offd (A1.erase ℓ) (A2.erase ℓ)).card) (I' := ((A1 ∩ A2).erase ℓ).card)
      (x := (if a ∈ A1 then 1 else 0 : ℕ)) (y := (if b ∈ A2 then 1 else 0 : ℕ))
      (x' := (if ℓ ∈ A1 then 1 else 0 : ℕ)) (y' := (if ℓ ∈ A2 then 1 else 0 : ℕ))
      (b01 _) (b01 _) (b01 _) (b01 _)
      (by push_cast [← ea, ← eb] at e1 ⊢; linarith)
      (by exact_mod_cast h2n)
      (by push_cast [← ea', ← eb'] at e2 ⊢; linarith)
      (by rw [← f3, g3]; push_cast; ring)
      (by exact_mod_cast hα1) (by exact_mod_cast hα2) (by exact_mod_cast hiA1)
    have hgr : ((13 + 3 * (if a ∈ A1 then 0 else 1) + 3 * (if b ∈ A2 then 0 else 1) +
        (if a ∈ A1 then 0 else 1) * (if b ∈ A2 then 0 else 1) : ℕ) : ℤ) =
        13 + 3 * (1 - ((if a ∈ A1 then 1 else 0 : ℕ) : ℤ)) +
          3 * (1 - ((if b ∈ A2 then 1 else 0 : ℕ) : ℤ)) +
            (1 - ((if a ∈ A1 then 1 else 0 : ℕ) : ℤ)) * (1 - ((if b ∈ A2 then 1 else 0 : ℕ) : ℤ)) := by
      by_cases h1 : a ∈ A1 <;> by_cases h2 : b ∈ A2 <;> simp [h1, h2]
    have : (12 * (offd (A1.erase a) (A2.erase b)).card : ℤ) ≤
        ((13 + 3 * (if a ∈ A1 then 0 else 1) + 3 * (if b ∈ A2 then 0 else 1) +
          (if a ∈ A1 then 0 else 1) * (if b ∈ A2 then 0 else 1) : ℕ) : ℤ) *
            (offd (A1.erase ℓ) (A2.erase ℓ)).card := by rw [hgr]; exact key
    exact Int.ofNat_le.mp (by rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]; exact this)
  · rw [dite_eq_right h, dite_eq_right h, dite_eq_right h]; simp

omit hK hg in
/-- At most two labels are unavailable at a future cell of the domino (`k = 7`). -/
theorem sum_ind_le7 {X : Finset ℕ} (hX : X ⊆ range 7) (h5 : 5 ≤ X.card) :
    ∑ a ∈ range 7, (if a ∈ X then 0 else 1 : ℕ) ≤ 2 := by
  rw [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one]
  have e : (range 7).filter (fun a => ¬ a ∈ X) = range 7 \ X := by ext a; simp [mem_sdiff]
  rw [e, card_sdiff_of_subset hX, card_range]
  omega

theorem sum_gR7 : ∑ a ∈ range 7, ∑ b ∈ range 7,
    gR7 (P := P) (A := A) (N := N) (R := R) hv g a b ≤ 725 := by
  unfold gR7
  by_cases h : 2 ≤ c
  · simp only [dite_eq_left h]
    set A1 := (slabR c m 7 P A N R).avail (boxBV c v) g (rA h v)
    set A2 := (slabR c m 7 P A N R).avail (boxBV c v) g (rB hv h)
    have hsub : ∀ y : Cell c m, 2 ≤ y.1.val → (slabR c m 7 P A N R).avail (boxBV c v) g y ⊆
        range 7 := fun y hy z hz => by
      have := ((slabR c m 7 P A N R).mem_avail.mp hz).1; rwa [slabR_D, slab_D_fut hy] at this
    have h1 := sum_ind_le7 (hsub (rA h v) (show 2 ≤ 3 by omega)) (by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rA_inYV h v).1
        (show 2 ≤ (rA (c := c) h v).1.val by simp [rA])
      have := nbrsOut_rA (k := 7) (P := P) (A := A) (N := N) (R := R) h v
      omega)
    have h2 := sum_ind_le7 (hsub (rB hv h) (show 2 ≤ 3 by omega)) (by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rB_inYV h hv).1
        (show 2 ≤ (rB (c := c) hv h).1.val by simp [rB])
      have := nbrsOut_rB (k := 7) (P := P) (A := A) (N := N) (R := R) h hv
      omega)
    set I := fun a => (if a ∈ A1 then 0 else 1 : ℕ)
    set J := fun b => (if b ∈ A2 then 0 else 1 : ℕ)
    have e : ∀ a, ∑ b ∈ range 7, (13 + 3 * I a + 3 * J b + I a * J b) =
        91 + 21 * I a + 3 * (∑ b ∈ range 7, J b) + I a * ∑ b ∈ range 7, J b := by
      intro a
      simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum]; ring
    calc ∑ a ∈ range 7, ∑ b ∈ range 7, (13 + 3 * I a + 3 * J b + I a * J b)
        = ∑ a ∈ range 7, (91 + 21 * I a + 3 * (∑ b ∈ range 7, J b) +
            I a * ∑ b ∈ range 7, J b) := sum_congr rfl fun a _ => e a
      _ = 637 + 21 * (∑ a ∈ range 7, I a) + 21 * (∑ b ∈ range 7, J b) +
            (∑ a ∈ range 7, I a) * (∑ b ∈ range 7, J b) := by
          simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum, ← sum_mul]
          ring
      _ ≤ 725 := by
          have h1' : ∑ a ∈ range 7, I a ≤ 2 := h1
          have h2' : ∑ b ∈ range 7, J b ≤ 2 := h2
          have := Nat.mul_le_mul h1' h2'
          omega
  · simp only [dite_eq_right h, sum_const, card_range, smul_eq_mul]; norm_num

set_option maxHeartbeats 1000000 in
/-- **The vertical box inequality on one fibre** (`k = 7`). -/
theorem box_fibreV7 (hA : ∀ v, (A v).card = 7) {ℓ : ℕ} (hℓ : ℓ < 7) (hR : ℓ ∈ R v) :
    (((slabR c m 7 P A N R).cls (boxBV c v) g).card : ℚ) * 27 ≤
      ((((slabR c m 7 P A N R).cls (boxBV c v) g).filter (HitV hc hv ℓ)).card : ℚ) * 5075 := by
  set U' := (optUv' c 7 P A N R hc v ℓ g).card
  set D' := (optDv' c 7 P A N R hc v ℓ g).card
  set L' := (optLv c 7 P A N R hv g ℓ ℓ).card
  set R' := (optRv c 7 P A N R hv g ℓ ℓ).card
  have hup := card_cls_le_sumV (k := 7) (P := P) (A := A) (N := N) (R := R) hc hv g
  have hlo := card_hit_geV (P := P) (A := A) (N := N) (R := R) (hc := hc) (hv := hv) hg hℓ hR
  have hU := ratio_U7 (P := P) hK hg hc (v := v) ℓ
  have hD := ratio_D7 (P := P) hK hg hc (v := v) ℓ
  have hsum := sum_gR7 (P := P) (A := A) (N := N) (R := R) hK hg (c := c) hv
  have hterm : ∀ a b : ℕ, ((optUv c 7 P A N R hc v g).card : ℚ) * (optDv c 7 P A N R hc v g).card *
      (optLv c 7 P A N R hv g a b).card * (optRv c 7 P A N R hv g a b).card ≤
        (4 / 3 * U') * (4 / 3 * D') * (7 / 4 * L') *
          ((gR7 (P := P) (A := A) (N := N) (R := R) hv g a b : ℚ) / 12 * R') := by
    intro a b
    have h1 : ((optUv c 7 P A N R hc v g).card : ℚ) ≤ 4 / 3 * U' := by
      have := (Nat.cast_le (α := ℚ)).mpr hU; push_cast at this; linarith
    have h2 : ((optDv c 7 P A N R hc v g).card : ℚ) ≤ 4 / 3 * D' := by
      have := (Nat.cast_le (α := ℚ)).mpr hD; push_cast at this; linarith
    have h3 : ((optLv c 7 P A N R hv g a b).card : ℚ) ≤ 7 / 4 * L' := by
      have := (Nat.cast_le (α := ℚ)).mpr (ratio_L7 (P := P) hK hA hg hv hℓ a b)
      push_cast at this; linarith
    have h4 : ((optRv c 7 P A N R hv g a b).card : ℚ) ≤
        (gR7 (P := P) (A := A) (N := N) (R := R) hv g a b : ℚ) / 12 * R' := by
      have := (Nat.cast_le (α := ℚ)).mpr (ratio_R7 (P := P) hK hg hv ℓ a b)
      push_cast at this
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
    have p1 : (0 : ℚ) ≤ (optUv c 7 P A N R hc v g).card := Nat.cast_nonneg _
    have p2 : (0 : ℚ) ≤ (optDv c 7 P A N R hc v g).card := Nat.cast_nonneg _
    have p3 : (0 : ℚ) ≤ (optLv c 7 P A N R hv g a b).card := Nat.cast_nonneg _
    have p4 : (0 : ℚ) ≤ (optRv c 7 P A N R hv g a b).card := Nat.cast_nonneg _
    have q1 : (0 : ℚ) ≤ 4 / 3 * U' := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have q2 : (0 : ℚ) ≤ 4 / 3 * D' := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have q3 : (0 : ℚ) ≤ 7 / 4 * L' := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 p2 q1) h3 p3 (mul_nonneg q1 q2)) h4 p4
      (mul_nonneg (mul_nonneg q1 q2) q3)
  have hcls : (((slabR c m 7 P A N R).cls (boxBV c v) g).card : ℚ) ≤
      ∑ a ∈ range 7, ∑ b ∈ range 7, (4 / 3 * U') * (4 / 3 * D') * (7 / 4 * L') *
        ((gR7 (P := P) (A := A) (N := N) (R := R) hv g a b : ℚ) / 12 * R') := by
    have := (Nat.cast_le (α := ℚ)).mpr hup
    push_cast at this
    exact le_trans this (sum_le_sum fun a _ => sum_le_sum fun b _ => hterm a b)
  have heq : ∑ a ∈ range 7, ∑ b ∈ range 7, (4 / 3 * (U' : ℚ)) * (4 / 3 * D') * (7 / 4 * L') *
      ((gR7 (P := P) (A := A) (N := N) (R := R) hv g a b : ℚ) / 12 * R') =
        (16 / 9 * (7 / 4) / 12) * (U' * D' * L' * R') *
          ((∑ a ∈ range 7, ∑ b ∈ range 7,
            gR7 (P := P) (A := A) (N := N) (R := R) hv g a b : ℕ) : ℚ) := by
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    ring
  have hsumq : ((∑ a ∈ range 7, ∑ b ∈ range 7,
      gR7 (P := P) (A := A) (N := N) (R := R) hv g a b : ℕ) : ℚ) ≤ 725 := by
    exact_mod_cast hsum
  have hloq : (U' : ℚ) * D' * L' * R' ≤
      ((((slabR c m 7 P A N R).cls (boxBV c v) g).filter (HitV hc hv ℓ)).card : ℚ) := by
    exact_mod_cast hlo
  have hpos : (0 : ℚ) ≤ U' * D' * L' * R' :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  rw [heq] at hcls
  nlinarith

omit hg in
/-- **The vertical box bound** (`k = 7`): at least a `27/5075` fraction of the relaxed-slab
solutions put the relaxed label `ℓ` on both cells of its edge. -/
theorem boxV_bound_seven (hA : ∀ v, (A v).card = 7) {ℓ : ℕ} (hℓ : ℓ < 7) (hR : ℓ ∈ R v) :
    (slabR c m 7 P A N R).Ω.card * 27 ≤
      ((slabR c m 7 P A N R).Ω.filter (HitV hc hv ℓ)).card * 5075 :=
  (slabR c m 7 P A N R).fibre_sum_ge (boxBV c v) _ _ _ fun _ hg' => by
    have := box_fibreV7 hK ((CSP.mem_Ω _).mp hg') hc hv hA hℓ hR
    exact_mod_cast this

end Seven

/-! ### The relaxation step at `k = 7` -/

/-- The relaxation gain at `k = 7`. -/
def gammaV7 : ℚ := 27 / 5075

/-- **A relaxation step at `k = 7`.** -/
theorem relax_step7 (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 7) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj 7 A M) {R : Fin m → Finset ℕ} {v : Fin m} (hv : v.val + 1 < m) {ℓ : ℕ}
    (hℓ : ℓ < 7) (hn : ℓ ∉ R v) :
    ((slabR c m 7 P A M R).Ω.card : ℚ) ≤
      (1 - gammaV7) * (slabR c m 7 P A M (Radd R v ℓ)).Ω.card := by
  have hsplit := card_relax (k := 7) (P := P) (A := A) (M := M) hc hv hn
  have hmem : ℓ ∈ Radd R v ℓ v := by simp [Radd]
  have hbox := boxV_bound_seven (P := P) hK hc hv hA hℓ hmem
  have hq := (Nat.cast_le (α := ℚ)).mpr hbox
  push_cast at hq
  have hsplit' : ((slabR c m 7 P A M (Radd R v ℓ)).Ω.card : ℚ) = (slabR c m 7 P A M R).Ω.card +
      ((slabR c m 7 P A M (Radd R v ℓ)).Ω.filter (HitV hc hv ℓ)).card := by exact_mod_cast hsplit
  unfold gammaV7
  linarith

/-- **Relaxing a set of pairs** (`k = 7`). -/
theorem relax_all7 (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 7) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj 7 A M) : ∀ T : Finset (Fin m × ℕ), (∀ p ∈ T, p.1.val + 1 < m ∧ p.2 < 7) →
      ((slabR c m 7 P A M (fun _ => ∅)).Ω.card : ℚ) ≤
        (1 - gammaV7) ^ T.card * (slabR c m 7 P A M (RT T)).Ω.card := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _
      have e : RT (∅ : Finset (Fin m × ℕ)) = fun _ => ∅ := by
        funext v; ext ℓ; simp [mem_RT]
      rw [e, card_empty, pow_zero, one_mul]
  | insert p T hp ih =>
      intro hT
      have h1 := ih (fun q hq => hT q (mem_insert_of_mem hq))
      obtain ⟨hv, hℓ⟩ := hT p (mem_insert_self p T)
      have hn : p.2 ∉ RT T p.1 := by rw [mem_RT]; exact hp
      have e : RT (insert p T) = Radd (RT T) p.1 p.2 := by
        funext v
        ext ℓ
        rw [mem_RT, mem_insert]
        simp only [Radd]
        by_cases hv' : v = p.1
        · subst hv'
          rw [ite_eq_left rfl, mem_insert, mem_RT]
          constructor
          · rintro (h | h)
            · exact Or.inl (congrArg Prod.snd h)
            · exact Or.inr h
          · rintro (h | h)
            · exact Or.inl (Prod.ext rfl h)
            · exact Or.inr h
        · rw [ite_eq_right hv', mem_RT]
          constructor
          · rintro (h | h)
            · exact absurd (congrArg Prod.fst h) hv'
            · exact h
          · exact Or.inr
      have h2 := relax_step7 (P := P) hc hA hK (R := RT T) hv hℓ hn
      rw [← e] at h2
      have hγ : 0 ≤ 1 - gammaV7 := by unfold gammaV7; norm_num
      rw [card_insert_of_notMem hp, pow_succ]
      calc ((slabR c m 7 P A M (fun _ => ∅)).Ω.card : ℚ)
          ≤ (1 - gammaV7) ^ T.card * (slabR c m 7 P A M (RT T)).Ω.card := h1
        _ ≤ (1 - gammaV7) ^ T.card *
              ((1 - gammaV7) * (slabR c m 7 P A M (RT (insert p T))).Ω.card) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg hγ _)
        _ = _ := by ring

end GridGen.Gauge
