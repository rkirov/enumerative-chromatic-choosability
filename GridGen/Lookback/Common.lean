/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The column-lookback route: helpers shared by every height

The height-four (`GridGen/Four/`) and height-five (`GridGen/Five/`) seam arguments compare a
column `s` against the next lists `B₁, …, Bᵣ` of `k` colours through the punctured lists
`Aᵢ = Bᵢ.erase sᵢ`. Everything in this file is about one list, one pair of consecutive lists or
one row, so it serves every height unchanged:

* **Counting** (`card_prepend`, `card_pairAvoid`, `card_star`, …): colourings of a row placed in
  front of a tail, avoiding one or two colours of the tail.
* **The local data of a pair of consecutive lists**: the bonus `hb B c` (`1` when `c ∉ B`), the
  mismatch `mu k B C = k − |B ∩ C|`, the difference-set bits `zz B C a b`, and the size of a
  consecutive intersection of punctured lists (`card_inter_erase`,
  `|Aⱼ₋₁ ∩ Aⱼ| = k − μⱼ − 2 + hⱼ₋₁ + hⱼ + zⱼ`).
* **The rate of one row** (`rate_first`, `rate_main`, `rate_main_chord`): the log of a row's rate
  on punctured lists against its uniform value, with the state colours in the difference sets
  costing `zslope n μ` each.
* **The sharp fibre bound** (`fibre_row_sharp`): a property pinning one row to a function of the
  others carries at most a `R/(R + m − 1)` share of any weight whose values are within the
  factor `R`, for a row with `m` admissible values.

These were proved for height four and moved here unchanged on 2026-10-25 when height five reused
them.
-/

namespace GridGen.Lookback

open Finset Real

/-! ### Counting -/

/-- The card of a filtered product, as a sum over the first factor. -/
theorem card_filter_prod {α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset α)
    (C : Finset β) (P : α → Prop) [DecidablePred P] (Q : α → β → Prop) [∀ a b, Decidable (Q a b)] :
    ((S ×ˢ C).filter (fun x => P x.1 ∧ Q x.1 x.2)).card =
      ∑ a ∈ S.filter P, (C.filter (Q a)).card := by
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_filter]
  by_cases hP : P a
  · simp only [hP, true_and, ite_true]
  · simp only [hP, false_and, ite_false, Finset.sum_const_zero]

/-- Prepending a row: `#{(x, rest) : x ∈ A, x ≠ first rest} = |A|·#rest − #{rest : first ∈ A}`. -/
theorem card_prepend {β : Type*} [DecidableEq β] (A : Finset ℕ) (R : Finset β) (f : β → ℕ) :
    (((A ×ˢ R).filter (fun p => p.1 ≠ f p.2)).card : ℤ) =
      A.card * R.card - (R.filter (fun r => f r ∈ A)).card := by
  have h := card_filter_prod A R (fun _ => True) (fun a r => a ≠ f r)
  simp only [true_and, Finset.filter_true] at h
  rw [h]
  have hswap : ∑ a ∈ A, (R.filter (fun r => a ≠ f r)).card =
      ∑ r ∈ R, (A.filter (fun a => a ≠ f r)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hterm : ∀ r ∈ R, ((A.filter (fun a => a ≠ f r)).card : ℤ) = A.card - if f r ∈ A then 1 else 0 := by
    intro r _
    rw [Finset.filter_ne' A (f r)]
    split_ifs with h
    · rw [Finset.card_erase_of_mem h]; push_cast [Nat.cast_sub (Finset.card_pos.mpr ⟨_, h⟩)]; ring
    · rw [Finset.erase_eq_of_notMem h]; ring
  push_cast
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_filter]
  push_cast
  ring

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

/-- The image of a punctured palette under a map injective on the palette. -/
theorem image_erase_of_injOn {g : ℕ → ℕ} {P : Finset ℕ} (hg : Set.InjOn g ↑P) {x : ℕ}
    (hx : x ∈ P) : (P.erase x).image g = (P.image g).erase (g x) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨z, ⟨hzx, hz⟩, rfl⟩
    exact ⟨fun h => hzx (hg hz hx h), z, hz, rfl⟩
  · rintro ⟨hy, z, hz, rfl⟩
    exact ⟨z, ⟨fun h => hy (by rw [h]), hz⟩, rfl⟩

theorem card_ge_of_erase {k : ℕ} {B : Finset ℕ} (hB : B.card = k) (c : ℕ) :
    k - 1 ≤ (B.erase c).card := by
  have := Finset.pred_card_le_card_erase (s := B) (a := c); omega

/-- Inclusion–exclusion inside the middle list. -/
theorem triple_ge (X Y Z : Finset ℕ) :
    ((X ∩ Y).card : ℝ) + (Y ∩ Z).card - Y.card ≤ (X ∩ Y ∩ Z).card := by
  have h := Finset.card_union_add_card_inter (X ∩ Y) (Y ∩ Z)
  have hsub : (X ∩ Y) ∪ (Y ∩ Z) ⊆ Y := Finset.union_subset Finset.inter_subset_right
    Finset.inter_subset_left
  have hle := Finset.card_le_card hsub
  have heq : (X ∩ Y) ∩ (Y ∩ Z) = X ∩ Y ∩ Z := by ext; simp only [Finset.mem_inter]; tauto
  rw [heq] at h
  have : ((X ∩ Y).card : ℝ) + (Y ∩ Z).card = ((X ∩ Y) ∪ (Y ∩ Z)).card + (X ∩ Y ∩ Z).card := by
    exact_mod_cast h.symm
  have : (((X ∩ Y) ∪ (Y ∩ Z)).card : ℝ) ≤ Y.card := by exact_mod_cast hle
  linarith

/-! ### The local data of a pair of consecutive lists -/

/-- The bonus of a colour against a list. -/
noncomputable def hb (B : Finset ℕ) (c : ℕ) : ℝ := if c ∈ B then 0 else 1

/-- The mismatch of two lists of `k` colours. -/
noncomputable def mu (k : ℕ) (B C : Finset ℕ) : ℝ := (k : ℝ) - (B ∩ C).card

/-- State colours in the difference sets: `a ∈ B ∖ C` and `b ∈ C ∖ B`. -/
noncomputable def zz (B C : Finset ℕ) (a b : ℕ) : ℝ :=
  (if a ∈ B ∧ a ∉ C then 1 else 0) + (if b ∈ C ∧ b ∉ B then 1 else 0)

theorem hb_cases (B : Finset ℕ) (c : ℕ) : hb B c = 0 ∨ hb B c = 1 := by
  unfold hb; split_ifs <;> simp

theorem zz_nonneg (B C : Finset ℕ) (a b : ℕ) : 0 ≤ zz B C a b := by
  unfold zz; split_ifs <;> norm_num

theorem zz_le_two (B C : Finset ℕ) (a b : ℕ) : zz B C a b ≤ 2 := by
  unfold zz; split_ifs <;> norm_num

theorem zz_eq (B C : Finset ℕ) (a b : ℕ) :
    zz B C a b = (if a ∈ B \ C then 1 else 0) + (if b ∈ C \ B then 1 else 0) := by
  unfold zz; simp only [Finset.mem_sdiff]

theorem mu_nonneg {k : ℕ} {B C : Finset ℕ} (hB : B.card = k) : 0 ≤ mu k B C := by
  unfold mu
  have : (B ∩ C).card ≤ k := hB ▸ Finset.card_le_card Finset.inter_subset_left
  have : ((B ∩ C).card : ℝ) ≤ k := by exact_mod_cast this
  linarith

theorem mu_le {k : ℕ} (B C : Finset ℕ) : mu k B C ≤ k := by
  unfold mu; have : (0 : ℝ) ≤ (B ∩ C).card := Nat.cast_nonneg _; linarith

theorem mu_comm (k : ℕ) (B C : Finset ℕ) : mu k B C = mu k C B := by
  unfold mu; rw [Finset.inter_comm]

/-- Equal lists from zero mismatch. -/
theorem eq_of_mu_zero {k : ℕ} {B C : Finset ℕ} (hB : B.card = k) (hC : C.card = k)
    (h : mu k B C = 0) : B = C := by
  unfold mu at h
  have hc : (B ∩ C).card = k := by
    have : ((B ∩ C).card : ℝ) = k := by linarith
    exact_mod_cast this
  have h1 : B ∩ C = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have h2 : B ∩ C = C := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  rw [← h1, h2]

theorem card_sdiff_mu {k : ℕ} {B : Finset ℕ} (hB : B.card = k) (C : Finset ℕ) :
    ((B \ C).card : ℝ) = mu k B C := by
  unfold mu
  have := Finset.card_sdiff_add_card_inter B C
  rw [hB] at this
  have : ((B \ C).card : ℝ) + (B ∩ C).card = k := by exact_mod_cast this
  linarith

/-- The size of a punctured list. -/
theorem card_erase_hb {k : ℕ} {B : Finset ℕ} (hB : B.card = k) (c : ℕ) :
    ((B.erase c).card : ℝ) = (k : ℝ) - 1 + hb B c := by
  unfold hb
  split_ifs with h
  · rw [Finset.card_erase_of_mem h, hB]
    have : 1 ≤ k := hB ▸ Finset.card_pos.mpr ⟨c, h⟩
    push_cast [Nat.cast_sub this]; ring
  · rw [Finset.erase_eq_of_notMem h, hB]; ring

/-- **Consecutive punctured lists.** -/
theorem card_inter_erase {k : ℕ} {B C : Finset ℕ} (hB : B.card = k) (hC : C.card = k)
    {a b : ℕ} (hab : a ≠ b) :
    (((B.erase a) ∩ (C.erase b)).card : ℝ) = ((k : ℝ) - mu k B C - 2) + hb B a + hb C b + zz B C a b := by
  have hset : (B.erase a) ∩ (C.erase b) = ((B ∩ C).erase a).erase b := by
    ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
  rw [hset]
  have e1 : ((((B ∩ C).erase a).erase b).card : ℝ)
      = (B ∩ C).card - (if a ∈ B ∩ C then 1 else 0) - (if b ∈ B ∩ C then 1 else 0) := by
    have hb' : b ∈ (B ∩ C).erase a ↔ b ∈ B ∩ C := by
      rw [Finset.mem_erase]; exact ⟨fun h => h.2, fun h => ⟨Ne.symm hab, h⟩⟩
    by_cases ha : a ∈ B ∩ C <;> by_cases hbm : b ∈ B ∩ C
    · rw [Finset.card_erase_of_mem (hb'.mpr hbm), Finset.card_erase_of_mem ha]
      have h1 : 1 ≤ (B ∩ C).card := Finset.card_pos.mpr ⟨a, ha⟩
      have h2 : 1 ≤ ((B ∩ C).erase a).card := Finset.card_pos.mpr ⟨b, hb'.mpr hbm⟩
      rw [Finset.card_erase_of_mem ha] at h2
      simp only [ha, hbm, if_true]; push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
    · rw [Finset.erase_eq_of_notMem (fun h => hbm (hb'.mp h)), Finset.card_erase_of_mem ha]
      have h1 : 1 ≤ (B ∩ C).card := Finset.card_pos.mpr ⟨a, ha⟩
      simp only [ha, hbm, if_true, if_false]; push_cast [Nat.cast_sub h1]; ring
    · rw [Finset.card_erase_of_mem (hb'.mpr hbm), Finset.erase_eq_of_notMem ha]
      have h1 : 1 ≤ (B ∩ C).card := Finset.card_pos.mpr ⟨b, hbm⟩
      simp only [ha, hbm, if_true, if_false]; push_cast [Nat.cast_sub h1]; ring
    · rw [Finset.erase_eq_of_notMem (fun h => hbm (hb'.mp h)), Finset.erase_eq_of_notMem ha]
      simp only [ha, hbm, if_false]; ring
  rw [e1]
  unfold mu hb zz
  simp only [Finset.mem_inter]
  by_cases haB : a ∈ B <;> by_cases haC : a ∈ C <;> by_cases hbB : b ∈ B <;> by_cases hbC : b ∈ C <;>
    simp [haB, haC, hbB, hbC] <;> (try ring)

/-! ### The rate of one row

Notation: `n = k - 1`, `ℓ = n - 1 = k - 2`, `A = n² - n + 1 = ℓ² + ℓ + 1`, `t = A / n` (the uniform
rate of a row when the previous row is ignored). For a row, `h` is the bonus indicator (its state
colour is missing from its list), `μ` the number of colours its list does not share with the
previous list, and `z ∈ {0, 1, 2}` counts state colours lying in the two difference sets. -/

/-- **The log comparison.** If `x - y ≥ P - Q` with `x, y` in `[ℓ, K]`, then
`log (x / y) ≥ P / K - Q / ℓ`. -/
theorem log_ratio_ge {x y l K P Q : ℝ} (hl : 0 < l) (hlx : l ≤ x) (hxK : x ≤ K) (hy : 0 < y)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h : P - Q ≤ x - y) : P / K - Q / l ≤ log (x / y) := by
  have hx : 0 < x := lt_of_lt_of_le hl hlx
  have hK : 0 < K := lt_of_lt_of_le hx hxK
  have hlog : 1 - y / x ≤ log (x / y) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rwa [inv_div] at this
  refine le_trans ?_ hlog
  have hyx : 1 - y / x = (x - y) / x := by field_simp
  rw [hyx]
  rcases le_or_gt y x with hxy | hxy
  · -- nonnegative difference: divide by the larger `K`
    have h1 : (x - y) / K ≤ (x - y) / x :=
      div_le_div_of_nonneg_left (by linarith) hx hxK
    have h2 : P / K - Q / l ≤ (P - Q) / K := by
      rw [sub_div]
      have : Q / K ≤ Q / l := div_le_div_of_nonneg_left hQ hl (by linarith)
      linarith
    have h3 : (P - Q) / K ≤ (x - y) / K := div_le_div_of_nonneg_right h hK.le
    linarith
  · -- negative difference: divide by the smaller `ℓ`
    have h1 : (x - y) / l ≤ (x - y) / x := by
      rw [div_le_div_iff₀ hl hx]
      nlinarith
    have h2 : P / K - Q / l ≤ (P - Q) / l := by
      rw [sub_div]
      have : P / K ≤ P / l := div_le_div_of_nonneg_left hP hl (by linarith)
      linarith
    have h3 : (P - Q) / l ≤ (x - y) / l := div_le_div_of_nonneg_right h hl.le
    linarith

/-- **One row, main term.** If the previous row has bonus `h₀`, this row bonus `h₁`, list
mismatch `μ` and `z` state colours in the difference sets, the punctured intersection has
`e = (n - 1 - μ) + h₀ + h₁ + z` colours, and the uniform-on-list rate
`r̃ = (n + h₁) - e/(n + h₀)` satisfies
`log (r̃ / t) ≥ log (1 + μ/A) + ((n-1)/n) h₁/(n+1) - z/(n(n-1)) - (μ+1) h₀/(n(n+1)(n-1))`. -/
theorem rate_main {n h0 h1 z μ e : ℝ} (hn : 5 ≤ n) (hh0 : h0 = 0 ∨ h0 = 1)
    (hh1 : h1 = 0 ∨ h1 = 1) (hz : 0 ≤ z) (hμ : 0 ≤ μ) (hμk : μ ≤ n + 1)
    (he : e = (n - 1 - μ) + h0 + h1 + z) (he0 : 0 ≤ e) (heN : e ≤ n + h0) :
    log (1 + μ / (n ^ 2 - n + 1)) + ((n - 1) / n) * h1 / (n + 1)
        - z / (n * (n - 1)) - (μ + 1) * h0 / (n * (n + 1) * (n - 1))
      ≤ log (((n + h1) - e / (n + h0)) / ((n ^ 2 - n + 1) / n)) := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hA0 : 0 < n ^ 2 - n + 1 := by nlinarith
  have hnne : n ≠ 0 := hn0.ne'
  have hn1ne : n + 1 ≠ 0 := by linarith
  have hlne : n - 1 ≠ 0 := hl0.ne'
  have hden : 0 < n + h0 := by rcases hh0 with rfl | rfl <;> linarith
  have ht0 : 0 < (n ^ 2 - n + 1) / n := div_pos hA0 hn0
  have hr0 : 0 < (n ^ 2 - n + 1) / n + μ / n := by positivity
  -- the rate lies in `[n - 1, n + 1]`
  have hq : e / (n + h0) ≤ 1 := by rw [div_le_one hden]; exact heN
  have hq0 : 0 ≤ e / (n + h0) := div_nonneg he0 hden.le
  have hlo : n - 1 ≤ (n + h1) - e / (n + h0) := by
    rcases hh1 with rfl | rfl <;> linarith
  have hhi : (n + h1) - e / (n + h0) ≤ n + 1 := by
    rcases hh1 with rfl | rfl <;> linarith
  -- the comparison with `r₀ = t + μ/n`
  have hdiff : ((n - 1) / n) * h1 - (z / n + (μ + 1) * h0 / (n * (n + 1)))
      ≤ ((n + h1) - e / (n + h0)) - ((n ^ 2 - n + 1) / n + μ / n) := by
    rw [he]
    rcases hh0 with rfl | rfl
    · have key : (n + h1) - (n - 1 - μ + 0 + h1 + z) / (n + 0) - ((n ^ 2 - n + 1) / n + μ / n)
          = ((n - 1) / n) * h1 - z / n := by
        field_simp; ring
      rw [key]; simp
    · have key : (n + h1) - (n - 1 - μ + 1 + h1 + z) / (n + 1) - ((n ^ 2 - n + 1) / n + μ / n)
          = h1 * (n / (n + 1)) - z / (n + 1) - (1 + μ) / (n * (n + 1)) := by
        field_simp; ring
      rw [key]
      have c1 : ((n - 1) / n) * h1 ≤ h1 * (n / (n + 1)) := by
        rcases hh1 with rfl | rfl
        · simp
        · rw [mul_one, one_mul, div_le_div_iff₀ hn0 (by linarith)]; nlinarith
      have c2 : z / (n + 1) ≤ z / n := div_le_div_of_nonneg_left hz hn0 (by linarith)
      have c3 : (μ + 1) * 1 / (n * (n + 1)) = (1 + μ) / (n * (n + 1)) := by ring
      linarith
  have hP : 0 ≤ ((n - 1) / n) * h1 := by rcases hh1 with rfl | rfl <;> positivity
  have hh0nn : 0 ≤ h0 := by rcases hh0 with rfl | rfl <;> norm_num
  have hQ : 0 ≤ z / n + (μ + 1) * h0 / (n * (n + 1)) := by positivity
  have hlog := log_ratio_ge hl0 hlo hhi hr0 hP hQ hdiff
  -- split `log (r̃ / t) = log (r₀ / t) + log (r̃ / r₀)`
  have hrpos : 0 < (n + h1) - e / (n + h0) := by linarith
  have hsplit : log (((n + h1) - e / (n + h0)) / ((n ^ 2 - n + 1) / n))
      = log (((n ^ 2 - n + 1) / n + μ / n) / ((n ^ 2 - n + 1) / n))
        + log (((n + h1) - e / (n + h0)) / ((n ^ 2 - n + 1) / n + μ / n)) := by
    rw [← Real.log_mul (div_pos hr0 ht0).ne' (div_pos hrpos hr0).ne']
    congr 1; field_simp
  have hr0t : ((n ^ 2 - n + 1) / n + μ / n) / ((n ^ 2 - n + 1) / n) = 1 + μ / (n ^ 2 - n + 1) := by
    field_simp
  rw [hsplit, hr0t]
  have e1 : ((n - 1) / n) * h1 / (n + 1) - (z / n + (μ + 1) * h0 / (n * (n + 1))) / (n - 1)
      = ((n - 1) / n) * h1 / (n + 1) - z / (n * (n - 1)) - (μ + 1) * h0 / (n * (n + 1) * (n - 1)) := by
    field_simp; ring
  rw [e1] at hlog
  linarith

/-- **Row one.** `log ((n + h₁)/n) ≥ ((n-1)/n) h₁ / (n+1)`. -/
theorem rate_first {n h1 : ℝ} (hn : 5 ≤ n) (hh1 : h1 = 0 ∨ h1 = 1) :
    ((n - 1) / n) * h1 / (n + 1) ≤ log ((n + h1) / n) := by
  have hn0 : 0 < n := by linarith
  rcases hh1 with rfl | rfl
  · simp
  · have hpos : 0 < (n + 1) / n := by positivity
    refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hpos)
    rw [inv_div, mul_one]
    rw [show 1 - n / (n + 1) = 1 / (n + 1) by field_simp; ring]
    apply div_le_div_of_nonneg_right _ (by linarith)
    rw [div_le_one hn0]; linarith

/-- The cost of one state colour in a difference set of a row with mismatch `μ`. -/
noncomputable def zslope (n μ : ℝ) : ℝ :=
  min (1 / (n * (n - 1))) (log ((n ^ 2 - n + 1 + μ) / (n ^ 2 - n + 1 + μ - 2)) / 2)

theorem zslope_nonneg {n μ : ℝ} (hn : 2 ≤ n) (hμ : 0 ≤ μ) : 0 ≤ zslope n μ := by
  unfold zslope
  have hA : 0 < n ^ 2 - n + 1 + μ - 2 := by nlinarith
  refine le_min (by apply div_nonneg zero_le_one; nlinarith) ?_
  apply div_nonneg _ zero_le_two
  apply Real.log_nonneg
  rw [le_div_iff₀ hA]; linarith

/-- **The chord of the logarithm.** For `z ∈ [0, 2]` and `B - 2 > 0`,
`log (B - z) ≥ log B - z · log (B/(B-2))/2`. -/
theorem log_chord {B z : ℝ} (hB : 0 < B - 2) (hz : 0 ≤ z) (hz2 : z ≤ 2) :
    log B - z * (log (B / (B - 2)) / 2) ≤ log (B - z) := by
  have hB0 : 0 < B := by linarith
  have hc := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2
    (Set.mem_Ioi.mpr hB0) (Set.mem_Ioi.mpr hB) (show (0 : ℝ) ≤ 1 - z / 2 by linarith)
    (show (0 : ℝ) ≤ z / 2 by linarith) (by ring)
  have e : (1 - z / 2) • B + (z / 2) • (B - 2) = B - z := by simp only [smul_eq_mul]; ring
  rw [e] at hc
  simp only [smul_eq_mul] at hc
  rw [Real.log_div hB0.ne' hB.ne']
  nlinarith

/-- **One row, main term, with the chord.** As `rate_main`, with `z ∈ [0, 2]` costing
`zslope n μ` each. -/
theorem rate_main_chord {n h0 h1 z μ e : ℝ} (hn : 5 ≤ n) (hh0 : h0 = 0 ∨ h0 = 1)
    (hh1 : h1 = 0 ∨ h1 = 1) (hz : 0 ≤ z) (hz2 : z ≤ 2) (hμ : 0 ≤ μ) (hμk : μ ≤ n + 1)
    (he : e = (n - 1 - μ) + h0 + h1 + z) (he0 : 0 ≤ e) (heN : e ≤ n + h0) :
    log (1 + μ / (n ^ 2 - n + 1)) + ((n - 1) / n) * h1 / (n + 1)
        - z * zslope n μ - (μ + 1) * h0 / (n * (n + 1) * (n - 1))
      ≤ log (((n + h1) - e / (n + h0)) / ((n ^ 2 - n + 1) / n)) := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hA0 : 0 < n ^ 2 - n + 1 := by nlinarith
  have hold := rate_main hn hh0 hh1 hz hμ hμk he he0 heN
  -- the chord bound
  have hchord : log (1 + μ / (n ^ 2 - n + 1)) + ((n - 1) / n) * h1 / (n + 1)
        - z * (log ((n ^ 2 - n + 1 + μ) / (n ^ 2 - n + 1 + μ - 2)) / 2)
        - (μ + 1) * h0 / (n * (n + 1) * (n - 1))
      ≤ log (((n + h1) - e / (n + h0)) / ((n ^ 2 - n + 1) / n)) := by
    set A := n ^ 2 - n + 1 with hA
    have hden : 0 < n + h0 := by rcases hh0 with rfl | rfl <;> linarith
    have ht0 : 0 < A / n := div_pos hA0 hn0
    have hBz : 0 < A + μ - 2 := by nlinarith
    -- the bonus-free rate `r₀ = t + (μ - z)/n`
    set r0 := A / n + (μ - z) / n with hr0
    have hr0p : 0 < r0 := by
      rw [hr0, ← add_div]; apply div_pos _ hn0; linarith
    have hq : e / (n + h0) ≤ 1 := by rw [div_le_one hden]; exact heN
    have hq0 : 0 ≤ e / (n + h0) := div_nonneg he0 hden.le
    have hlo : n - 1 ≤ (n + h1) - e / (n + h0) := by rcases hh1 with rfl | rfl <;> linarith
    have hhi : (n + h1) - e / (n + h0) ≤ n + 1 := by rcases hh1 with rfl | rfl <;> linarith
    have hdiff : ((n - 1) / n) * h1 - (μ + 1) * h0 / (n * (n + 1))
        ≤ ((n + h1) - e / (n + h0)) - r0 := by
      rw [he, hr0, hA]
      rcases hh0 with rfl | rfl
      · have key : (n + h1) - (n - 1 - μ + 0 + h1 + z) / (n + 0)
            - ((n ^ 2 - n + 1) / n + (μ - z) / n) = ((n - 1) / n) * h1 := by
          field_simp; ring
        rw [key]; simp
      · have key : (n + h1) - (n - 1 - μ + 1 + h1 + z) / (n + 1)
            - ((n ^ 2 - n + 1) / n + (μ - z) / n)
            = h1 * (n / (n + 1)) - (μ + 1 - z) / (n * (n + 1)) := by
          field_simp; ring
        rw [key]
        have c1 : ((n - 1) / n) * h1 ≤ h1 * (n / (n + 1)) := by
          rcases hh1 with rfl | rfl
          · simp
          · rw [mul_one, one_mul, div_le_div_iff₀ hn0 (by linarith)]; nlinarith
        have c2 : (μ + 1 - z) / (n * (n + 1)) ≤ (μ + 1) * 1 / (n * (n + 1)) := by
          apply div_le_div_of_nonneg_right _ (by positivity); linarith
        linarith
    have hP : 0 ≤ ((n - 1) / n) * h1 := by rcases hh1 with rfl | rfl <;> positivity
    have hh0nn : 0 ≤ h0 := by rcases hh0 with rfl | rfl <;> norm_num
    have hQ : 0 ≤ (μ + 1) * h0 / (n * (n + 1)) := by positivity
    have hlog := log_ratio_ge hl0 hlo hhi hr0p hP hQ hdiff
    have hrpos : 0 < (n + h1) - e / (n + h0) := by linarith
    have hsplit : log (((n + h1) - e / (n + h0)) / (A / n))
        = log (r0 / (A / n)) + log (((n + h1) - e / (n + h0)) / r0) := by
      rw [← Real.log_mul (div_pos hr0p ht0).ne' (div_pos hrpos hr0p).ne']
      congr 1; field_simp
    have hr0t : r0 / (A / n) = (A + μ - z) / A := by
      rw [hr0]; field_simp; ring
    have hc := log_chord (B := A + μ) hBz hz hz2
    have hlA : log (r0 / (A / n)) = log (A + μ - z) - log A := by
      rw [hr0t, Real.log_div (by linarith) hA0.ne']
    have hl1 : log (1 + μ / A) = log (A + μ) - log A := by
      rw [show 1 + μ / A = (A + μ) / A by field_simp, Real.log_div (by linarith) hA0.ne']
    have e1 : ((n - 1) / n) * h1 / (n + 1) - (μ + 1) * h0 / (n * (n + 1)) / (n - 1)
        = ((n - 1) / n) * h1 / (n + 1) - (μ + 1) * h0 / (n * (n + 1) * (n - 1)) := by
      field_simp
    rw [e1] at hlog
    rw [hsplit, hlA]
    rw [hl1]
    linarith
  -- the better of the two slopes
  unfold zslope
  rcases le_total (1 / (n * (n - 1)))
      (log ((n ^ 2 - n + 1 + μ) / (n ^ 2 - n + 1 + μ - 2)) / 2) with hm | hm
  · rw [min_eq_left hm]
    have : z * (1 / (n * (n - 1))) = z / (n * (n - 1)) := by ring
    rw [this]; exact hold
  · rw [min_eq_right hm]; exact hchord

/-- From a log gain to the product form `GB ≥ GU · (1 + λ)`. -/
theorem mul_one_add_le_of_log {u b l : ℝ} (hu : 0 < u) (hb : 0 < b) (h : l ≤ log (b / u)) :
    u * (1 + l) ≤ b := by
  have hpos : 0 < b / u := div_pos hb hu
  have h2 : exp l ≤ b / u := by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr h
  have h3 : 1 + l ≤ b / u := (by rw [add_comm]; exact Real.add_one_le_exp _ : 1 + l ≤ _).trans h2
  calc u * (1 + l) ≤ u * (b / u) := mul_le_mul_of_nonneg_left h3 hu.le
    _ = b := mul_div_cancel₀ _ hu.ne'

/-! ### The sharp fibre bound -/

/-- **The sharp one-row fibre bound.** The pinned elements of `Ω` and their images under the
`m - 1` values of the row other than the current one are disjoint, so
`(R + m - 1) · Σ_P w ≤ R · Σ w` when the weights are within the factor `R`. -/
theorem fibre_row_sharp {α : Type*} [DecidableEq α] {Ω : Finset α} (w : α → ℝ)
    (hw : ∀ t, 0 ≤ w t) (P : α → Prop) [DecidablePred P] (get : α → ℕ) (set : α → ℕ → α)
    (φ : α → ℕ) (opts : α → Finset ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hopts : ∀ t ∈ Ω, m ≤ (opts t).card) (hcur : ∀ t ∈ Ω, get t ∈ opts t)
    (hmem : ∀ t ∈ Ω, ∀ x ∈ opts t, set t x ∈ Ω) (hget : ∀ t x, get (set t x) = x)
    (hset : ∀ t₁ t₂ x₁ x₂, set t₁ x₁ = set t₂ x₂ → get t₁ = get t₂ → t₁ = t₂)
    (hφ : ∀ t x, φ (set t x) = φ t) (hP : ∀ t, P t → get t = φ t)
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, w t ≤ R * w t') :
    (R + ((m : ℝ) - 1)) * ∑ t ∈ Ω.filter P, w t ≤ R * ∑ t ∈ Ω, w t := by
  classical
  set S := (Ω.filter P).sigma (fun t => (opts t).erase (get t)) with hS
  have h1 : ((m : ℝ) - 1) * ∑ t ∈ Ω.filter P, w t ≤ ∑ p ∈ S, w p.1 := by
    rw [hS, Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨htΩ, -⟩ := Finset.mem_filter.mp ht
    show ((m : ℝ) - 1) * w t ≤ ∑ _x ∈ (opts t).erase (get t), w t
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (m : ℝ) - 1 ≤ ((opts t).erase (get t)).card := by
      rw [Finset.card_erase_of_mem (hcur t htΩ)]
      have := hopts t htΩ
      have h1 : 1 ≤ (opts t).card := le_trans hm this
      rw [Nat.cast_sub h1]; push_cast
      have : (m : ℝ) ≤ (opts t).card := by exact_mod_cast this
      linarith
    exact mul_le_mul_of_nonneg_right hc (hw t)
  have h2 : ∑ p ∈ S, w p.1 ≤ ∑ p ∈ S, R * w (set p.1 p.2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨ht, hx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨htΩ, -⟩ := Finset.mem_filter.mp ht
    exact hR p.1 htΩ _ (hmem p.1 htΩ p.2 (Finset.mem_of_mem_erase hx))
  have hinjS : Set.InjOn (fun p : (_ : α) × ℕ => set p.1 p.2) S := by
    intro p hp q hq hpq
    obtain ⟨hpt, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hqt, hqx⟩ := Finset.mem_sigma.mp hq
    obtain ⟨-, hpP⟩ := Finset.mem_filter.mp hpt
    obtain ⟨-, hqP⟩ := Finset.mem_filter.mp hqt
    have hx : p.2 = q.2 := by
      have := congrArg get hpq; simp only [hget] at this; exact this
    have hg : get p.1 = get q.1 := by
      rw [hP _ hpP, hP _ hqP, ← hφ p.1 p.2, ← hφ q.1 q.2]
      exact congrArg φ hpq
    exact Sigma.ext (hset _ _ _ _ hpq hg) (heq_of_eq hx)
  have h3 : ∑ p ∈ S, w (set p.1 p.2) ≤ ∑ t ∈ Ω.filter (fun t => ¬ P t), w t := by
    rw [← Finset.sum_image (f := w) hinjS]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => hw t)
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hpt, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpΩ, hpP⟩ := Finset.mem_filter.mp hpt
    refine Finset.mem_filter.mpr ⟨hmem p.1 hpΩ p.2 (Finset.mem_of_mem_erase hpx), fun hP' => ?_⟩
    have e1 := hP _ hP'
    rw [hget, hφ, ← hP _ hpP] at e1
    exact (Finset.ne_of_mem_erase hpx) e1
  have h4 : ∑ t ∈ Ω, w t = ∑ t ∈ Ω.filter P, w t + ∑ t ∈ Ω.filter (fun t => ¬ P t), w t :=
    (Finset.sum_filter_add_sum_filter_not Ω P w).symm
  have h5 : ∑ p ∈ S, R * w (set p.1 p.2) = R * ∑ p ∈ S, w (set p.1 p.2) := by
    rw [Finset.mul_sum]
  have h6 := mul_le_mul_of_nonneg_left h3 hR0.le
  nlinarith

end GridGen.Lookback
