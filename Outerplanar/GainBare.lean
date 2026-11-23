/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Gain

/-!
# Bare even faces are in the gain class

Every bare even face (all path edges greedy) is in the gain class `Gain1` of
`Outerplanar/Gain.lean`. Write `α` for the ordinary constant of the face. Either every proper pair
has count at least `α`, or there is a pair `(a, b)` with

`count (c, d) ≥ α - 1 + [c ≠ a] + [d ≠ b]`

on every proper pair, which is the mixture `1 - 3/α` of the constant and `3/α` of the table
`(2 + [c ≠ a] + [d ≠ b]) / 3` (`zGood_lv`: floor `2/3`, bijections `≥ 32/27`, four-cell bound
`≥ 16/27 ≥ 9/16`).

* Squares (`gain1_square`): the deficient pair of `Outerplanar/BareEven.lean` (`bsq_low`).
* Longer even faces (`gain1_even_long`): enumerate the lists from the far end so that a colour kept
  from one list to the next keeps its index (`psum_aligned`). The path count is then the
  product of the matrices `K + D_j`, with `K` the walk matrix of the triangle and `D_j`
  diagonal, one at the indices whose colour changes at step `j` (`amat`). Expanding,
  `amat ≥ K^n + K^p D_j K^q` (`amat_single`). A deficient proper cell `(x, x)` forces every
  change at `x` to sit at step `1` or `n - 2`, and that change adds `K_{ix} (K^{n-2})_{xl} ≥ 3`
  to every cell with `i, l ≠ x` (`amat_long`).

The argument for every length is from `ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`
("In fact this same convex hull covers a bare even face of every length", a ChatGPT session);
formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### The lower table -/

theorem lv_ge_two (r s : Bool) : 2 ≤ lv r s := by cases r <;> cases s <;> decide

/-- Three cells of a bijection: at most one in the row and one in the column of the deficient
pair. -/
theorem three_bits : ∀ r₀ r₁ r₂ s₀ s₁ s₂ : Bool,
    (r₀ && r₁) = false → (r₀ && r₂) = false → (r₁ && r₂) = false →
    (s₀ && s₁) = false → (s₀ && s₂) = false → (s₁ && s₂) = false →
    32 ≤ lv r₀ s₀ * lv r₁ s₁ * lv r₂ s₂ := by
  decide

theorem bool_two {x y : Prop} [Decidable x] [Decidable y] (h : x → y → False) :
    (decide x && decide y) = false := by
  by_cases hx : x <;> by_cases hy : y <;> simp_all

/-- The table `(2 + [c ≠ a] + [d ≠ b]) / 3`. -/
noncomputable def lvZ (a b : ℕ) : ℕ → ℕ → ℝ := fun c e => (lv (decide (c = a)) (decide (e = b)) : ℝ) / 3

theorem zGood_lv (S T : Finset ℕ) (a b : ℕ) : ZGood S T (lvZ a b) := by
  refine ⟨fun c e => by unfold lvZ; positivity, fun c _ e _ _ => ?_, ?_, ?_⟩
  · unfold lvZ
    have : (2 : ℝ) ≤ lv (decide (c = a)) (decide (e = b)) := by exact_mod_cast lv_ge_two _ _
    linarith
  · intro α β hα hβ _ _ _
    have hr : ∀ {x y : Fin 3}, x ≠ y → (decide (α x = a) && decide (α y = a)) = false :=
      fun hxy => bool_two fun h1 h2 => hxy (hα (h1.trans h2.symm))
    have hs : ∀ {x y : Fin 3}, x ≠ y → (decide (β x = b) && decide (β y = b)) = false :=
      fun hxy => bool_two fun h1 h2 => hxy (hβ (h1.trans h2.symm))
    have key := three_bits _ _ _ _ _ _ (hr (by decide : (0 : Fin 3) ≠ 1))
      (hr (by decide : (0 : Fin 3) ≠ 2)) (hr (by decide : (1 : Fin 3) ≠ 2))
      (hs (by decide : (0 : Fin 3) ≠ 1)) (hs (by decide : (0 : Fin 3) ≠ 2))
      (hs (by decide : (1 : Fin 3) ≠ 2))
    have key' : (32 : ℝ) ≤ (lv (decide (α 0 = a)) (decide (β 0 = b)) : ℝ)
        * lv (decide (α 1 = a)) (decide (β 1 = b)) * lv (decide (α 2 = a)) (decide (β 2 = b)) := by
      exact_mod_cast key
    simp only [lvZ, Fin.prod_univ_three]
    linarith
  · intro p q hm _ i j k l hij hik hil hjk hjl hkl
    have hr : ∀ {x y z : Fin 6}, x ≠ y → x ≠ z → y ≠ z →
        (decide (p x = a) && decide (p y = a) && decide (p z = a)) = false :=
      fun hxy hxz hyz => bool_three fun h1 h2 h3 =>
        hm.no_three hxy hxz hyz (h1.trans h2.symm) (h1.trans h3.symm)
    have hs : ∀ {x y z : Fin 6}, x ≠ y → x ≠ z → y ≠ z →
        (decide (q x = b) && decide (q y = b) && decide (q z = b)) = false :=
      fun hxy hxz hyz => bool_three fun h1 h2 h3 =>
        hm.symm.no_three hxy hxz hyz (h1.trans h2.symm) (h1.trans h3.symm)
    have hrs : ∀ {x y : Fin 6}, x ≠ y →
        (decide (p x = a) && decide (q x = b) && (decide (p y = a) && decide (q y = b))) = false :=
      fun hxy => bool_four fun h1 h2 h3 h4 =>
        hxy (hm.injective (h1.trans h3.symm) (h2.trans h4.symm))
    have hn := four_bits _ _ _ _ _ _ _ _ (hr hij hik hjk) (hr hij hil hjl) (hr hik hil hkl)
      (hr hjk hjl hkl) (hs hij hik hjk) (hs hij hil hjl) (hs hik hil hkl) (hs hjk hjl hkl)
      (hrs hij) (hrs hik) (hrs hil) (hrs hjk) (hrs hjl) (hrs hkl)
    have hn' : (432 : ℝ) ≤ (lv (decide (p i = a)) (decide (q i = b)) : ℝ) ^ 2
        * (lv (decide (p j = a)) (decide (q j = b)) : ℝ) ^ 2
        * lv (decide (p k = a)) (decide (q k = b)) * lv (decide (p l = a)) (decide (q l = b)) := by
      exact_mod_cast hn
    simp only [lvZ]
    have e : ∀ x y z w : ℝ, (x / 3) ^ 2 * (y / 3) ^ 2 * (z / 3) * (w / 3)
        = x ^ 2 * y ^ 2 * z * w / 729 := fun x y z w => by ring
    rw [e, one_pow, mul_one, le_div_iff₀ (by norm_num)]
    nlinarith

/-- The mixture of the constant and `lvZ a b` with weight `3/α`. -/
theorem gain1_of_low {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {α K : ℝ} (hα : 3 ≤ α)
    {a b : ℕ} (h : ∀ c ∈ S, ∀ d ∈ T, c ≠ d →
      K * (α - 1 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0)) ≤ W c d) :
    Gain1 S T W (α * K) := by
  have hαpos : 0 < α := by linarith
  refine ⟨3 / α, lvZ a b, by positivity, by rw [div_le_one hαpos]; exact hα, zGood_lv S T a b,
    fun c hc d hd hcd => le_trans (le_of_eq ?_) (h c hc d hd hcd)⟩
  simp only [lvZ]
  rw [lv_cast]
  field_simp
  ring

/-! ### Squares -/

/-- **A bare square is in the gain class.** -/
theorem gain1_square (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin 3 → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 3 → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Gain1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * ∏ j, A j) := by
  have hP0 : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have h3 : faceConst3 2 = 3 := by norm_num [faceConst3]
  have hW : ∀ c ∈ Lu, ∀ d ∈ Lv,
      (∏ j, A j) * bsq (Li 0) (Li 1) c d ≤ faceSum Li (fun _ _ => 1) E c d := by
    intro c hc d hd
    have := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
    rw [faceSum_two Li (fun _ => neP)] at this
    exact this
  by_cases hall : ∀ c ∈ Lu, ∀ d ∈ Lv, c ≠ d → 3 ≤ bsq (Li 0) (Li 1) c d
  · refine Dominant.gain1 fun c hc d hd hcd => ?_
    rw [h3]
    calc 3 * ∏ j, A j = (∏ j, A j) * 3 := mul_comm _ _
      _ ≤ (∏ j, A j) * bsq (Li 0) (Li 1) c d := mul_le_mul_of_nonneg_left (hall c hc d hd hcd) hP0
      _ ≤ _ := hW c hc d hd
  · push Not at hall
    obtain ⟨a, -, b, -, hab, hlt⟩ := hall
    rw [h3]
    refine gain1_of_low (le_refl 3) (a := a) (b := b) fun c hc d hd hcd => ?_
    have := bsq_low (hLi 0) (hLi 1) hab hlt hcd
    calc (∏ j, A j) * (3 - 1 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0))
        = (∏ j, A j) * (2 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0)) := by ring
      _ ≤ (∏ j, A j) * bsq (Li 0) (Li 1) c d := mul_le_mul_of_nonneg_left this hP0
      _ ≤ _ := hW c hc d hd

/-! ### Aligned path matrices -/

/-- The product of the aligned path matrices `K + D` (`K` off the diagonal, `D` the diagonal
indicator `δ`). -/
def amat : List (Fin 3 → Bool) → Fin 3 → Fin 3 → ℕ
  | [], i, l => if i = l then 1 else 0
  | δ :: δs, i, l => amat δs (i + 1) l + amat δs (i + 2) l + (if δ i then amat δs i l else 0)

theorem cnt_zero (a b : Fin 3) : cnt 0 a b = if a = b then 1 else 0 := by
  unfold cnt
  split_ifs <;> rfl

theorem amat_ge : ∀ (δs : List (Fin 3 → Bool)) (i l : Fin 3), cnt δs.length i l ≤ amat δs i l
  | [], i, l => by
    show cnt 0 i l ≤ amat [] i l
    rw [cnt_zero]
    exact le_refl _
  | δ :: δs, i, l => by
    simp only [amat, List.length_cons, cnt_succ]
    have := amat_ge δs (i + 1) l
    have := amat_ge δs (i + 2) l
    omega

/-- One diagonal term of the expansion. -/
theorem amat_single : ∀ (pre : List (Fin 3 → Bool)) (δ : Fin 3 → Bool)
    (post : List (Fin 3 → Bool)) (x : Fin 3), δ x = true → ∀ i l : Fin 3,
    cnt (pre.length + 1 + post.length) i l + cnt pre.length i x * cnt post.length x l
      ≤ amat (pre ++ δ :: post) i l
  | [], δ, post, x, hx, i, l => by
    simp only [List.nil_append, amat, List.length_nil, zero_add]
    rw [add_comm 1, cnt_succ]
    have h1 := amat_ge post (i + 1) l
    have h2 := amat_ge post (i + 2) l
    have h3 := amat_ge post i l
    rw [cnt_zero]
    by_cases hix : i = x
    · subst hix
      simp only [hx, ite_true, one_mul]
      omega
    · simp only [hix, ite_false, zero_mul, add_zero]
      omega
  | δ' :: pre, δ, post, x, hx, i, l => by
    simp only [List.cons_append, amat, List.length_cons]
    have h1 := amat_single pre δ post x hx (i + 1) l
    have h2 := amat_single pre δ post x hx (i + 2) l
    rw [show pre.length + 1 + 1 + post.length = (pre.length + 1 + post.length) + 1 by ring,
      cnt_succ, cnt_succ, add_mul]
    have h0 : 0 ≤ (if δ' i = true then amat (pre ++ δ :: post) i l else 0) := Nat.zero_le _
    linarith

theorem dN_mono : Monotone dN := monotone_nat_of_le_succ fun k => by
  rw [dN_succ]; exact Nat.le_add_right _ _

theorem sN_pos_of_ne_one : ∀ k, k ≠ 1 → 0 < sN k
  | 0, _ => by decide
  | 1, h => absurd rfl h
  | (k + 2), _ => by rw [sN_succ]; have := dN_pos k; omega

theorem cnt_ge_sN {k : ℕ} (hk : Odd k) (a b : Fin 3) : sN k ≤ cnt k a b := by
  have := (sN_dN_parity k).2 hk
  unfold cnt
  split_ifs <;> omega

/-- **The aligned matrix of an odd path of at least five steps**: either every proper cell is at
least the constant, or there is an index `x` with `cnt ≥ sN n + [i ≠ x] + [l ≠ x]` on all of
them. A cell is proper when its indices differ or the colour at the index changes. -/
theorem amat_long (δs : List (Fin 3 → Bool)) (hodd : Odd δs.length) (h5 : 5 ≤ δs.length) :
    (∀ i l, (i ≠ l ∨ ∃ δ ∈ δs, δ i = true) → dN δs.length ≤ amat δs i l) ∨
    ∃ x, ∀ i l, (i ≠ l ∨ ∃ δ ∈ δs, δ i = true) →
      sN δs.length + (if i ≠ x then 1 else 0) + (if l ≠ x then 1 else 0) ≤ amat δs i l := by
  set n := δs.length with hn
  have hpar : dN n = sN n + 1 := (sN_dN_parity n).2 hodd
  by_cases hdef : ∃ x, (∃ δ ∈ δs, δ x = true) ∧ amat δs x x < dN n
  · right
    obtain ⟨x, ⟨δ, hδ, hx⟩, hlt⟩ := hdef
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hδ
    have hlen : n = pre.length + 1 + post.length := by
      rw [hn, List.length_append, List.length_cons]; ring
    have hs := amat_single pre δ post x hx x x
    rw [← hlen] at hs
    have hxx : cnt n x x = sN n := by simp [cnt]
    rw [hxx] at hs
    have hzero : sN pre.length * sN post.length = 0 := by
      simp only [cnt, ite_true] at hs
      omega
    have h3 : 3 ≤ dN (n - 2) := (show 3 ≤ dN 3 by decide).trans (dN_mono (by omega))
    have hone : pre.length = 1 ∨ post.length = 1 := by
      rcases Nat.mul_eq_zero.mp hzero with h | h
      · by_contra hc
        push Not at hc
        exact absurd h (sN_pos_of_ne_one _ hc.1).ne'
      · by_contra hc
        push Not at hc
        exact absurd h (sN_pos_of_ne_one _ hc.2).ne'
    refine ⟨x, fun i l hil => ?_⟩
    have hge := amat_ge (pre ++ δ :: post) i l
    rw [← hn] at hge
    by_cases hi : i = x <;> by_cases hl : l = x
    · subst hi; subst hl
      simp only [ne_eq, not_true_eq_false, ite_false, add_zero]
      simpa [cnt] using hge
    · subst hi
      have : cnt n i l = dN n := by simp [cnt, Ne.symm hl]
      simp only [ne_eq, not_true_eq_false, ite_false, hl, not_false_eq_true, ite_true, add_zero]
      omega
    · subst hl
      have : cnt n i l = dN n := by simp [cnt, hi]
      simp only [ne_eq, hi, not_false_eq_true, ite_true, not_true_eq_false, ite_false, add_zero]
      omega
    · have hsg := amat_single pre δ post x hx i l
      rw [← hlen] at hsg
      have hc1 : cnt pre.length i x = dN pre.length := by simp [cnt, hi]
      have hc2 : cnt post.length x l = dN post.length := by simp [cnt, Ne.symm hl]
      rw [hc1, hc2] at hsg
      have hcg := cnt_ge_sN hodd i l
      have hprod : 3 ≤ dN pre.length * dN post.length := by
        rcases hone with h | h
        · have : post.length = n - 2 := by omega
          rw [h, this]
          simpa [show dN 1 = 1 from rfl] using h3
        · have : pre.length = n - 2 := by omega
          rw [h, this]
          simpa [show dN 1 = 1 from rfl] using h3
      simp only [ne_eq, hi, not_false_eq_true, ite_true, hl]
      omega
  · left
    push Not at hdef
    intro i l hil
    by_cases hil' : i = l
    · subst hil'
      rcases hil with h | h
      · exact absurd rfl h
      · exact hdef i h
    · have := amat_ge δs i l
      rw [← hn] at this
      have e : cnt n i l = dN n := by simp [cnt, hil']
      omega

/-! ### Alignment along the path -/

theorem enum_surj {S : Finset ℕ} (hS : S.card = 3) {α : Fin 3 → ℕ} (hα : Function.Injective α)
    (hm : ∀ a, α a ∈ S) {c : ℕ} (hc : c ∈ S) : ∃ a, α a = c := by
  have himg : univ.image α = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc
      exact hm a
    · rw [Finset.card_image_of_injective _ hα, hS, Finset.card_univ, Fintype.card_fin]
  rw [← himg] at hc
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hc
  exact ⟨a, ha⟩

/-- The step of an aligned enumeration. -/
theorem neP_aligned {α γ : Fin 3 → ℕ} (hal : ∀ c a, γ c = α a → a = c) (i i' : Fin 3) :
    neP (γ i) (α i') = if i' = i then (if decide (γ i ≠ α i) then 1 else 0) else 1 := by
  unfold neP
  by_cases h : i' = i
  · subst h
    by_cases h' : γ i' = α i' <;> simp [h']
  · have : γ i ≠ α i' := fun e => h (hal _ _ e)
    simp [h, this]

theorem sum_ite_three (i : Fin 3) (e : ℝ) (f : Fin 3 → ℝ) :
    ∑ i', (if i' = i then e else 1) * f i' = f (i + 1) + f (i + 2) + e * f i := by
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

theorem amat_cons_cast (δ : Fin 3 → Bool) (δs : List (Fin 3 → Bool)) (i l : Fin 3) :
    (amat (δ :: δs) i l : ℝ) = ∑ i', (if i' = i then (if δ i then 1 else 0) else 1)
      * (amat δs i' l : ℝ) := by
  rw [sum_ite_three i _ fun i' => (amat δs i' l : ℝ)]
  simp only [amat]
  push_cast
  split_ifs <;> simp

/-- **Aligned enumerations**: the path count dominates the aligned matrix product, and an index
whose colour never changes keeps its colour. -/
theorem psum_aligned : ∀ (Vs : List (Finset ℕ)) (Lv : Finset ℕ) (ψ : Fin 3 → ℕ),
    (∀ L ∈ Vs, L.card = 3) → Function.Injective ψ → (∀ a, ψ a ∈ Lv) →
    ∀ L₀ : Finset ℕ, L₀.card = 3 → ∃ (φ : Fin 3 → ℕ) (δs : List (Fin 3 → Bool)),
      Function.Injective φ ∧ (∀ a, φ a ∈ L₀) ∧ δs.length = Vs.length + 1 ∧
      (∀ i l, (amat δs i l : ℝ) ≤ psum (Vs ++ [Lv]) (nes (Vs.length + 1)) (φ i) (ψ l)) ∧
      (∀ i, (∀ δ ∈ δs, δ i = false) → φ i = ψ i)
  | [], Lv, ψ, _, hψ, hψm, L₀, hL₀ => by
    obtain ⟨φ, hφ, hφm, hal⟩ := exists_aligned hL₀ hψ
    refine ⟨φ, [fun i => decide (φ i ≠ ψ i)], hφ, hφm, rfl, fun i l => ?_, fun i h => ?_⟩
    · rw [List.nil_append, show nes ([] : List (Finset ℕ)).length.succ = [neP] from rfl,
        psum_single Lv neP _ _ (hψm l), amat_cons_cast, neP_aligned hal]
      simp only [amat]
      rw [Fin.sum_univ_three]
      fin_cases i <;> fin_cases l <;> simp
    · have := h _ (List.mem_singleton_self _)
      simpa using this
  | L :: Vs, Lv, ψ, hVs, hψ, hψm, L₀, hL₀ => by
    obtain ⟨φ₁, δs, hφ₁, hφ₁m, hlen, hle, hkeep⟩ :=
      psum_aligned Vs Lv ψ (fun L' hL' => hVs L' (List.mem_cons_of_mem _ hL')) hψ hψm L
        (hVs L (List.mem_cons_self))
    obtain ⟨φ, hφ, hφm, hal⟩ := exists_aligned hL₀ hφ₁
    refine ⟨φ, (fun i => decide (φ i ≠ φ₁ i)) :: δs, hφ, hφm, by simp [hlen], fun i l => ?_,
      fun i h => ?_⟩
    · rw [List.cons_append, List.length_cons, nes_succ, psum_cons,
        sum_enum (hVs L List.mem_cons_self) hφ₁ hφ₁m, amat_cons_cast]
      refine Finset.sum_le_sum fun i' _ => ?_
      rw [neP_aligned hal]
      refine mul_le_mul (le_refl _) (hle i' l) (Nat.cast_nonneg _) ?_
      split_ifs <;> norm_num
    · have h1 := h _ List.mem_cons_self
      have h2 : φ i = φ₁ i := by simpa using h1
      rw [h2]
      exact hkeep i fun δ hδ => h δ (List.mem_cons_of_mem _ hδ)

/-! ### Longer even faces -/

/-- **A bare even face of length at least six is in the gain class.** -/
theorem gain1_even_long {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Gain1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hP0 : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have hcount : ∀ c ∈ Lu, ∀ d ∈ Lv, (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) c d
      ≤ faceSum Li (fun _ _ => 1) E c d := fun c hc d hd => by
    have h1 := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
    have h2 : faceSum Li (fun _ _ => 1) (fun _ => neP) c d
        = psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) c d := by
      rw [faceSum_eq_psum Li Lv _ c d hd, List.ofFn_const]
      rfl
    rwa [h2] at h1
  have hcard : ∀ L ∈ List.ofFn Li, L.card = 3 := fun L hL => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hL
    exact hLi i
  obtain ⟨ψ, hψ, hψm⟩ := exists_enum hLv
  obtain ⟨φ, δs, hφ, hφm, hlen, hle, hkeep⟩ :=
    psum_aligned (List.ofFn Li) Lv ψ hcard hψ hψm Lu hLu
  rw [List.length_ofFn] at hlen hle
  have hodd : Odd δs.length := by
    rw [hlen]; obtain ⟨k, hk⟩ := hm; exact ⟨k, by omega⟩
  have hα : faceConst3 m = (dN (m + 1) : ℝ) := faceConst3_eq_dN m
  -- proper cells in indices
  have hprop : ∀ i l, φ i ≠ ψ l → (i ≠ l ∨ ∃ δ ∈ δs, δ i = true) := fun i l hne => by
    by_cases hil : i = l
    · subst hil
      right
      by_contra hc
      push Not at hc
      exact hne (hkeep i fun δ hδ => by simpa using hc δ hδ)
    · exact Or.inl hil
  have hα3 : (3 : ℝ) ≤ faceConst3 m := by
    obtain ⟨k, hk⟩ := hm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, show k' + 1 + (k' + 1) = 2 * k' + 2 by ring]
    exact faceConst3_even_ge_three k'
  rcases amat_long δs hodd (by omega) with hall | ⟨x, hx⟩
  · refine Dominant.gain1 fun c hc d hd hcd => ?_
    obtain ⟨i, rfl⟩ := enum_surj hLu hφ hφm hc
    obtain ⟨l, rfl⟩ := enum_surj hLv hψ hψm hd
    have h1 : (dN (m + 1) : ℝ) ≤ amat δs i l := by
      have := hall i l (hprop i l hcd)
      rw [hlen] at this
      exact_mod_cast this
    calc faceConst3 m * ∏ j, A j = (∏ j, A j) * dN (m + 1) := by rw [hα, mul_comm]
      _ ≤ (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) (φ i) (ψ l) :=
          mul_le_mul_of_nonneg_left (h1.trans (hle i l)) hP0
      _ ≤ _ := hcount _ hc _ hd
  · refine gain1_of_low hα3 (a := φ x) (b := ψ x) fun c hc d hd hcd => ?_
    obtain ⟨i, rfl⟩ := enum_surj hLu hφ hφm hc
    obtain ⟨l, rfl⟩ := enum_surj hLv hψ hψm hd
    have hpar : dN (m + 1) = sN (m + 1) + 1 := by
      have := (sN_dN_parity (m + 1)).2 (by rw [← hlen]; exact hodd)
      exact this
    have h1 := hx i l (hprop i l hcd)
    rw [hlen] at h1
    have e1 : (if φ i ≠ φ x then (1 : ℝ) else 0) = if i ≠ x then 1 else 0 := by
      by_cases h : i = x
      · simp [h]
      · have : φ i ≠ φ x := fun e => h (hφ e)
        simp [h, this]
    have e2 : (if ψ l ≠ ψ x then (1 : ℝ) else 0) = if l ≠ x then 1 else 0 := by
      by_cases h : l = x
      · simp [h]
      · have : ψ l ≠ ψ x := fun e => h (hψ e)
        simp [h, this]
    have h2 : faceConst3 m - 1 + (if i ≠ x then (1 : ℝ) else 0) + (if l ≠ x then 1 else 0)
        ≤ amat δs i l := by
      rw [hα]
      have : ((dN (m + 1) : ℕ) : ℝ) = (sN (m + 1) : ℝ) + 1 := by exact_mod_cast hpar
      rw [this]
      have h1' : ((sN (m + 1) + (if i ≠ x then 1 else 0) + (if l ≠ x then 1 else 0) : ℕ) : ℝ)
          ≤ amat δs i l := by exact_mod_cast h1
      push_cast at h1'
      convert h1' using 2; split_ifs <;> simp
    rw [e1, e2]
    calc (∏ j, A j) * (faceConst3 m - 1 + (if i ≠ x then 1 else 0) + (if l ≠ x then 1 else 0))
        ≤ (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) (φ i) (ψ l) :=
          mul_le_mul_of_nonneg_left (h2.trans (hle i l)) hP0
      _ ≤ _ := hcount _ hc _ hd

/-- **Every bare even face is in the gain class.** -/
theorem gain1_even_bare {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Gain1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  rcases Nat.lt_or_ge m 4 with h | h
  · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
    exact gain1_square Lu Lv Li hLi E hE0 A hA hE
  · exact gain1_even_long hm h Lu Lv Li hLu hLv hLi E hE0 A hA hE

end Outerplanar
