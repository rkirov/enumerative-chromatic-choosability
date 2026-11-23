/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.HallTri
import Outerplanar.OddBall

/-!
# The hexagon bound through faces of odd length

A face with an odd number `m ≥ 3` of interior vertices maps the hexagon bound (`Hex`) on all
its path edges to the hexagon bound on its root edge (`hexOddClosed`). Triangles do the same
(`hex_tri`, `Outerplanar/Hex.lean`).

The proof is the unit-weight case of the balanced designs of `Outerplanar/Walks.lean`. Every
table of the path has `A⁶ ≤ u M` (`OffHex`), and the chosen walks of the six root cells use
every pair of different indices equally often, so their total weight is `up Ms α = (∏ u M)^α`.

* identity monodromy: all walks (`walks_hex_id`);
* transposition: all walks except the alternating walk in the two closed cells
  (`walks_hex_tr`);
* rotation: the closed cells with all their `α + 1` walks (`Dp_sq`) and the bijection triple
  through a uniform midpoint (`halves`); the constant is then `(α + 1)³ · 27 s² a⁴ ≥ α⁶`
  (`walk_num`).

This is part of the formalization of the six-even-face theorem (research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`, section "From two to six").
-/

namespace Outerplanar

open Finset

/-! ### Tables -/

/-- The hexagon bound of one table: the six entries at pairs of different indices. -/
def OffHex (M : Fin 3 → Fin 3 → ℝ) (A : ℝ) : Prop := A ^ 6 ≤ u M

theorem up_one_ge {Ms : List (Fin 3 → Fin 3 → ℝ)} {As : List ℝ} (h : List.Forall₂ OffHex Ms As)
    (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 ≤ A) : As.prod ^ 6 ≤ up Ms 1 := by
  induction h with
  | nil => simp [up]
  | @cons M A Ms As h1 _ ih =>
    rw [up_cons, pow_one, List.prod_cons, mul_pow]
    have hA0 := hA A List.mem_cons_self
    have ih' := ih (fun M' h' => hM M' (List.mem_cons_of_mem _ h'))
      (fun A' h' => hA A' (List.mem_cons_of_mem _ h'))
    exact mul_le_mul h1 ih' (pow_nonneg (List.prod_nonneg fun A' h' =>
      hA A' (List.mem_cons_of_mem _ h')) _) ((pow_nonneg hA0 _).trans h1)

theorem offHex_pos {Ms : List (Fin 3 → Fin 3 → ℝ)} {As : List ℝ} (h : List.Forall₂ OffHex Ms As)
    (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A) :
    ∀ M ∈ Ms, ∀ a b, a ≠ b → 0 < M a b := by
  induction h with
  | nil => simp
  | @cons M A Ms As h1 _ ih =>
    intro M' hM' a b hab
    rcases List.mem_cons.mp hM' with rfl | hmem
    · have hpos : 0 < u M' := lt_of_lt_of_le (pow_pos (hA A List.mem_cons_self) 6) h1
      obtain ⟨k, hk⟩ := offPair_surj a b hab
      rcases (hM M' List.mem_cons_self a b).eq_or_lt with h0 | h0
      · exfalso
        refine hpos.ne' (Finset.prod_eq_zero (mem_univ k) ?_)
        rw [hk]
        exact h0.symm
      · exact h0
    · exact ih (fun M'' h'' => hM M'' (List.mem_cons_of_mem _ h''))
        (fun A' h'' => hA A' (List.mem_cons_of_mem _ h'')) M' hmem a b hab

/-! ### Assembly -/

/-- Six cells with chosen walk products `Γ k` whose total is `U ^ α`. -/
theorem hex_assembly {α : ℕ} (hα : 0 < α) {p Γ : Fin 6 → ℝ} {U B : ℝ} (hp : ∀ k, 0 ≤ p k)
    (hΓ : ∀ k, 0 ≤ Γ k) (hpΓ : ∀ k, (α : ℝ) ^ α * Γ k ≤ p k ^ α) (hprod : ∏ k, Γ k = U ^ α)
    (hB : 0 ≤ B) (hU : B ≤ U) : (α : ℝ) ^ 6 * B ≤ ∏ k, p k := by
  have hαr : (0 : ℝ) ≤ (α : ℝ) := Nat.cast_nonneg _
  have h1 : ∏ k, ((α : ℝ) ^ α * Γ k) ≤ ∏ k, p k ^ α :=
    Finset.prod_le_prod₀ (fun k _ => mul_nonneg (pow_nonneg hαr _) (hΓ k)) fun k _ => hpΓ k
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hprod,
    Finset.prod_pow] at h1
  have h2 : ((α : ℝ) ^ 6 * B) ^ α ≤ (∏ k, p k) ^ α := by
    calc ((α : ℝ) ^ 6 * B) ^ α = ((α : ℝ) ^ α) ^ 6 * B ^ α := by rw [mul_pow, ← pow_mul,
          ← pow_mul, mul_comm 6 α]
      _ ≤ ((α : ℝ) ^ α) ^ 6 * U ^ α :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hU _) (by positivity)
      _ ≤ _ := h1
  exact (pow_le_pow_iff_left₀ (by positivity) (prod_nonneg fun k _ => hp k) hα.ne').mp h2

/-! ### The three kinds of monodromy -/

theorem walks_hex_id (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (hpos : 0 < Ms.length)
    (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hhex : List.Forall₂ OffHex Ms As) :
    ((dN Ms.length : ℝ) * As.prod) ^ 6 ≤ ∏ k, pw Ms (offPair k).1 (offPair k).2 := by
  have hα : 0 < dN Ms.length := by
    obtain ⟨k, hk⟩ : ∃ k, Ms.length = k + 1 := ⟨Ms.length - 1, by omega⟩
    rw [hk]
    exact dN_pos k
  have hc : ∀ k : Fin 6, cnt Ms.length (offPair k).1 (offPair k).2 = dN Ms.length := fun k => by
    simp [cnt, offPair_ne k]
  rw [mul_pow]
  refine hex_assembly hα (p := fun k => pw Ms (offPair k).1 (offPair k).2)
    (Γ := fun k => wgp Ms (offPair k).1 (offPair k).2) (U := up Ms 1)
    (fun k => pw_nonneg Ms hM _ _) (fun k => wgp_nonneg Ms hM _ _) (fun k => ?_) ?_
    (pow_nonneg (List.prod_nonneg fun A hA' => (hA A hA').le) _)
    (up_one_ge hhex hM fun A hA' => (hA A hA').le)
  · have := pw_ub Ms hM (offPair k).1 (offPair k).2
    rwa [hc k] at this
  · show Og Ms = _
    rw [Og_eq, ← up_mul, one_mul]

theorem walks_hex_tr (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (hlen : Even Ms.length)
    (hpos : 0 < Ms.length) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hhex : List.Forall₂ OffHex Ms As) (a : Fin 3) :
    ((dN Ms.length : ℝ) * As.prod) ^ 6 ≤ ∏ k, pw Ms (offPair k).1 (tr a (offPair k).2) := by
  have hMpos := offHex_pos hhex hM hA
  have hα : 0 < dN Ms.length := by
    obtain ⟨k, hk⟩ : ∃ k, Ms.length = k + 1 := ⟨Ms.length - 1, by omega⟩
    rw [hk]
    exact dN_pos k
  have hs : sN Ms.length = dN Ms.length + 1 := (sN_dN_parity _).1 hlen
  set α := dN Ms.length with hαdef
  have hp := pw_nonneg Ms hM
  have hg := wgp_nonneg Ms hM
  have big : ∀ (s : Bool) (x : Fin 3), (α : ℝ) ^ α * (wgp Ms x x / alt s Ms x) ≤ pw Ms x x ^ α := by
    intro s x
    obtain ⟨-, i2, i3, -⟩ := pw_ub_alt Ms hM s x
    rw [altEnd_even _ s x hlen] at i2 i3
    have hc : cnt Ms.length x x - 1 = α := by
      simp [cnt, hs]
    rw [hc] at i3
    have hal := alt_pos s Ms hMpos x
    rw [← mul_div_assoc, div_le_iff₀ hal]
    refine i3.trans (mul_le_mul_of_nonneg_right ?_ hal.le)
    exact pow_le_pow_left₀ (sub_nonneg.mpr i2) (by linarith) _
  have small : ∀ x w : Fin 3, x ≠ w → (α : ℝ) ^ α * wgp Ms x w ≤ pw Ms x w ^ α := by
    intro x w hxw
    have hc : cnt Ms.length x w = α := by simp [cnt, hxw, hαdef]
    have h1 := pw_ub Ms hM x w
    rw [hc] at h1
    exact h1
  have cellb : ∀ k : Fin 6,
      (α : ℝ) ^ α * gcell Ms a (offPair k).1 (tr a (offPair k).2)
        ≤ pw Ms (offPair k).1 (tr a (offPair k).2) ^ α ∧
      0 ≤ gcell Ms a (offPair k).1 (tr a (offPair k).2) := by
    intro k
    by_cases hxw : (offPair k).1 = tr a (offPair k).2
    · rw [← hxw]
      rcases tr_diag a _ _ (offPair_ne k).symm hxw.symm with hx | hx
      · have e : gcell Ms a (offPair k).1 (offPair k).1
            = wgp Ms (offPair k).1 (offPair k).1 / alt true Ms (offPair k).1 := by
          simp [gcell, hx]
        rw [e]
        exact ⟨big true _, div_nonneg (hg _ _) (alt_nonneg true Ms hM _)⟩
      · have hne : (offPair k).1 ≠ a := by
          rw [hx]
          exact (add_one_ne a).symm
        have e : gcell Ms a (offPair k).1 (offPair k).1
            = wgp Ms (offPair k).1 (offPair k).1 / alt false Ms (offPair k).1 := by
          simp [gcell, hne]
        rw [e]
        exact ⟨big false _, div_nonneg (hg _ _) (alt_nonneg false Ms hM _)⟩
    · have e : gcell Ms a (offPair k).1 (tr a (offPair k).2)
          = wgp Ms (offPair k).1 (tr a (offPair k).2) := by
        simp [gcell, hxw]
      rw [e]
      exact ⟨small _ _ hxw, hg _ _⟩
  have hbal : ∏ k : Fin 6, gcell Ms a (offPair k).1 (tr a (offPair k).2) = up Ms α := by
    rw [prod_tr a (gcell Ms a), ← Og_eq Ms, Og_tr Ms a]
    have hA1 := alt_pos true Ms hMpos a
    have hA2 := alt_pos false Ms hMpos (a + 1)
    have i := (alt_bal Ms a).1 hlen
    have e1 : gcell Ms a a a = wgp Ms a a / alt true Ms a := by simp [gcell]
    have e2 : gcell Ms a (a + 1) (a + 1) = wgp Ms (a + 1) (a + 1) / alt false Ms (a + 1) := by
      simp [gcell, (add_one_ne a).symm]
    have e3 : gcell Ms a (a + 2) a = wgp Ms (a + 2) a := by
      simp [gcell, (add_two_ne a).symm]
    have e4 : gcell Ms a (a + 2) (a + 1) = wgp Ms (a + 2) (a + 1) := by
      have : a + 2 ≠ a + 1 := by fin_cases a <;> decide
      simp [gcell, this]
    have e5 : gcell Ms a a (a + 2) = wgp Ms a (a + 2) := by simp [gcell, add_two_ne a]
    have e6 : gcell Ms a (a + 1) (a + 2) = wgp Ms (a + 1) (a + 2) := by
      have : a + 1 ≠ a + 2 := by fin_cases a <;> decide
      simp [gcell, this]
    rw [e1, e2, e3, e4, e5, e6]
    field_simp
    linear_combination (wgp Ms (a + 2) a * wgp Ms (a + 2) (a + 1) * wgp Ms a (a + 2)
      * wgp Ms (a + 1) (a + 2)) * i
  rw [mul_pow]
  refine hex_assembly hα (p := fun k => pw Ms (offPair k).1 (tr a (offPair k).2))
    (Γ := fun k => gcell Ms a (offPair k).1 (tr a (offPair k).2)) (U := up Ms 1)
    (fun k => hp _ _) (fun k => (cellb k).2) (fun k => (cellb k).1) ?_
    (pow_nonneg (List.prod_nonneg fun A hA' => (hA A hA').le) _)
    (up_one_ge hhex hM fun A hA' => (hA A hA').le)
  rw [hbal, ← up_mul, one_mul]

/-- A family made of the three closed cells and a bijection triple `T`. -/
theorem rot_hex (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (h : ℕ) (hh : 2 ≤ h)
    (hlen : Ms.length = h + h) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hhex : List.Forall₂ OffHex Ms As) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up Ms 1 ≤ T ^ 2) :
    ((dN Ms.length : ℝ) * As.prod) ^ 6 ≤ Dp Ms * T := by
  obtain ⟨M, Ms', rfl⟩ : ∃ M Ms', Ms = M :: Ms' := by
    cases Ms with
    | nil => simp at hlen; omega
    | cons M L => exact ⟨M, L, rfl⟩
  have hD := Dp_sq M Ms' hM
  have hlen' : Ms'.length + 1 = h + h := by simpa using hlen
  rw [hlen'] at hD
  rw [List.length_cons, hlen']
  set α : ℝ := (dN (h + h) : ℝ) with hαdef
  set s : ℝ := (sN (h + h) : ℝ) with hsdef
  set K : ℝ := (27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4 with hKdef
  set U := up (M :: Ms') 1 with hUdef
  have hU0 : 0 ≤ U := up_nonneg _ hM 1
  have hK0 : 0 ≤ K := by positivity
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hα0 : 0 ≤ α := Nat.cast_nonneg _
  have hDp0 : 0 ≤ Dp (M :: Ms') := Dp_nonneg _ hM
  -- `(Dp T)² ≥ (s³ K U)²`
  have hsq : (s ^ 3 * K * U) ^ 2 ≤ (Dp (M :: Ms') * T) ^ 2 := by
    calc (s ^ 3 * K * U) ^ 2 = (s ^ 6 * U) * (K ^ 2 * U) := by ring
      _ ≤ Dp (M :: Ms') ^ 2 * T ^ 2 :=
          mul_le_mul hD hT (by positivity) (sq_nonneg _)
      _ = _ := by ring
  have h1 : s ^ 3 * K * U ≤ Dp (M :: Ms') * T :=
    (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hDp0 hT0) (by norm_num)).mp hsq
  -- the constant
  have hwn : α ^ 5 ≤ s ^ 2 * K := by
    have := walk_num h hh
    rw [hαdef, hsdef, hKdef]
    exact_mod_cast this
  have hαs : α ≤ s := by
    have := (sN_dN_parity (h + h)).1 ⟨h, rfl⟩
    rw [hαdef, hsdef, this]
    push_cast
    linarith
  have hconst : α ^ 6 ≤ s ^ 3 * K := by
    calc α ^ 6 = α * α ^ 5 := by ring
      _ ≤ s * (s ^ 2 * K) := mul_le_mul hαs hwn (pow_nonneg hα0 _) hs0
      _ = s ^ 3 * K := by ring
  have hB := up_one_ge hhex hM fun A hA' => (hA A hA').le
  rw [← hUdef] at hB
  calc (α * As.prod) ^ 6 = α ^ 6 * As.prod ^ 6 := mul_pow _ _ _
    _ ≤ (s ^ 3 * K) * U := mul_le_mul hconst hB
        (pow_nonneg (List.prod_nonneg fun A hA' => (hA A hA').le) _) (by positivity)
    _ ≤ _ := h1

/-- **The hexagon bound of a path of `h + h` steps, `h ≥ 2`**, for the six cells `(a, σ b)`,
`a ≠ b`, of any bijection `σ`. -/
theorem walks_hex (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (h : ℕ) (hh : 2 ≤ h)
    (hlen : Ms.length = h + h) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hhex : List.Forall₂ OffHex Ms As) (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ) :
    ((dN Ms.length : ℝ) * As.prod) ^ 6 ≤ ∏ k, pw Ms (offPair k).1 (σ (offPair k).2) := by
  have hev : Even Ms.length := ⟨h, hlen⟩
  have hpos : 0 < Ms.length := by omega
  have hp := pw_nonneg Ms hM
  rcases inj_cases σ hσ with rfl | rfl | rfl | ⟨a, rfl⟩
  · exact walks_hex_id Ms As hpos hM hA hhex
  · have e : ∏ k, pw Ms (offPair k).1 ((offPair k).2 + 1) = Dp Ms * T₂ Ms := by
      simp [Fin.prod_univ_six, offPair, Dp, T₂]
      ring
    rw [e]
    exact rot_hex Ms As h hh hlen hM hA hhex (mul_nonneg (mul_nonneg (hp _ _) (hp _ _)) (hp _ _))
      (halves Ms h hh hlen hM).2
  · have e : ∏ k, pw Ms (offPair k).1 ((offPair k).2 + 2) = Dp Ms * T₁ Ms := by
      simp [Fin.prod_univ_six, offPair, Dp, T₁]
      ring
    rw [e]
    exact rot_hex Ms As h hh hlen hM hA hhex (mul_nonneg (mul_nonneg (hp _ _) (hp _ _)) (hp _ _))
      (halves Ms h hh hlen hM).1
  · exact walks_hex_tr Ms As hev hpos hM hA hhex a

/-! ### Between lists and indices -/

/-- The hexagon class read through aligned enumerations of the two lists. -/
theorem Hex.offHex {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (h : Hex S T W A)
    {ζ ξ : Fin 3 → ℕ} (hζ : Function.Injective ζ) (hξ : Function.Injective ξ)
    (hζm : ∀ a, ζ a ∈ S) (hξm : ∀ b, ξ b ∈ T) (hal : ∀ a b, ζ a = ξ b → a = b) :
    OffHex (idxM W ζ ξ) A :=
  h _ _ (matched_of_enum hζ hξ hζm hξm) fun i e => offPair_ne i (hal _ _ e)

/-- The hexagon class at a root edge from its index form. -/
theorem hex_of_idx {Lu Lv : Finset ℕ} {F : ℕ → ℕ → ℝ} {A : ℝ}
    (h : ∀ α β : Fin 3 → ℕ, Function.Injective α → Function.Injective β → (∀ a, α a ∈ Lu) →
      (∀ b, β b ∈ Lv) → (∀ a b, α a = β b → a = b) →
      A ^ 6 ≤ ∏ k, F (α (offPair k).1) (β (offPair k).2)) :
    Hex Lu Lv F A := by
  intro p q hm hpq
  obtain ⟨α, β, hα, hβ, hαm, hβm, hab⟩ := hm
  have hal : ∀ a b, α a = β b → a = b := by
    intro a b e
    by_contra hne
    obtain ⟨i, hi1, hi2⟩ := hab a b hne
    exact hpq i (by rw [hi1, hi2, e])
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  have e : ∏ i, F (p i) (q i) = ∏ k, F (α (offPair k).1) (β (offPair k).2) := by
    rw [← hκb.prod_comp fun i => F (p i) (q i)]
    exact Finset.prod_congr rfl fun k _ => by rw [(hκ k).1, (hκ k).2]
  rw [e]
  exact h α β hα hβ hαm hβm hal

/-- The hexagon class on every edge of a path, in the form of lists. -/
def ChainHex : Finset ℕ → List (Finset ℕ) → List (ℕ → ℕ → ℝ) → List ℝ → Prop
  | _, [], [], [] => True
  | S, L :: Vs, E :: Es, A :: As => Hex S L E A ∧ ChainHex L Vs Es As
  | _, _, _, _ => False

theorem chainHex_of_fin : ∀ {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (A : Fin (m + 1) → ℝ),
    (∀ j : Fin (m + 1),
      Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) →
    ChainHex Lu (List.ofFn Li ++ [Lv]) (List.ofFn E) (List.ofFn A)
  | 0, Lu, Lv, Li, E, A, h => by
    have h0 := h 0
    have p0 : pathList Lu Lv Li (Fin.castSucc (0 : Fin 1)) = Lu :=
      consSnoc_zero _ _ _ _ (by simp)
    have p1 : pathList Lu Lv Li (Fin.succ (0 : Fin 1)) = Lv := consSnoc_last _ _ _ _ (by simp)
    rw [p0, p1] at h0
    simp only [List.ofFn_succ, List.ofFn_zero, List.nil_append]
    exact ⟨h0, trivial⟩
  | m + 1, Lu, Lv, Li, E, A, h => by
    have h0 := h 0
    have p0 : pathList Lu Lv Li (Fin.castSucc (0 : Fin (m + 2))) = Lu :=
      consSnoc_zero _ _ _ _ (by simp)
    have p1 : pathList Lu Lv Li (Fin.succ (0 : Fin (m + 2))) = Li 0 :=
      consSnoc_mid _ _ _ _ (0 : Fin (m + 1)) (by simp)
    rw [p0, p1] at h0
    have ih := chainHex_of_fin (Li 0) Lv (Fin.tail Li) (Fin.tail E) (Fin.tail A) (fun j => by
      have hj := h j.succ
      have e1 : (j.succ : Fin (m + 2)).castSucc = (j.castSucc).succ := rfl
      rw [e1, pathList_tail, pathList_tail] at hj
      exact hj)
    rw [List.ofFn_succ (f := Li), List.ofFn_succ (f := E), List.ofFn_succ (f := A)]
    exact ⟨h0, ih⟩

/-- Enumerations along a path with the hexagon class on every edge. -/
theorem framesHex : ∀ (Vs : List (Finset ℕ)) (Es : List (ℕ → ℕ → ℝ)) (As : List ℝ)
    (S : Finset ℕ) (ζ₀ : Fin 3 → ℕ), Function.Injective ζ₀ → (∀ a, ζ₀ a ∈ S) →
    (∀ L ∈ Vs, L.card = 3) → (∀ E ∈ Es, ∀ c d, 0 ≤ E c d) → ChainHex S Vs Es As →
    ∃ ζs : List (Fin 3 → ℕ),
      List.Forall₂ (fun (ζ : Fin 3 → ℕ) (L : Finset ℕ) => Function.Injective ζ ∧ ∀ a, ζ a ∈ L)
        ζs Vs ∧
      List.Forall₂ OffHex (mkMs ζ₀ ζs Es) As ∧ ∀ M ∈ mkMs ζ₀ ζs Es, ∀ a b, 0 ≤ M a b
  | [], [], [], _, _, _, _, _, _, _ => ⟨[], List.Forall₂.nil, List.Forall₂.nil, by simp [mkMs]⟩
  | [], [], _ :: _, _, _, _, _, _, _, h => absurd h (by simp [ChainHex])
  | [], _ :: _, _, _, _, _, _, _, _, h => absurd h (by simp [ChainHex])
  | _ :: _, [], _, _, _, _, _, _, _, h => absurd h (by simp [ChainHex])
  | _ :: _, _ :: _, [], _, _, _, _, _, _, h => absurd h (by simp [ChainHex])
  | L :: Vs, E :: Es, A :: As, S, ζ₀, hζ₀, hζ₀m, hV, hE0, h => by
    obtain ⟨hE, hrest⟩ := h
    obtain ⟨ξ, hξ, hξm, hal'⟩ := exists_aligned (hV L List.mem_cons_self) hζ₀
    have hal : ∀ a b, ζ₀ a = ξ b → a = b := fun a b e => hal' b a e.symm
    obtain ⟨ζs, h1, h2, h3⟩ := framesHex Vs Es As L ξ hξ hξm
      (fun L' hL' => hV L' (List.mem_cons_of_mem _ hL'))
      (fun E' hE' => hE0 E' (List.mem_cons_of_mem _ hE')) hrest
    refine ⟨ξ :: ζs, List.Forall₂.cons ⟨hξ, hξm⟩ h1, ?_, ?_⟩
    · rw [mkMs]
      exact List.Forall₂.cons (hE.offHex hζ₀ hξ hζ₀m hξm hal) h2
    · intro M hM a b
      rw [mkMs] at hM
      rcases List.mem_cons.mp hM with rfl | hM'
      · exact hE0 E List.mem_cons_self _ _
      · exact h3 M hM' a b

/-- **Faces of odd length preserve the hexagon bound with every path edge loaded.** -/
theorem hexOddClosed (m : ℕ) (hodd : Odd m) (h3 : 3 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (_hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  refine hex_of_idx fun α β hα hβ hαm hβm _ => ?_
  set Vs := List.ofFn Li ++ [Lv] with hVs
  have hVcard : ∀ L ∈ Vs, L.card = 3 := by
    intro L hL
    rcases List.mem_append.mp hL with h | h
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp h
      exact hLi i
    · rw [List.mem_singleton.mp h]
      exact hLv
  have hEs0 : ∀ E' ∈ List.ofFn E, ∀ c d, 0 ≤ E' c d := by
    intro E' hE' c d
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hE'
    exact hE0 i c d
  have hAs : ∀ A' ∈ List.ofFn A, 0 < A' := by
    intro A' hA'
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hA'
    exact hA i
  obtain ⟨ζs, hζs, hOff, hMnn⟩ := framesHex Vs (List.ofFn E) (List.ofFn A) Lu α hα hαm hVcard
    hEs0 (chainHex_of_fin Lu Lv Li E A hE)
  have hlenV : Vs.length = m + 1 := by simp [hVs]
  have hlenE : (List.ofFn E).length = m + 1 := List.length_ofFn
  have hlenζ : ζs.length = m + 1 := by rw [hζs.length_eq, hlenV]
  set Ms := mkMs α ζs (List.ofFn E) with hMs
  have hlenM : Ms.length = m + 1 := by
    rw [hMs, mkMs_length _ _ _ (by rw [hlenζ, hlenE]), hlenE]
  have hend : Function.Injective (ζs.getLastD α) ∧ ∀ a, (ζs.getLastD α) a ∈ Lv := by
    have h := forall₂_getLastD (P := fun ζ L => Function.Injective ζ ∧ ∀ a, ζ a ∈ L) ζs Vs α Lu
      hζs ⟨hα, hαm⟩
    have e : Vs.getLastD Lu = Lv := by
      rw [hVs, getLastD_append]
      rfl
    rwa [e] at h
  have himg : ∀ b, ∃ x, (ζs.getLastD α) x = β b := fun b => by
    have hb : β b ∈ univ.image (ζs.getLastD α) := by
      rw [image_enum hLv hend.1 hend.2]
      exact hβm b
    obtain ⟨x, -, hx⟩ := mem_image.mp hb
    exact ⟨x, hx⟩
  choose σ hσ using himg
  have hσinj : Function.Injective σ := fun b b' e => hβ (by rw [← hσ b, ← hσ b', e])
  obtain ⟨r, hr⟩ := hodd
  have key := walks_hex Ms (List.ofFn A) (r + 1) (by omega) (by rw [hlenM]; omega) hMnn hAs hOff
    σ hσinj
  have hp := pw_nonneg Ms hMnn
  have hcell : ∀ a b : Fin 3, pw Ms a (σ b) ≤ faceSum Li (fun _ _ => 1) E (α a) (β b) :=
    fun a b => by
      rw [faceSum_eq_psum Li Lv E (α a) (β b) (hβm b), ← hσ b]
      exact pw_le_psum Vs (List.ofFn E) ζs α (by rw [hlenE, hlenV]) hζs hEs0 a (σ b)
  calc (faceConst3 m * ∏ j, A j) ^ 6
      = ((dN Ms.length : ℝ) * (List.ofFn A).prod) ^ 6 := by
        rw [hlenM, ← faceConst3_eq_dN, List.prod_ofFn]
    _ ≤ ∏ k, pw Ms (offPair k).1 (σ (offPair k).2) := key
    _ ≤ _ := Finset.prod_le_prod₀ (fun k _ => hp _ _) fun k _ => hcell _ _

end Outerplanar
