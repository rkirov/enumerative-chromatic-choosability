/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Arms
import Outerplanar.SquareCert

/-!
# Chains of aligned enumerations along an arm

Along a stretch of ordinary edges, enumerate each list so that a colour shared with the previous
list keeps its index (`Chain`). The stretch is then described by its *codes*: for each edge, the
set of indices whose colours agree at its two ends. The number of proper colourings of the stretch
with given end colours is at least the corresponding entry of the *chain matrix*
`chainM ds = N_{d₁} ⋯ N_{dₙ}`, `N_d = J - diag d` (`Chain.count_ge`).

The conditions of the three rules of `Outerplanar/Arms.lean` follow from conditions on codes
(`cutCode`, `sh1Code`, `sh0Code`), which are decidable: `Chain.cut`, `Chain.sh1`, `Chain.sh0`.
-/

namespace Outerplanar

open Finset

/-! ### Chain matrices -/

/-- The matrix of an ordinary edge with code `d`: no colouring at an index with equal colours. -/
def nMat (d : Fin 3 → Bool) (x y : Fin 3) : ℕ := if x = y ∧ d x = true then 0 else 1

/-- The product of two `3 × 3` matrices. -/
def mmul (A B : Fin 3 → Fin 3 → ℕ) (x y : Fin 3) : ℕ := A x 0 * B 0 y + A x 1 * B 1 y + A x 2 * B 2 y

/-- The chain matrix of a list of codes. -/
def chainM : List (Fin 3 → Bool) → Fin 3 → Fin 3 → ℕ
  | [] => fun x y => if x = y then 1 else 0
  | d :: ds => mmul (nMat d) (chainM ds)

/-- The code of an edge between equal lists. -/
def fullCode : Fin 3 → Bool := fun _ => true

/-- The chain matrix of `s` edges between equal lists: the number of walks of length `s` in the
triangle. -/
def dMat (s : ℕ) : Fin 3 → Fin 3 → ℕ := chainM (List.replicate s fullCode)

theorem nMat_full_le (d : Fin 3 → Bool) (x y : Fin 3) : nMat fullCode x y ≤ nMat d x y := by
  unfold nMat fullCode
  split_ifs <;> simp_all

theorem mmul_mono {A A' B B' : Fin 3 → Fin 3 → ℕ} (hA : ∀ x y, A x y ≤ A' x y)
    (hB : ∀ x y, B x y ≤ B' x y) (x y : Fin 3) : mmul A B x y ≤ mmul A' B' x y :=
  Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul (hA _ _) (hB _ _))
    (Nat.mul_le_mul (hA _ _) (hB _ _))) (Nat.mul_le_mul (hA _ _) (hB _ _))

/-- Any chain matrix is at least the matrix of walks in the triangle. -/
theorem dMat_le_chainM : ∀ (ds : List (Fin 3 → Bool)) (x y : Fin 3),
    dMat ds.length x y ≤ chainM ds x y
  | [], _, _ => le_rfl
  | d :: ds, x, y => mmul_mono (nMat_full_le d) (dMat_le_chainM ds) x y

/-- The matrix of walks depends on whether the two ends agree. -/
theorem dMat_two_valued : ∀ s : ℕ, ∃ p q : ℕ, ∀ x y : Fin 3, dMat s x y = if x = y then p else q
  | 0 => ⟨1, 0, fun _ _ => rfl⟩
  | s + 1 => by
    obtain ⟨p, q, h⟩ := dMat_two_valued s
    refine ⟨2 * q, p + q, fun x y => ?_⟩
    show mmul (nMat fullCode) (dMat s) x y = _
    unfold mmul nMat fullCode
    simp only [h]
    fin_cases x <;> fin_cases y <;> simp <;> omega

theorem dMat_perm (s : ℕ) {τ : Fin 3 → Fin 3} (hτ : Function.Injective τ) (x y : Fin 3) :
    dMat s (τ x) (τ y) = dMat s x y := by
  obtain ⟨p, q, h⟩ := dMat_two_valued s
  rw [h, h]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy, ite_eq_left (by rw [hxy])]
  · rw [ite_eq_right hxy, ite_eq_right fun e => hxy (hτ e)]

/-! ### Chains -/

/-- `Chain ζ U ds ζ'`: starting from the enumeration `ζ`, the lists of `U` carry enumerations,
each aligned with the previous one; `ds` are the codes of the edges and `ζ'` is the enumeration of
the last list. -/
inductive Chain : (Fin 3 → ℕ) → List (Finset ℕ) → List (Fin 3 → Bool) → (Fin 3 → ℕ) → Prop
  | nil (ζ : Fin 3 → ℕ) : Chain ζ [] [] ζ
  | cons {ζ ζ₁ ζ' : Fin 3 → ℕ} {L : Finset ℕ} {U : List (Finset ℕ)} {ds : List (Fin 3 → Bool)}
      (hL : L.card = 3) (hinj : Function.Injective ζ₁) (hmem : ∀ i, ζ₁ i ∈ L)
      (hal : ∀ c a, ζ₁ c = ζ a → a = c) (h : Chain ζ₁ U ds ζ') :
      Chain ζ (L :: U) ((fun x => decide (ζ x = ζ₁ x)) :: ds) ζ'

theorem exists_chain : ∀ (U : List (Finset ℕ)), (∀ L ∈ U, L.card = 3) → ∀ ζ : Fin 3 → ℕ,
    Function.Injective ζ → ∃ ds ζ', Chain ζ U ds ζ'
  | [], _, ζ, _ => ⟨[], ζ, Chain.nil ζ⟩
  | L :: U, hU, ζ, hζ => by
    obtain ⟨ζ₁, hζ₁, hm₁, hal⟩ := exists_aligned (hU L List.mem_cons_self) hζ
    obtain ⟨ds, ζ', hc⟩ := exists_chain U (fun L' hL' => hU L' (List.mem_cons_of_mem _ hL')) ζ₁ hζ₁
    exact ⟨_, ζ', Chain.cons (hU L List.mem_cons_self) hζ₁ hm₁ hal hc⟩

variable {ζ ζ' : Fin 3 → ℕ} {U : List (Finset ℕ)} {ds : List (Fin 3 → Bool)}

theorem Chain.length (h : Chain ζ U ds ζ') : ds.length = U.length := by
  induction h with
  | nil ζ => rfl
  | cons _ _ _ _ _ ih => simp [ih]

theorem Chain.injective (h : Chain ζ U ds ζ') (hζ : Function.Injective ζ) :
    Function.Injective ζ' := by
  induction h with
  | nil ζ => exact hζ
  | cons _ hinj _ _ _ ih => exact ih hinj

theorem Chain.mem (h : Chain ζ U ds ζ') {X : Finset ℕ} (hζ : ∀ i, ζ i ∈ X) :
    ∀ i, ζ' i ∈ U.getLastD X := by
  induction h generalizing X with
  | nil ζ => exact hζ
  | cons _ _ hmem _ _ ih =>
    rw [getLastD_cons]
    exact ih hmem

theorem Chain.cards (h : Chain ζ U ds ζ') : ∀ L ∈ U, L.card = 3 := by
  induction h with
  | nil ζ => intro L hL; cases hL
  | cons hL _ _ _ _ ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | h'
    · exact hL
    · exact ih L' h'

/-- Indices whose colours agree on every edge have the same colour at both ends. -/
theorem Chain.forced (h : Chain ζ U ds ζ') (a : Fin 3) (ha : ∀ d ∈ ds, d a = true) :
    ζ a = ζ' a := by
  induction h with
  | nil ζ => rfl
  | cons _ _ _ _ _ ih =>
    have h1 := ha _ List.mem_cons_self
    rw [of_decide_eq_true h1]
    exact ih fun d hd => ha d (List.mem_cons_of_mem _ hd)

/-- **The number of colourings of a stretch is at least the entry of its chain matrix.** -/
theorem Chain.count_ge (h : Chain ζ U ds ζ') (a y : Fin 3) :
    ((chainM ds a y : ℕ) : ℝ) ≤ psum U (nes U.length) (ζ a) (ζ' y) := by
  induction h generalizing a with
  | nil ζ =>
    show (((if a = y then 1 else 0 : ℕ)) : ℝ) ≤ psum [] (nes 0) (ζ a) (ζ y)
    rw [psum_nil]
    by_cases hay : a = y
    · rw [ite_eq_left hay, ite_eq_left (by rw [hay])]
      norm_num
    · rw [ite_eq_right hay]
      split_ifs <;> norm_num
  | @cons ζ ζ₁ ζ' L U ds hL hinj hmem hal _ ih =>
    show ((mmul (nMat fun x => decide (ζ x = ζ₁ x)) (chainM ds) a y : ℕ) : ℝ)
      ≤ psum (L :: U) (neP :: nes U.length) (ζ a) (ζ' y)
    rw [psum_cons, sum_enum hL hinj hmem (fun x => neP (ζ a) x * psum U (nes U.length) x (ζ' y)),
      Fin.sum_univ_three]
    have hterm : ∀ i : Fin 3, ((nMat (fun x => decide (ζ x = ζ₁ x)) a i * chainM ds i y : ℕ) : ℝ)
        ≤ neP (ζ a) (ζ₁ i) * psum U (nes U.length) (ζ₁ i) (ζ' y) := fun i => by
      have hne : ((nMat (fun x => decide (ζ x = ζ₁ x)) a i : ℕ) : ℝ) = neP (ζ a) (ζ₁ i) := by
        show (((if a = i ∧ decide (ζ a = ζ₁ a) = true then 0 else 1 : ℕ)) : ℝ)
          = if ζ a ≠ ζ₁ i then 1 else 0
        by_cases hai : ζ a = ζ₁ i
        · obtain rfl := hal i a hai.symm
          rw [ite_eq_left ⟨rfl, decide_eq_true hai⟩, ite_eq_right (not_not.mpr hai), Nat.cast_zero]
        · have hn : ¬ (a = i ∧ decide (ζ a = ζ₁ a) = true) := fun ⟨e, h'⟩ =>
            hai (by rw [← e]; exact of_decide_eq_true h')
          rw [ite_eq_right hn, ite_eq_left hai, Nat.cast_one]
      rw [Nat.cast_mul, hne]
      exact mul_le_mul_of_nonneg_left (ih i) (neP_nonneg _ _)
    have := add_le_add (add_le_add (hterm 0) (hterm 1)) (hterm 2)
    unfold mmul
    push_cast at this ⊢
    exact this

/-- Splitting a chain. -/
theorem Chain.split : ∀ {A B : List (Finset ℕ)} {ζ ζ' : Fin 3 → ℕ} {ds : List (Fin 3 → Bool)},
    Chain ζ (A ++ B) ds ζ' →
    ∃ ζm dA dB, ds = dA ++ dB ∧ Chain ζ A dA ζm ∧ Chain ζm B dB ζ'
  | [], B, ζ, ζ', ds, h => ⟨ζ, [], ds, rfl, Chain.nil ζ, h⟩
  | L :: A, B, ζ, ζ', ds, h => by
    cases h with
    | cons hL hinj hmem hal h' =>
      obtain ⟨ζm, dA, dB, rfl, hA, hB⟩ := Chain.split h'
      exact ⟨ζm, _ :: dA, dB, rfl, Chain.cons hL hinj hmem hal hA, hB⟩

/-! ### Conditions on codes -/

/-- `p x y` for all `x`, `y`. -/
def all3F2 (p : Fin 3 → Fin 3 → Bool) : Bool := all3F fun x => all3F fun y => p x y

theorem all3F2_apply {p : Fin 3 → Fin 3 → Bool} (h : all3F2 p = true) (x y : Fin 3) :
    p x y = true := all3F_apply (all3F_apply h x) y

/-- The condition of the cut rule on the codes of a stretch. -/
def cutCode (ds : List (Fin 3 → Bool)) : Bool :=
  all3F2 fun x y => decide (2 ^ ds.length + 1 ≤ 3 * chainM ds x y)

/-- The condition for replacing a stretch of three edges by one edge. -/
def sh1Code : List (Fin 3 → Bool) → Bool
  | [d₁, d₂, d₃] => all3F2 fun x y =>
      decide ((if x = y ∧ d₁ x = true ∧ d₂ x = true ∧ d₃ x = true then 2 else 3)
        ≤ chainM [d₁, d₂, d₃] x y)
  | _ => false

/-- The condition for contracting a stretch of two edges: three equal lists. -/
def sh0Code : List (Fin 3 → Bool) → Bool
  | [d₁, d₂] => all3F fun x => d₁ x && d₂ x
  | _ => false

theorem chainM_full_two : ∀ a y : Fin 3,
    chainM [fullCode, fullCode] a y = (if a = y then 1 else 0) + 1 := by decide

/-- A colour of the first list of a chain, as an index. -/
theorem exists_idx {X : Finset ℕ} (hX : X.card = 3) (hζ : Function.Injective ζ)
    (hm : ∀ i, ζ i ∈ X) {x : ℕ} (hx : x ∈ X) : ∃ a, ζ a = x := by
  rw [← image_enum hX hζ hm] at hx
  obtain ⟨a, -, ha⟩ := mem_image.mp hx
  exact ⟨a, ha⟩

/-- **The cut rule from codes.** -/
theorem Chain.cut {X : Finset ℕ} (h : Chain ζ U ds ζ') (hX : X.card = 3)
    (hζ : Function.Injective ζ) (hm : ∀ i, ζ i ∈ X) (hcode : cutCode ds = true) :
    ∃ b : ℕ, 2 ^ U.length + 1 ≤ 3 * b ∧
      ∀ x ∈ X, ∀ z ∈ U.getLastD X, (b : ℝ) ≤ psum U (nes U.length) x z := by
  refine ⟨(2 ^ U.length + 1 + 2) / 3, by omega, fun x hx z hz => ?_⟩
  obtain ⟨a, rfl⟩ := exists_idx hX hζ hm hx
  obtain ⟨y, rfl⟩ := exists_idx (card_getLastD hX h.cards) (h.injective hζ) (h.mem hm) hz
  have h1 := of_decide_eq_true (all3F2_apply hcode a y)
  rw [h.length] at h1
  have h2 : (2 ^ U.length + 1 + 2) / 3 ≤ chainM ds a y := by omega
  exact (Nat.cast_le.mpr h2).trans (h.count_ge a y)

/-- **Replacing three edges by one, from codes.** -/
theorem Chain.sh1 {X Y₁ Y₂ Z : Finset ℕ} (h : Chain ζ [Y₁, Y₂, Z] ds ζ') (hX : X.card = 3)
    (hζ : Function.Injective ζ) (hm : ∀ i, ζ i ∈ X) (hcode : sh1Code ds = true) :
    ∀ x ∈ X, ∀ z ∈ Z, neP x z + 2 ≤ psum [Y₁, Y₂, Z] (nes 3) x z := by
  have hlen := h.length
  obtain ⟨d₁, d₂, d₃, rfl⟩ : ∃ d₁ d₂ d₃, ds = [d₁, d₂, d₃] := by
    match ds, hlen with
    | [d₁, d₂, d₃], _ => exact ⟨d₁, d₂, d₃, rfl⟩
  intro x hx z hz
  obtain ⟨a, rfl⟩ := exists_idx hX hζ hm hx
  have hZ : Z.card = 3 := h.cards Z (by simp)
  obtain ⟨y, rfl⟩ := exists_idx hZ (h.injective hζ) (h.mem (X := X) hm) hz
  have h1 := of_decide_eq_true (all3F2_apply hcode a y)
  have h2 := h.count_ge a y
  have h3 : neP (ζ a) (ζ' y) + 2
      ≤ (((if a = y ∧ d₁ a = true ∧ d₂ a = true ∧ d₃ a = true then 2 else 3 : ℕ)) : ℝ) := by
    by_cases hc : a = y ∧ d₁ a = true ∧ d₂ a = true ∧ d₃ a = true
    · rw [ite_eq_left hc]
      obtain ⟨rfl, e1, e2, e3⟩ := hc
      have hf := h.forced a fun d hd => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl <;> assumption
      unfold neP
      rw [ite_eq_right (not_not.mpr hf)]
      norm_num
    · rw [ite_eq_right hc]
      unfold neP
      split_ifs <;> norm_num
  exact h3.trans ((Nat.cast_le.mpr h1).trans h2)

/-- **Contracting two edges, from codes.** -/
theorem Chain.sh0 {X Y Z : Finset ℕ} (h : Chain ζ [Y, Z] ds ζ') (hX : X.card = 3)
    (hζ : Function.Injective ζ) (hm : ∀ i, ζ i ∈ X) (hcode : sh0Code ds = true) :
    X = Z ∧ ∀ x ∈ Z, ∀ z ∈ Z, (if x = z then (1 : ℝ) else 0) + 1 ≤ psum [Y, Z] (nes 2) x z := by
  have hlen := h.length
  obtain ⟨d₁, d₂, rfl⟩ : ∃ d₁ d₂, ds = [d₁, d₂] := by
    match ds, hlen with
    | [d₁, d₂], _ => exact ⟨d₁, d₂, rfl⟩
  have hc : all3F (fun x => d₁ x && d₂ x) = true := hcode
  have hfull : ∀ a, d₁ a = true ∧ d₂ a = true := fun a =>
    Bool.and_eq_true_iff.mp (all3F_apply hc a)
  have hZ : Z.card = 3 := h.cards Z (by simp)
  have hm' : ∀ i, ζ' i ∈ Z := h.mem (X := X) hm
  have heq : ∀ a, ζ a = ζ' a := fun a => h.forced a fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact (hfull a).1
    · exact (hfull a).2
  have hXZ : X = Z := by
    rw [← image_enum hX hζ hm, ← image_enum hZ (h.injective hζ) hm']
    exact Finset.image_congr fun a _ => heq a
  refine ⟨hXZ, fun x hx z hz => ?_⟩
  obtain ⟨a, rfl⟩ := exists_idx hX hζ hm (hXZ ▸ hx)
  obtain ⟨y, rfl⟩ := exists_idx hZ (h.injective hζ) hm' hz
  have h2 := h.count_ge a y
  have h3 : (if ζ a = ζ' y then (1 : ℝ) else 0) + 1 ≤ ((chainM [d₁, d₂] a y : ℕ) : ℝ) := by
    have hM : chainM [d₁, d₂] a y = (if a = y then 1 else 0) + 1 := by
      have e1 : d₁ = fullCode := funext fun i => (hfull i).1
      have e2 : d₂ = fullCode := funext fun i => (hfull i).2
      rw [e1, e2]
      exact chainM_full_two a y
    rw [hM]
    by_cases hay : a = y
    · rw [ite_eq_left hay, ite_eq_left (by rw [heq a, hay])]
      norm_num
    · rw [ite_eq_right hay, ite_eq_right fun e => hay (hζ (by rw [heq y]; exact e))]
      norm_num
  exact h3.trans h2

end Outerplanar
