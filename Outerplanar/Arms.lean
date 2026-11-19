/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.PathSum

/-!
# A face with one loaded edge, as two arms; the reduction rules

A face with one loaded edge `S T` is described from the loaded edge outwards: `U₁` are the lists
of the vertices after `S` on the way to the root end `u` (the last one is the list of `u`), `U₂`
those after `T` on the way to `v`. Its profile is

`armF S U₁ T U₂ W c d = ∑ s ∈ S, ∑ t ∈ T, (paths s → c) * W s t * (paths t → d)`.

`FaceOK S U₁ T U₂` says that the face maps the ball class to the ball class with the constant
`faceConst3` of its number of interior vertices. The description is symmetric (`FaceOK.swap`),
so rules are stated for the second arm only. With `U₂ = P ++ Sub ++ R`, where the stretch `Sub`
of ordinary edges starts at the last list `X` of `T :: P`:

* `faceOK_cut` — if `Sub` has at least `b` proper colourings for all colours of its ends and
  `2 ^ n + 1 ≤ 3 b`, the face is fine;
* `faceOK_sh1` — if a stretch of three edges has at least `[x ≠ z] + 2` colourings, the face
  follows from the face in which the stretch is replaced by one edge;
* `faceOK_sh0` — if a stretch of two edges between equal lists has at least `[x = z] + 1`
  colourings, the face follows from the face in which the stretch is contracted.
-/

namespace Outerplanar

open Finset

/-! ### Constants -/

theorem faceConst3_add_two (m : ℕ) : faceConst3 (m + 2) = faceConst3 m + 2 ^ (m + 1) := by
  unfold faceConst3
  push_cast
  have h2 : ((3 : ℝ) - 1) = 2 := by norm_num
  rw [h2, show m + 2 + 1 = (m + 1) + 2 from rfl, pow_add, pow_add (-1 : ℝ)]
  ring

theorem faceConst3_le_cut {m n e b : ℕ} (hme : m + 1 = n + e) (hb : 2 ^ n + 1 ≤ 3 * b) :
    faceConst3 m ≤ (b : ℝ) * 2 ^ e := by
  unfold faceConst3
  push_cast
  have h2 : ((3 : ℝ) - 1) = 2 := by norm_num
  rw [h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  have h1 : (2 : ℝ) ^ (m + 1) - (-1) ^ (m + 1) ≤ 2 ^ (m + 1) + 1 := by
    have : (-1 : ℝ) ≤ (-1) ^ (m + 1) := by
      rcases Nat.even_or_odd (m + 1) with he | ho
      · rw [he.neg_one_pow]; norm_num
      · rw [ho.neg_one_pow]
    linarith
  have hb' : (2 : ℝ) ^ n + 1 ≤ 3 * b := by exact_mod_cast hb
  have he1 : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
  calc (2 : ℝ) ^ (m + 1) - (-1) ^ (m + 1) ≤ 2 ^ (m + 1) + 1 := h1
    _ = 2 ^ n * 2 ^ e + 1 := by rw [hme, pow_add]
    _ ≤ (2 ^ n + 1) * 2 ^ e := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
    _ ≤ 3 * b * 2 ^ e := mul_le_mul_of_nonneg_right hb' (by positivity)
    _ = b * 2 ^ e * 3 := by ring

/-! ### Lists -/

theorem getLastD_append {α : Type*} : ∀ (A B : List α) (x : α),
    (A ++ B).getLastD x = B.getLastD (A.getLastD x)
  | [], _, _ => rfl
  | a :: A, B, x => by
    have h1 : ∀ (C : List α) (y : α), (a :: C).getLastD y = C.getLastD a := fun C y => by
      cases C <;> rfl
    rw [List.cons_append, h1, h1, getLastD_append A B a]

theorem getLastD_cons {α : Type*} (a : α) (C : List α) (y : α) :
    (a :: C).getLastD y = C.getLastD a := by
  cases C <;> rfl

theorem eq_nil_or_snoc {α : Type*} (l : List α) : l = [] ∨ ∃ l' a, l = l' ++ [a] := by
  rcases List.eq_nil_or_concat l with h | ⟨l', a, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨l', a, by rw [h, List.concat_eq_append]⟩

theorem card_getLastD {l : List (Finset ℕ)} {X : Finset ℕ} (hX : X.card = 3)
    (hl : ∀ L ∈ l, L.card = 3) : (l.getLastD X).card = 3 := by
  rcases eq_nil_or_snoc l with rfl | ⟨l', Y, rfl⟩
  · exact hX
  · rw [getLastD_append]
    exact hl Y (List.mem_append_right _ List.mem_cons_self)

theorem nes_add (a b : ℕ) : nes (a + b) = nes a ++ nes b := List.replicate_add a b neP

theorem neP_comm (c d : ℕ) : neP c d = neP d c := by
  unfold neP
  simp [eq_comm]

/-- Splitting a path of ordinary edges after a first stretch `P`. -/
theorem psum_split_nes (P B : List (Finset ℕ)) (T : Finset ℕ) {t : ℕ} (ht : t ∈ T) (d : ℕ) :
    psum (P ++ B) (nes (P.length + B.length)) t d
      = ∑ x ∈ P.getLastD T, psum P (nes P.length) t x * psum B (nes B.length) x d := by
  rcases eq_nil_or_snoc P with rfl | ⟨P', X, rfl⟩
  · show psum B (nes (0 + B.length)) t d = ∑ x ∈ T, psum [] (nes 0) t x * psum B (nes B.length) x d
    simp only [psum_nil, zero_add]
    rw [Finset.sum_eq_single t (fun x _ hx => by rw [ite_eq_right (Ne.symm hx), zero_mul])
      (fun h => absurd ht h), ite_eq_left rfl, one_mul]
  · have hl : (P' ++ [X]).getLastD T = X := by rw [getLastD_append]; rfl
    rw [hl, nes_add, List.append_assoc]
    exact psum_append P' X B _ _ (by simp [nes]) t d

/-! ### The two-arm form -/

/-- The profile of a face with loaded edge `S T`, arms `U₁` (towards `u`) and `U₂` (towards
`v`). -/
noncomputable def armF (S : Finset ℕ) (U₁ : List (Finset ℕ)) (T : Finset ℕ)
    (U₂ : List (Finset ℕ)) (W : ℕ → ℕ → ℝ) (c d : ℕ) : ℝ :=
  ∑ s ∈ S, ∑ t ∈ T, psum U₁ (nes U₁.length) s c * W s t * psum U₂ (nes U₂.length) t d

/-- The face with loaded edge `S T` and arms `U₁`, `U₂` maps the ball class to the ball class. -/
def FaceOK (S : Finset ℕ) (U₁ : List (Finset ℕ)) (T : Finset ℕ) (U₂ : List (Finset ℕ)) : Prop :=
  ∀ W : ℕ → ℕ → ℝ, (∀ c d, 0 ≤ W c d) → ∀ A : ℝ, 0 < A → InBall S T W A →
    InBall (U₁.getLastD S) (U₂.getLastD T) (armF S U₁ T U₂ W)
      (faceConst3 (U₁.length + U₂.length) * A)

theorem armF_nonneg {S : Finset ℕ} {U₁ : List (Finset ℕ)} {T : Finset ℕ} {U₂ : List (Finset ℕ)}
    {W : ℕ → ℕ → ℝ} (hW : ∀ c d, 0 ≤ W c d) (c d : ℕ) : 0 ≤ armF S U₁ T U₂ W c d :=
  sum_nonneg fun s _ => sum_nonneg fun t _ =>
    mul_nonneg (mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (hW s t))
      (psum_nonneg _ _ (nes_nonneg _) _ _)

/-- The description is symmetric in the two arms. -/
theorem FaceOK.swap {S : Finset ℕ} {U₁ : List (Finset ℕ)} {T : Finset ℕ} {U₂ : List (Finset ℕ)}
    (h : FaceOK T U₂ S U₁) : FaceOK S U₁ T U₂ := by
  intro W hW A hA hin
  have h1 := (h (fun d c => W c d) (fun d c => hW c d) A hA hin.swap).swap
  rw [Nat.add_comm U₂.length U₁.length] at h1
  have e : (fun c d => armF T U₂ S U₁ (fun d c => W c d) d c) = armF S U₁ T U₂ W := by
    funext c d
    unfold armF
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
  rw [e] at h1
  exact h1

/-! ### Vertex profiles along an arm -/

/-- **A vertex profile carried outwards along ordinary edges**: from the first vertex to the
last one, the constant is multiplied by `2 ^ n`. -/
theorem VBall.transport_fwd : ∀ (U : List (Finset ℕ)) (S : Finset ℕ) {g : ℕ → ℝ} {A : ℝ},
    S.card = 3 → (∀ L ∈ U, L.card = 3) → 0 ≤ A → (∀ c, 0 ≤ g c) → VBall S g A →
    VBall (U.getLastD S) (fun c => ∑ s ∈ S, psum U (nes U.length) s c * g s) (2 ^ U.length * A)
  | [], S, g, A, _, _, _, _, h => by
    rw [List.length_nil, pow_zero, one_mul]
    intro ζ hζ hm
    have hm' : ∀ i, ζ i ∈ S := hm
    have key := h ζ hζ hm'
    have e : ∀ i, (∑ s ∈ S, psum [] (nes 0) s (ζ i) * g s) = g (ζ i) := fun i => by
      simp only [psum_nil]
      rw [Finset.sum_eq_single (ζ i) (fun x _ hx => by rw [ite_eq_right hx, zero_mul])
        (fun hh => absurd (hm' i) hh), ite_eq_left rfl, one_mul]
    show VIdx (fun i => ∑ s ∈ S, psum [] (nes 0) s (ζ i) * g s) A
    simp only [e]
    exact key
  | L :: U, S, g, A, hS, hU, hA, hg, h => by
    rw [getLastD_cons]
    have hstep := h.step (T := L) hA hS fun c _ => hg c
    have ih := VBall.transport_fwd U L (hU L List.mem_cons_self)
      (fun L' hL' => hU L' (List.mem_cons_of_mem _ hL')) (mul_nonneg (by norm_num) hA)
      (fun c => sum_nonneg fun x _ => mul_nonneg (by split_ifs <;> norm_num) (hg x)) hstep
    have e : (fun c => ∑ s ∈ S, psum (L :: U) (nes (L :: U).length) s c * g s)
        = fun c => ∑ l ∈ L, psum U (nes U.length) l c
          * ∑ x ∈ S, (if l ≠ x then 1 else 0) * g x := by
      funext c
      show ∑ s ∈ S, psum (L :: U) (neP :: nes U.length) s c * g s = _
      simp only [psum_cons, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun s _ => ?_
      have hne : neP s l = if l ≠ s then 1 else 0 := by
        unfold neP
        simp [eq_comm]
      rw [hne]
      ring
    rw [e, show (2 : ℝ) ^ (L :: U).length * A = 2 ^ U.length * (2 * A) by
      rw [List.length_cons, pow_succ]; ring]
    exact ih

/-- **The arm with the loaded edge**, free at its far end: as a function of the colour of the
root end `u` it is in the vertex ball class. `K t` stands for the number of colourings of the
part beyond `T`. -/
theorem arm_vBall {S : Finset ℕ} {U₁ : List (Finset ℕ)} {T : Finset ℕ} (hS : S.card = 3)
    (hU₁ : ∀ L ∈ U₁, L.card = 3) (hT : T.card = 3) {W : ℕ → ℕ → ℝ} (hW : ∀ c d, 0 ≤ W c d)
    {A : ℝ} (hA : 0 < A) (hin : InBall S T W A) {K : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ t ∈ T, κ ≤ K t) :
    VBall (U₁.getLastD S)
      (fun c => ∑ s ∈ S, ∑ t ∈ T, psum U₁ (nes U₁.length) s c * W s t * K t)
      (κ * (2 ^ U₁.length * (2 * A))) := by
  have hg := hin.vBall_left hA.le hT hW
  have htr := VBall.transport_fwd U₁ S hS hU₁ (mul_nonneg (by norm_num) hA.le)
    (fun c => sum_nonneg fun t _ => hW c t) hg
  refine (htr.smul κ).mono (fun c _ => mul_nonneg hκ (sum_nonneg fun s _ =>
    mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (sum_nonneg fun t _ => hW s t)))
    fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  have h1 : 0 ≤ psum U₁ (nes U₁.length) s c * W s t :=
    mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (hW s t)
  calc κ * (psum U₁ (nes U₁.length) s c * W s t)
      = psum U₁ (nes U₁.length) s c * W s t * κ := by ring
    _ ≤ psum U₁ (nes U₁.length) s c * W s t * K t := mul_le_mul_of_nonneg_left (hK t ht) h1

/-- The free-end count of the stretch `P` beyond `T`. -/
theorem free_P_ge (P : List (Finset ℕ)) (T : Finset ℕ) (hP : ∀ L ∈ P, L.card = 3) {t : ℕ}
    (ht : t ∈ T) : (2 : ℝ) ^ P.length ≤ ∑ x ∈ P.getLastD T, psum P (nes P.length) t x := by
  rcases eq_nil_or_snoc P with rfl | ⟨P', X, rfl⟩
  · show (2 : ℝ) ^ 0 ≤ ∑ x ∈ T, psum [] (nes 0) t x
    simp only [psum_nil, pow_zero]
    rw [Finset.sum_eq_single t (fun x _ hx => by rw [ite_eq_right (Ne.symm hx)])
      (fun h => absurd ht h), ite_eq_left rfl]
  · have hl : (P' ++ [X]).getLastD T = X := by rw [getLastD_append]; rfl
    rw [hl, List.length_append, List.length_singleton]
    exact free_end_ge P' X (fun L hL => hP L (List.mem_append_left _ hL))
      (hP X (List.mem_append_right _ List.mem_cons_self)) t

/-- **The term left by a cut**: the arm with the loaded edge, free beyond the stretch `P`, times
a factor that depends on the colour of `v` only and is at least `κ`. -/
theorem cut_inBall {S : Finset ℕ} {U₁ : List (Finset ℕ)} {T : Finset ℕ} (P : List (Finset ℕ))
    {Lv : Finset ℕ} (hS : S.card = 3) (hU₁ : ∀ L ∈ U₁, L.card = 3) (hT : T.card = 3)
    (hP : ∀ L ∈ P, L.card = 3) (hLv : Lv.card = 3) {W : ℕ → ℕ → ℝ} (hW : ∀ c d, 0 ≤ W c d)
    {A : ℝ} (hA : 0 < A) (hin : InBall S T W A) {K : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ d ∈ Lv, κ ≤ K d) :
    InBall (U₁.getLastD S) Lv
      (fun c d => (∑ x ∈ P.getLastD T, ∑ s ∈ S, ∑ t ∈ T,
        psum U₁ (nes U₁.length) s c * W s t * psum P (nes P.length) t x) * K d)
      (2 ^ P.length * (2 ^ U₁.length * (2 * A)) * κ) := by
  have hLu : (U₁.getLastD S).card = 3 := card_getLastD hS hU₁
  have harm := arm_vBall hS hU₁ hT hW hA hin (K := fun t => ∑ x ∈ P.getLastD T,
    psum P (nes P.length) t x) (κ := 2 ^ P.length) (by positivity) fun t ht => free_P_ge P T hP ht
  have h1 : InBall (U₁.getLastD S) Lv
      (fun c _ => ∑ s ∈ S, ∑ t ∈ T, psum U₁ (nes U₁.length) s c * W s t
        * ∑ x ∈ P.getLastD T, psum P (nes P.length) t x)
      (2 ^ P.length * (2 ^ U₁.length * (2 * A))) := harm.inBall_left hLu hLv
  have h2 : InBall (U₁.getLastD S) Lv (fun _ d => K d) κ :=
    Dominant.inBall hκ fun c _ d hd _ => hK d hd
  have h3 := InBall.mul (by positivity) hκ h1 h2
  have e : (fun c d => (∑ s ∈ S, ∑ t ∈ T, psum U₁ (nes U₁.length) s c * W s t
        * ∑ x ∈ P.getLastD T, psum P (nes P.length) t x) * K d)
      = fun c d => (∑ x ∈ P.getLastD T, ∑ s ∈ S, ∑ t ∈ T,
        psum U₁ (nes U₁.length) s c * W s t * psum P (nes P.length) t x) * K d := by
    funext c d
    congr 1
    simp only [Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
  rw [e] at h3
  exact h3

/-- The profile of a face, split at the end of the stretch `P` of its second arm. -/
theorem armF_split (S : Finset ℕ) (U₁ : List (Finset ℕ)) (T : Finset ℕ) (P B : List (Finset ℕ))
    (W : ℕ → ℕ → ℝ) (c d : ℕ) :
    armF S U₁ T (P ++ B) W c d
      = ∑ x ∈ P.getLastD T, (∑ s ∈ S, ∑ t ∈ T,
          psum U₁ (nes U₁.length) s c * W s t * psum P (nes P.length) t x)
        * psum B (nes B.length) x d := by
  unfold armF
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm (s := P.getLastD T) (t := S)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm (s := P.getLastD T) (t := T)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [List.length_append, psum_split_nes P B T ht d, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-! ### The rules -/

section Rules

variable {S : Finset ℕ} {U₁ : List (Finset ℕ)} {T : Finset ℕ} {P R : List (Finset ℕ)}

/-- **Cut.** -/
theorem faceOK_cut (hS : S.card = 3) (hU₁ : ∀ L ∈ U₁, L.card = 3) (hT : T.card = 3)
    (hP : ∀ L ∈ P, L.card = 3) {Sub : List (Finset ℕ)} (hSub : ∀ L ∈ Sub, L.card = 3)
    (hR : ∀ L ∈ R, L.card = 3) (b : ℕ)
    (hcut : ∀ x ∈ P.getLastD T, ∀ z ∈ Sub.getLastD (P.getLastD T),
      (b : ℝ) ≤ psum Sub (nes Sub.length) x z)
    (hb : 2 ^ Sub.length + 1 ≤ 3 * b) : FaceOK S U₁ T (P ++ (Sub ++ R)) := by
  intro W hW A hA hin
  have hZ : (Sub.getLastD (P.getLastD T)).card = 3 := card_getLastD (card_getLastD hT hP) hSub
  have hlast : (P ++ (Sub ++ R)).getLastD T = R.getLastD (Sub.getLastD (P.getLastD T)) := by
    rw [getLastD_append, getLastD_append]
  have hLv : (R.getLastD (Sub.getLastD (P.getLastD T))).card = 3 := card_getLastD hZ hR
  rw [hlast]
  have hcutI := cut_inBall P hS hU₁ hT hP hLv hW hA hin (K := fun _ => (b : ℝ) * 2 ^ R.length)
    (κ := (b : ℝ) * 2 ^ R.length) (by positivity) fun d _ => le_rfl
  have hconst : faceConst3 (U₁.length + (P ++ (Sub ++ R)).length) * A
      ≤ 2 ^ P.length * (2 ^ U₁.length * (2 * A)) * ((b : ℝ) * 2 ^ R.length) := by
    have h1 := faceConst3_le_cut (m := U₁.length + (P ++ (Sub ++ R)).length) (n := Sub.length)
      (e := P.length + U₁.length + 1 + R.length) (b := b)
      (by simp only [List.length_append]; omega) hb
    calc faceConst3 (U₁.length + (P ++ (Sub ++ R)).length) * A
        ≤ (b : ℝ) * 2 ^ (P.length + U₁.length + 1 + R.length) * A :=
          mul_le_mul_of_nonneg_right h1 hA.le
      _ = _ := by
          rw [pow_add, pow_add, pow_add]
          ring
  refine (hcutI.weaken (mul_nonneg (faceConst3_pos _).le hA.le) hconst).mono
    (fun c d => mul_nonneg (sum_nonneg fun x _ => sum_nonneg fun s _ => sum_nonneg fun t _ =>
      mul_nonneg (mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (hW s t))
        (psum_nonneg _ _ (nes_nonneg _) _ _)) (by positivity)) fun c _ d hd _ => ?_
  rw [armF_split, Finset.sum_mul]
  refine Finset.sum_le_sum fun x hx => ?_
  refine mul_le_mul_of_nonneg_left ?_ (sum_nonneg fun s _ => sum_nonneg fun t _ =>
    mul_nonneg (mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (hW s t))
      (psum_nonneg _ _ (nes_nonneg _) _ _))
  rw [List.length_append, psum_split_nes Sub R (P.getLastD T) hx d]
  have hfree := free_start_ge R (Sub.getLastD (P.getLastD T)) hR hZ d hd
  calc (b : ℝ) * 2 ^ R.length
      ≤ (b : ℝ) * ∑ z ∈ Sub.getLastD (P.getLastD T), psum R (nes R.length) z d :=
        mul_le_mul_of_nonneg_left hfree (Nat.cast_nonneg _)
    _ = ∑ z ∈ Sub.getLastD (P.getLastD T), (b : ℝ) * psum R (nes R.length) z d :=
        Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hcut x hx z hz)
        (psum_nonneg _ _ (nes_nonneg _) _ _)

/-- The two parts of a shortened face: common end of the proofs of the two shortening rules.
`F ≥ F' + γ · (cut term)` with `F'` in the ball class with the constant of a face with two
vertices fewer. -/
theorem faceOK_of_split (hS : S.card = 3) (hU₁ : ∀ L ∈ U₁, L.card = 3) (hT : T.card = 3)
    (hP : ∀ L ∈ P, L.card = 3) (hR : ∀ L ∈ R, L.card = 3) {Z : Finset ℕ} (hZ : Z.card = 3)
    {U₂ : List (Finset ℕ)} (hlast : U₂.getLastD T = R.getLastD Z) {m' : ℕ} (γ : ℕ)
    (hlen : U₁.length + U₂.length = m' + 2)
    (hγ : (γ : ℝ) * 2 ^ (P.length + U₁.length + 1 + R.length) = 2 ^ (m' + 1))
    {W : ℕ → ℕ → ℝ} (hW : ∀ c d, 0 ≤ W c d) {A : ℝ} (hA : 0 < A) (hin : InBall S T W A)
    {F' : ℕ → ℕ → ℝ} (hF'0 : ∀ c d, 0 ≤ F' c d)
    (hF' : InBall (U₁.getLastD S) (R.getLastD Z) F' (faceConst3 m' * A))
    (hle : ∀ c, ∀ d ∈ R.getLastD Z, F' c d
      + (∑ x ∈ P.getLastD T, ∑ s ∈ S, ∑ t ∈ T,
          psum U₁ (nes U₁.length) s c * W s t * psum P (nes P.length) t x)
        * ((γ : ℝ) * ∑ z ∈ Z, psum R (nes R.length) z d) ≤ armF S U₁ T U₂ W c d) :
    InBall (U₁.getLastD S) (U₂.getLastD T) (armF S U₁ T U₂ W)
      (faceConst3 (U₁.length + U₂.length) * A) := by
  have hLv : (R.getLastD Z).card = 3 := card_getLastD hZ hR
  rw [hlast, hlen, faceConst3_add_two]
  have hcutI := cut_inBall P hS hU₁ hT hP hLv hW hA hin
    (K := fun d => (γ : ℝ) * ∑ z ∈ Z, psum R (nes R.length) z d)
    (κ := (γ : ℝ) * 2 ^ R.length) (by positivity) fun d hd =>
      mul_le_mul_of_nonneg_left (free_start_ge R Z hR hZ d hd) (Nat.cast_nonneg _)
  have hsum := InBall.add (mul_nonneg (faceConst3_pos _).le hA.le) (by positivity) hF'0
    (fun c d => mul_nonneg (sum_nonneg fun x _ => sum_nonneg fun s _ => sum_nonneg fun t _ =>
      mul_nonneg (mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (hW s t))
        (psum_nonneg _ _ (nes_nonneg _) _ _))
      (mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun z _ => psum_nonneg _ _ (nes_nonneg _) _ _)))
    hF' hcutI
  have hconst : (faceConst3 m' + 2 ^ (m' + 1)) * A
      = faceConst3 m' * A + 2 ^ P.length * (2 ^ U₁.length * (2 * A)) * ((γ : ℝ) * 2 ^ R.length) := by
    rw [← hγ, pow_add, pow_add, pow_add]
    ring
  rw [hconst]
  exact hsum.mono (fun c d => add_nonneg (hF'0 c d)
    (mul_nonneg (sum_nonneg fun x _ => sum_nonneg fun s _ => sum_nonneg fun t _ =>
      mul_nonneg (mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (hW s t))
        (psum_nonneg _ _ (nes_nonneg _) _ _))
      (mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun z _ => psum_nonneg _ _ (nes_nonneg _) _ _))))
    fun c _ d hd _ => hle c d hd

/-- **Replacing a stretch of three edges by one edge.** -/
theorem faceOK_sh1 (hS : S.card = 3) (hU₁ : ∀ L ∈ U₁, L.card = 3) (hT : T.card = 3)
    (hP : ∀ L ∈ P, L.card = 3) (hR : ∀ L ∈ R, L.card = 3) {Y₁ Y₂ Z : Finset ℕ}
    (hZ : Z.card = 3) (ih : FaceOK S U₁ T (P ++ Z :: R))
    (h : ∀ x ∈ P.getLastD T, ∀ z ∈ Z, neP x z + 2 ≤ psum [Y₁, Y₂, Z] (nes 3) x z) :
    FaceOK S U₁ T (P ++ Y₁ :: Y₂ :: Z :: R) := by
  intro W hW A hA hin
  have hlast' : (P ++ Z :: R).getLastD T = R.getLastD Z := by
    rw [getLastD_append, getLastD_cons]
  have hih := ih W hW A hA hin
  rw [hlast'] at hih
  have hG0 : ∀ c x, 0 ≤ ∑ s ∈ S, ∑ t ∈ T,
      psum U₁ (nes U₁.length) s c * W s t * psum P (nes P.length) t x := fun c x =>
    sum_nonneg fun s _ => sum_nonneg fun t _ =>
      mul_nonneg (mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (hW s t))
        (psum_nonneg _ _ (nes_nonneg _) _ _)
  refine faceOK_of_split (P := P) (R := R) (m' := U₁.length + (P ++ Z :: R).length)
    hS hU₁ hT hP hR hZ
    (by rw [getLastD_append, getLastD_cons, getLastD_cons, getLastD_cons]) 2
    (by simp only [List.length_append, List.length_cons]; omega)
    (by
      simp only [List.length_append, List.length_cons]
      rw [show U₁.length + (P.length + (R.length + 1)) + 1
        = (P.length + U₁.length + 1 + R.length) + 1 by omega, pow_succ]
      push_cast
      ring) hW hA hin
    (armF_nonneg hW) hih fun c d _ => ?_
  rw [armF_split S U₁ T P (Z :: R), armF_split S U₁ T P (Y₁ :: Y₂ :: Z :: R), Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hG0 c x)
  have e1 : psum (Z :: R) (nes (Z :: R).length) x d
      = ∑ z ∈ Z, neP x z * psum R (nes R.length) z d := rfl
  have e2 : psum (Y₁ :: Y₂ :: Z :: R) (nes (Y₁ :: Y₂ :: Z :: R).length) x d
      = ∑ z ∈ Z, psum [Y₁, Y₂, Z] (nes 3) x z * psum R (nes R.length) z d := by
    have h3 : (Y₁ :: Y₂ :: Z :: R).length = [Y₁, Y₂, Z].length + R.length := by
      simp only [List.length_cons, List.length_nil]
      omega
    rw [h3]
    exact psum_split_nes [Y₁, Y₂, Z] R (P.getLastD T) hx d
  rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z hz => ?_
  have h0 := psum_nonneg R (nes R.length) (nes_nonneg _) z d
  calc neP x z * psum R (nes R.length) z d + ((2 : ℕ) : ℝ) * psum R (nes R.length) z d
      = (neP x z + 2) * psum R (nes R.length) z d := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (h x hx z hz) h0

/-- **Contracting a stretch of two edges between equal lists.** -/
theorem faceOK_sh0 (hS : S.card = 3) (hU₁ : ∀ L ∈ U₁, L.card = 3) (hT : T.card = 3)
    (hP : ∀ L ∈ P, L.card = 3) (hR : ∀ L ∈ R, L.card = 3) {Y Z : Finset ℕ} (hZ : Z.card = 3)
    (ih : FaceOK S U₁ T (P ++ R)) (hXZ : P.getLastD T = Z)
    (h : ∀ x ∈ Z, ∀ z ∈ Z, (if x = z then (1 : ℝ) else 0) + 1 ≤ psum [Y, Z] (nes 2) x z) :
    FaceOK S U₁ T (P ++ Y :: Z :: R) := by
  intro W hW A hA hin
  have hlast' : (P ++ R).getLastD T = R.getLastD Z := by
    rw [getLastD_append, hXZ]
  have hih := ih W hW A hA hin
  rw [hlast'] at hih
  have hG0 : ∀ c x, 0 ≤ ∑ s ∈ S, ∑ t ∈ T,
      psum U₁ (nes U₁.length) s c * W s t * psum P (nes P.length) t x := fun c x =>
    sum_nonneg fun s _ => sum_nonneg fun t _ =>
      mul_nonneg (mul_nonneg (psum_nonneg _ _ (nes_nonneg _) _ _) (hW s t))
        (psum_nonneg _ _ (nes_nonneg _) _ _)
  refine faceOK_of_split (P := P) (R := R) (m' := U₁.length + (P ++ R).length)
    hS hU₁ hT hP hR hZ
    (by rw [getLastD_append, getLastD_cons, getLastD_cons]) 1
    (by simp only [List.length_append, List.length_cons]; omega)
    (by
      simp only [List.length_append]
      rw [show U₁.length + (P.length + R.length) + 1 = P.length + U₁.length + 1 + R.length by
        omega]
      push_cast
      ring) hW hA hin
    (armF_nonneg hW) hih fun c d _ => ?_
  rw [armF_split S U₁ T P R, armF_split S U₁ T P (Y :: Z :: R), Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hG0 c x)
  have hxZ : x ∈ Z := by rw [← hXZ]; exact hx
  have e2 : psum (Y :: Z :: R) (nes (Y :: Z :: R).length) x d
      = ∑ z ∈ Z, psum [Y, Z] (nes 2) x z * psum R (nes R.length) z d := by
    have h3 : (Y :: Z :: R).length = [Y, Z].length + R.length := by
      simp only [List.length_cons, List.length_nil]
      omega
    rw [h3]
    exact psum_split_nes [Y, Z] R (P.getLastD T) hx d
  have e1 : psum R (nes R.length) x d
      = ∑ z ∈ Z, (if x = z then (1 : ℝ) else 0) * psum R (nes R.length) z d := by
    rw [Finset.sum_eq_single x (fun z _ hz => by rw [ite_eq_right (Ne.symm hz), zero_mul])
      (fun hh => absurd hxZ hh), ite_eq_left rfl, one_mul]
  rw [e2, e1, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z hz => ?_
  have h0 := psum_nonneg R (nes R.length) (nes_nonneg _) z d
  calc (if x = z then (1 : ℝ) else 0) * psum R (nes R.length) z d
        + ((1 : ℕ) : ℝ) * psum R (nes R.length) z d
      = ((if x = z then (1 : ℝ) else 0) + 1) * psum R (nes R.length) z d := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (h x hxZ z hz) h0

end Rules

end Outerplanar
