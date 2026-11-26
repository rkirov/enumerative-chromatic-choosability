/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Code15
import Outerplanar.SqClose

/-!
# Closing a square at the fifteen-face centroid

A term of a square centroid gives the four sides codes (`Outerplanar/Code15.lean`). At a root
`r` the laws below close the face glued to its root side; their discrete conditions are
`rootOK15` (the scale comparisons by `Sc.ge1`), and **`rootOK15_sound`** is their soundness.

* `[M, M, M]`, `[B, M, M]` (any position): the scales are at least one;
* `[H, M, M]` (any position) at `K = 59/56` (`sqLawH`);
* `[B, B, B]` at `(16/17)²` and `[B, 1, B]` at `16/17` (the run `B1B` of milestone M4);
* `three_heavy` at a constant root (`sq_HHH_close` of milestone M0);
* the closings **U1a, U1b, U2, U3** of the fifteen-face note at a constant root, read in both
  directions (`Outerplanar/Sq15RunHC.lean`).

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar Outerplanar.SqMulti C15

/-! ### Scales at least one -/

theorem C15.hV_ge (c : C15) : 1 ≤ c.hV.val := by
  cases c <;> simp only [C15.hV, Sc.val_one, Sc.val_A, Sc.val_a5, Sc.val_d6]
  all_goals first | exact one_le_a5 | exact one_le_d6 | norm_num

theorem C15.mV_ge (c : C15) : 1 ≤ c.mV.val := by
  cases c <;> simp only [C15.mV, Sc.val_one, Sc.val_kq, Sc.val_kA]
  all_goals first | exact one_le_κq | exact one_le_κA | norm_num

theorem C15.bV_ge (c : C15) : 1 ≤ c.bV.val := by
  cases c <;> simp only [C15.bV, Sc.val_one, Sc.val_A] <;> norm_num

/-! ### The laws in path form -/

section PathLaws

variable {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ}

theorem path3 {P : Fin 3 → Finset ℕ → Finset ℕ → Prop}
    (h : ∀ j : Fin 3, P j (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)) :
    P 0 Lu (Li 0) ∧ P 1 (Li 0) (Li 1) ∧ P 2 (Li 1) Lv := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  rw [l0, l1] at h0; rw [l2, l3] at h1; rw [l4, l5] at h2
  exact ⟨h0, h1, h2⟩

/-- **`[B, 1, B]`** in path form, at the scale `16/17`. -/
theorem sqLawB1B (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (h0 : InBall (pathList Lu Lv Li (0 : Fin 3).castSucc) (pathList Lu Lv Li (0 : Fin 3).succ)
      (E 0) (N 0))
    (h1 : Dominant (pathList Lu Lv Li (1 : Fin 3).castSucc) (pathList Lu Lv Li (1 : Fin 3).succ)
      (E 1) (N 1))
    (h2 : InBall (pathList Lu Lv Li (2 : Fin 3).castSucc) (pathList Lu Lv Li (2 : Fin 3).succ)
      (E 2) (N 2)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) E) (16 / 17 * faceConst3 2 * ∏ j, N j) := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  rw [l0, l1] at h0; rw [l2, l3] at h1; rw [l4, l5] at h2
  rw [faceConst3_two, Fin.prod_univ_three, show (16 / 17 : ℝ) * 3 = 3 * (16 / 17) by ring]
  exact sq_B1B_hex hLv hLi hE0 hN h0 h1 h2

end PathLaws

/-! ### The laws at a root -/

section Laws

variable (C : Fin (2 + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
  (G : Fin (2 + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d) (w : Fin (2 + 2) → ℝ)
  (hw : ∀ i, 0 < w i) (τ : Fin (2 + 2) → ℕ) (ρ : Fin (2 + 2) → Fin 3)
  (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i))

include hC hG0 hw hpt

theorem sq_side15 (r : Fin (2 + 2)) (j : Fin (2 + 1)) :
    PT (τ (pos r j)) (ρ (pos r j))
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.castSucc)
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.succ)
      (G (pos r j)) (w (pos r j)) :=
  side_root (fun i S T Y => PT (τ i) (ρ i) S T Y (w i)) hpt r j

/-- The code of a side. -/
abbrev cdOf (i : Fin (2 + 2)) : C15 := code15 (τ i) (ρ i)

omit hC hG0 hw hpt in
theorem prod3 (f : Fin (2 + 1) → ℝ) : ∏ j, f j = f 0 * f 1 * f 2 := Fin.prod_univ_three f

/-- `[M, M, M]` at the root `r`. -/
theorem sq_MMM15 (r : Fin (2 + 2)) (hM : ∀ j, (cdOf τ ρ (pos r j)).isM = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  have hP : ∀ j : Fin (2 + 1), HasPot
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.castSucc)
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.succ)
      (G (pos r j)) (w (pos r j) * (cdOf τ ρ (pos r j)).mV.val) := fun j => by
    have := sq_side15 C hC G hG0 w hw τ ρ hpt r j
    refine cap_hasPot15 ?_ ?_ (hw _) (hG0 _) (hM j) this
    · rw [pathList_root]; exact hC _
    · rw [pathList_root]; exact hC _
  have key := hasPot_face3 (m := 2) le_rfl (C (r + 1)) (C r)
    (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) (hC _) (hC _) (fun k => hC _)
    (fun j => G (pos r j)) (fun j c d => hG0 _ c d) _
    (fun j => mul_pos (hw _) (Sc.val_pos _)) hP
  have hH := key.hex (hC _) (hC _) (by
    have := faceConst3_pos 2
    have := Finset.prod_pos fun j (_ : j ∈ univ) =>
      mul_pos (hw (pos r j)) (Sc.val_pos (cdOf τ ρ (pos r j)).mV)
    positivity)
  refine close_scaled C hC G hG0 w hw r (κ := 1) (t := (cdOf τ ρ r).hV.val)
    (fun j => (cdOf τ ρ (pos r j)).mV.val) one_pos (fun j => Sc.val_pos _) (Sc.val_pos _)
    (by rw [one_mul]; exact hH) (cap_hex15 (hw r) (hG0 r) (hpt r)) ?_
  rw [one_mul]
  exact one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun j _ => C15.mV_ge _) (C15.hV_ge _)

/-- `[B, M, M]` at the root `r`, the ball side at the position `q`. -/
theorem sq_BMM15 (r : Fin (2 + 2)) (q : Fin (2 + 1))
    (hB : (cdOf τ ρ (pos r q)).hasB = true)
    (hM : ∀ j, j ≠ q → (cdOf τ ρ (pos r j)).isM = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => if j = q then (cdOf τ ρ (pos r j)).bV.val
    else (cdOf τ ρ (pos r j)).mV.val with hs
  have hspos : ∀ j, 0 < s j := fun j => by simp only [hs]; split_ifs <;> exact Sc.val_pos _
  have key : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      (faceConst3 2 * ∏ j : Fin (2 + 1), (w (pos r j) * s j)) :=
    sqLawB (hC r) (fun k => hC _) (fun j => G (pos r j)) (fun j c d => hG0 _ c d)
      (fun j => w (pos r j) * s j) (fun j => mul_pos (hw _) (hspos j)) q
      (by simpa [hs] using cap_B15 (hw _) hB (sq_side15 C hC G hG0 w hw τ ρ hpt r q))
      fun j hj => by
        simpa [hs, hj] using cap_M15 (hw _) (hM j hj) (sq_side15 C hC G hG0 w hw τ ρ hpt r j)
  refine close_scaled C hC G hG0 w hw r (κ := 1) (t := (cdOf τ ρ r).hV.val) s one_pos hspos
    (Sc.val_pos _) (by rw [one_mul]; exact key) (cap_hex15 (hw r) (hG0 r) (hpt r)) ?_
  rw [one_mul]
  refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun j _ => ?_) (C15.hV_ge _)
  simp only [hs]; split_ifs
  · exact C15.bV_ge _
  · exact C15.mV_ge _

/-- The scale vector of `[H, M, M]`: the hexagon side `q`, matchings elsewhere. -/
def hmS (cd : Fin (2 + 2) → C15) (r : Fin (2 + 2)) (q j : Fin (2 + 1)) : Sc :=
  if j = q then (cd (pos r j)).hV else (cd (pos r j)).mV

/-- `[H, M, M]` at the root `r`, the hexagon side at the position `q`. -/
theorem sq_HMM15 (r : Fin (2 + 2)) (q : Fin (2 + 1))
    (hM : ∀ j, j ≠ q → (cdOf τ ρ (pos r j)).isM = true)
    (hS : ((cdOf τ ρ r).hV.add ((hmS (cdOf τ ρ) r q 0).add ((hmS (cdOf τ ρ) r q 1).add
      ((hmS (cdOf τ ρ) r q 2).add Sc.kInv)))).ge1 = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => (hmS (cdOf τ ρ) r q j).val with hs
  have hspos : ∀ j, 0 < s j := fun j => Sc.val_pos _
  have key : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      (56 / 59 * faceConst3 2 * ∏ j : Fin (2 + 1), (w (pos r j) * s j)) :=
    sqLawH (hC r) (fun k => hC _) (fun j => G (pos r j)) (fun j c d => hG0 _ c d)
      (fun j => w (pos r j) * s j) (fun j => mul_pos (hw _) (hspos j)) q
      (by simpa [hs, hmS] using cap_hex15 (hw _) (hG0 _) (sq_side15 C hC G hG0 w hw τ ρ hpt r q))
      fun j hj => by
        simpa [hs, hmS, hj] using
          cap_M15 (hw _) (hM j hj) (sq_side15 C hC G hG0 w hw τ ρ hpt r j)
  refine close_scaled C hC G hG0 w hw r (κ := 56 / 59) (t := (cdOf τ ρ r).hV.val) s
    (by norm_num) hspos (Sc.val_pos _) key (cap_hex15 (hw r) (hG0 r) (hpt r)) ?_
  have := Sc.ge1_sound hS
  simp only [Sc.val_add, Sc.val_kInv] at this
  rw [prod3]
  simp only [hs]
  linarith

/-- `[B, B, B]` at the root `r`. -/
theorem sq_BBB15 (r : Fin (2 + 2)) (hB : ∀ j, (cdOf τ ρ (pos r j)).hasB = true)
    (hS : ((cdOf τ ρ r).hV.add ((cdOf τ ρ (pos r 0)).bV.add ((cdOf τ ρ (pos r 1)).bV.add
      ((cdOf τ ρ (pos r 2)).bV.add (Sc.aInv.add Sc.aInv))))).ge1 = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => (cdOf τ ρ (pos r j)).bV.val with hs
  have hspos : ∀ j, 0 < s j := fun j => Sc.val_pos _
  have key : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      ((16 / 17) ^ 2 * faceConst3 2 * ∏ j : Fin (2 + 1), (w (pos r j) * s j)) :=
    sqLawBBB (hC r) (fun k => hC _) (fun j => G (pos r j)) (fun j c d => hG0 _ c d)
      (fun j => w (pos r j) * s j) (fun j => mul_pos (hw _) (hspos j))
      fun j => cap_B15 (hw _) (hB j) (sq_side15 C hC G hG0 w hw τ ρ hpt r j)
  refine close_scaled C hC G hG0 w hw r (κ := (16 / 17) ^ 2) (t := (cdOf τ ρ r).hV.val) s
    (by norm_num) hspos (Sc.val_pos _) key (cap_hex15 (hw r) (hG0 r) (hpt r)) ?_
  have := Sc.ge1_sound hS
  simp only [Sc.val_add, Sc.val_aInv] at this
  rw [prod3]
  simp only [hs]
  linarith

/-- `[B, 1, B]` at the root `r`. -/
theorem sq_B1B15 (r : Fin (2 + 2)) (h1 : cdOf τ ρ (pos r 1) = .I)
    (hB0 : (cdOf τ ρ (pos r 0)).hasB = true) (hB2 : (cdOf τ ρ (pos r 2)).hasB = true)
    (hS : ((cdOf τ ρ r).hV.add ((cdOf τ ρ (pos r 0)).bV.add ((cdOf τ ρ (pos r 2)).bV.add
      Sc.aInv))).ge1 = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => if j = 1 then 1 else (cdOf τ ρ (pos r j)).bV.val with hs
  have hspos : ∀ j, 0 < s j := fun j => by simp only [hs]; split_ifs; exacts [one_pos, Sc.val_pos _]
  have key : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      (16 / 17 * faceConst3 2 * ∏ j : Fin (2 + 1), (w (pos r j) * s j)) :=
    sqLawB1B (hC r) (fun k => hC _) (fun j => G (pos r j)) (fun j c d => hG0 _ c d)
      (fun j => w (pos r j) * s j) (fun j => mul_pos (hw _) (hspos j))
      (by simpa [hs] using cap_B15 (hw _) hB0 (sq_side15 C hC G hG0 w hw τ ρ hpt r 0))
      (by simpa [hs] using cap_I15 h1 (sq_side15 C hC G hG0 w hw τ ρ hpt r 1))
      (by simpa [hs] using cap_B15 (hw _) hB2 (sq_side15 C hC G hG0 w hw τ ρ hpt r 2))
  refine close_scaled C hC G hG0 w hw r (κ := 16 / 17) (t := (cdOf τ ρ r).hV.val) s
    (by norm_num) hspos (Sc.val_pos _) key (cap_hex15 (hw r) (hG0 r) (hpt r)) ?_
  have := Sc.ge1_sound hS
  simp only [Sc.val_add, Sc.val_aInv] at this
  rw [prod3]
  simp only [hs, show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
  linarith

/-- The closing at a constant root: a count of `18` on the path gives the glued count. -/
theorem close18 (r : Fin (2 + 2)) (hI : cdOf τ ρ r = .I)
    (key : 18 * (w (pos r 0) * w (pos r 1) * w (pos r 2))
      ≤ ∑ x ∈ C (r + 1), ∑ y ∈ C r, if x = y then 0 else
        faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) (fun _ _ => 1)
          (fun j => G (pos r j)) x y) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  have hroot := cap_I15 hI (hpt r)
  have hcl := close_count C G hG0 r (hw r).le hroot key
  refine le_trans (le_of_eq ?_) hcl
  rw [← prod_root w r, prod3, faceConst3_two]
  ring

/-- `three_heavy` at a constant root `r`. -/
theorem sq_HHHc15 (r : Fin (2 + 2)) (hI : cdOf τ ρ r = .I)
    (hS : ((cdOf τ ρ (pos r 0)).hV.add ((cdOf τ ρ (pos r 1)).hV.add ((cdOf τ ρ (pos r 2)).hV.add
      (Sc.aInv.add (Sc.aInv.add Sc.aInv))))).ge1 = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => (cdOf τ ρ (pos r j)).hV.val with hs
  have hspos : ∀ j, 0 < s j := fun j => Sc.val_pos _
  obtain ⟨h0, h1, h2⟩ := path3 (Lu := C (r + 1)) (Lv := C r)
    (Li := fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
    (P := fun j S T => Hex S T (G (pos r j)) (w (pos r j) * s j))
    fun j => cap_hex15 (hw _) (hG0 _) (sq_side15 C hC G hG0 w hw τ ρ hpt r j)
  have key := SqMulti.sq_HHH_close (Li := fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
    (hC (r + 1)) (hC r) (fun k => hC _) (W := fun j => G (pos r j))
    (fun j c d => hG0 _ c d) (N := fun j => w (pos r j) * s j)
    (fun j => mul_pos (hw _) (hspos j)) h0 h1 h2
  refine close18 C hC G hG0 w hw τ ρ hpt r hI (le_trans ?_ key)
  have := Sc.ge1_sound hS
  simp only [Sc.val_add, Sc.val_aInv] at this
  have hW : 0 ≤ w (pos r 0) * w (pos r 1) * w (pos r 2) := by
    have := hw (pos r 0); have := hw (pos r 1); have := hw (pos r 2); positivity
  have e : 18 * (16 / 17) ^ 3 * (w (pos r 0) * s 0 * (w (pos r 1) * s 1) * (w (pos r 2) * s 2))
      = 18 * (w (pos r 0) * w (pos r 1) * w (pos r 2)) * (s 0 * (s 1 * (s 2 * (16 / 17 *
        (16 / 17 * (16 / 17)))))) := by ring
  rw [e]
  nlinarith

/-- The closings of the fifteen-face note at a constant root. -/
def uB (cd : Fin (2 + 2) → C15) (r : Fin (2 + 2)) : Bool :=
  let a := cd (pos r 0)
  let b := cd (pos r 1)
  let c := cd (pos r 2)
  (a.inABf && b.inBAHf && c.inH7f) || (a.inH7f && b.inBAHf && c.inABf) ||
  (a.inBAHf && b.inABf && c.inH7f) || (a.inH7f && b.inABf && c.inBAHf) ||
  (a.inBAHf && b.inBf6 && c.inBAHf) ||
  (a.inBAHf && b.inBf5 && c.inBf5) || (a.inBf5 && b.inBf5 && c.inBAHf)

/-- **U1a, U1b, U2, U3** at a constant root `r`. -/
theorem sq_U15 (hτ7 : ∀ i, τ i ≤ 7) (r : Fin (2 + 2)) (hI : cdOf τ ρ r = .I)
    (hU : uB (cdOf τ ρ) r = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  obtain ⟨p0, p1, p2⟩ := path3 (Lu := C (r + 1)) (Lv := C r)
    (Li := fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
    (P := fun j S T => PT (τ (pos r j)) (ρ (pos r j)) S T (G (pos r j)) (w (pos r j)))
    fun j => sq_side15 C hC G hG0 w hw τ ρ hpt r j
  refine close18 C hC G hG0 w hw τ ρ hpt r hI ?_
  have hL := hC (r + 1)
  have hR := hC r
  have hM : ∀ k : Fin 2, (C (k.castSucc.succ + (r + 1))).card = 3 := fun k => hC _
  have hW : ∀ j c d, 0 ≤ (fun j => G (pos r j)) j c d := fun j c d => hG0 _ c d
  have hN : ∀ j, 0 < (fun j => w (pos r j)) j := fun j => hw _
  unfold uB at hU
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hU
  rcases hU with ((((((⟨⟨a, b⟩, c⟩ | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) |
    ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩)
  · exact sq_U1a_close hL hR hM hW hN (cap_ABf (hw _) a p0) (cap_BAHf (hw _) (hG0 _) b p1)
      (cap_H7f (hw _) (hG0 _) (hτ7 _) c p2)
  · exact sq_U1a_close_rev hL hR hM hW hN (cap_H7f (hw _) (hG0 _) (hτ7 _) a p0)
      (cap_BAHf (hw _) (hG0 _) b p1) (cap_ABf (hw _) c p2)
  · exact sq_U1b_close hL hR hM hW hN (cap_BAHf (hw _) (hG0 _) a p0) (cap_ABf (hw _) b p1)
      (cap_H7f (hw _) (hG0 _) (hτ7 _) c p2)
  · exact sq_U1b_close_rev hL hR hM hW hN (cap_H7f (hw _) (hG0 _) (hτ7 _) a p0)
      (cap_ABf (hw _) b p1) (cap_BAHf (hw _) (hG0 _) c p2)
  · exact sq_U2_close hL hR hM hW hN (cap_BAHf (hw _) (hG0 _) a p0) (cap_Bf6 (hw _) b p1)
      (cap_BAHf (hw _) (hG0 _) c p2)
  · exact sq_U3_close hL hR hM hW hN (cap_BAHf (hw _) (hG0 _) a p0) (cap_Bf5 (hw _) b p1)
      (cap_Bf5 (hw _) c p2)
  · exact sq_U3_close_rev hL hR hM hW hN (cap_Bf5 (hw _) a p0) (cap_Bf5 (hw _) b p1)
      (cap_BAHf (hw _) (hG0 _) c p2)

end Laws

end Outerplanar.F15
