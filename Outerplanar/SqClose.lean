/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.CycSum

/-!
# Closing a face at the centroid: the codes of the pure types and the square

Research note `ai_research_notes/OUTERPLANAR_THIRTEEN_AND_GAUGE_OBSTRUCTION_2026-11-23.md`, Step 3,
the even centre of length four. A term of the centroid face gives each side a pure type; only nine
*codes* matter (`Code`: the constant `I`, the one- to four-mark tables `L1 L2 T3 T4`, the ball parts
`B5 B6` and the hexagon parts `H5 H6`). Their capabilities (`cap_hex`, `cap_M`, `cap_B`, `cap_I`)
are read off `Outerplanar/MarkTerms.lean`.

At a square the six laws of the note close a term at a chosen root `r`: `[M, M, M]` (matching),
`[B, M, M]` in each position, `[H, M, M]` in each position (`D₆² ≥ K`), `[B, B, B]`, `[H, H, H]`
and the closing `three_heavy`. **`sqCover`** checks by `decide` that every assignment of codes to
the four sides with at most twelve marks has a root and a law whose (discrete) conditions hold; the
conditions are sufficient (`sqPlan_sound`). This replaces the case analysis of the note (heavy
sides `w₁ ≥ w₂ ≥ w₃`) by an exhaustive check of its 2198 cases; it was cross-checked numerically
(`ai_research_notes/T4b_M3_thirteen.md`).

Formalized by Claude (milestone M3 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar

open Finset

/-! ### Codes -/

/-- The codes of the pure types. -/
inductive Code
  | I | L1 | L2 | T3 | T4 | B5 | B6 | H5 | H6
  deriving DecidableEq

namespace Code

/-- The marks of a code. -/
def marks : Code → ℕ
  | I => 0 | L1 => 1 | L2 => 2 | T3 => 3 | T4 => 4 | B5 => 5 | B6 => 6 | H5 => 5 | H6 => 6

/-- In the matching class `M`. -/
def isM : Code → Bool
  | I => true | L1 => true | L2 => true | _ => false

/-- In the ball class `B`. -/
def hasB : Code → Bool
  | H5 => false | H6 => false | _ => true

/-- In `A H`. -/
def hA : Code → Bool
  | L1 => true | L2 => true | T3 => true | T4 => true | H5 => true | _ => false

/-- In `A B`. -/
def bA : Code → Bool
  | L1 => true | L2 => true | T3 => true | _ => false

/-- In `D₆ H`. -/
def hbig : Code → Bool
  | I => false | B5 => false | B6 => false | _ => true

/-- The hexagon scale. -/
noncomputable def hsc : Code → ℝ
  | L1 => 17 / 16 | L2 => 17 / 16 | T3 => 17 / 16 | T4 => 17 / 16 | H5 => a5 | H6 => d6 | _ => 1

/-- The matching scale. -/
noncomputable def msc : Code → ℝ
  | L1 => κq | L2 => κA | _ => 1

/-- The ball scale. -/
noncomputable def bsc : Code → ℝ
  | L1 => 17 / 16 | L2 => 17 / 16 | T3 => 17 / 16 | _ => 1

theorem hsc_ge (c : Code) : 1 ≤ hsc c := by
  cases c <;> simp only [hsc] <;> first | exact one_le_a5 | exact one_le_d6 | norm_num

theorem msc_ge (c : Code) : 1 ≤ msc c := by
  cases c <;> simp only [msc] <;> first | exact one_le_κq | exact one_le_κA | norm_num

theorem bsc_ge (c : Code) : 1 ≤ bsc c := by cases c <;> simp only [bsc] <;> norm_num

theorem hsc_A {c : Code} (h : hA c = true) : 17 / 16 ≤ hsc c := by
  cases c <;> simp_all [hA, hsc, a5_ge]

theorem bsc_A {c : Code} (h : bA c = true) : 17 / 16 ≤ bsc c := by
  cases c <;> simp_all [bA, bsc]

theorem d6_le_A : d6 ≤ 17 / 16 :=
  le_of_cube_le d6_pos.le (by norm_num) (by rw [d6_cube]; norm_num)

theorem hsc_big {c : Code} (h : hbig c = true) : d6 ≤ hsc c := by
  cases c <;> simp only [hbig, hsc] at h ⊢
  all_goals first | exact absurd h (by decide) | exact d6_le_A | exact d6_le_a5 | exact le_rfl

end Code

open Code

/-- The code of the pure type `(k, r)`. -/
def code (k : ℕ) (r : Fin 3) : Code :=
  if r = 0 then .I
  else if r = 1 then
    (if k ≤ 1 then .L1 else if k = 2 then .L2 else if k = 3 then .T3 else if k = 4 then .T4
      else if k = 5 then .B5 else .B6)
  else if k ≤ 5 then .H5 else .H6

theorem code_marks (k : ℕ) (r : Fin 3) (h1 : r = 1 → 1 ≤ k) (h2 : r = 2 → 5 ≤ k) :
    (code k r).marks ≤ if r = 0 then 0 else k := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by fin_cases r <;> simp) with rfl | rfl | rfl
  · simp [code, Code.marks]
  · have := h1 rfl
    simp only [code, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    split_ifs <;> simp only [Code.marks] <;> omega
  · have := h2 rfl
    simp only [code, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
    split_ifs <;> simp only [Code.marks] <;> omega

section Caps

variable {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {w : ℝ} {k : ℕ} {r : Fin 3}

theorem r_cases (r : Fin 3) : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp

theorem cap_hex (hw : 0 < w) (h0 : ∀ c d, 0 ≤ Y c d) (h : PT k r S T Y w) :
    Hex S T Y (w * (code k r).hsc) := by
  rcases r_cases r with rfl | rfl | rfl
  · simpa [code, Code.hsc] using pt_hex hw h0 h
  · have hk := pt_one_ge hw h
    unfold code
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    split_ifs with h1 h2 h3 h4 h5
    · exact pt_hexA hw h0 hk (by omega) h
    · exact pt_hexA hw h0 hk (by omega) h
    · exact pt_hexA hw h0 hk (by omega) h
    · exact pt_hexA hw h0 hk (by omega) h
    · simpa [Code.hsc] using pt_hex hw h0 h
    · simpa [Code.hsc] using pt_hex hw h0 h
  · have hk := pt_two_ge hw h
    unfold code
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
    split_ifs with h5
    · obtain rfl : k = 5 := by omega
      exact pt_hex5 h
    · exact pt_hexH hw h

theorem cap_M (hw : 0 < w) (hM : (code k r).isM = true) (h : PT k r S T Y w) :
    BijGe S T Y (w * (code k r).msc) 1 := by
  rcases r_cases r with rfl | rfl | rfl
  · simpa [code, Code.msc, Outerplanar.msc] using pt_bij hw (Or.inl rfl) h
  · have hk := pt_one_ge hw h
    unfold code at hM ⊢
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hM ⊢
    split_ifs at hM ⊢ with h1 h2
    · obtain rfl : k = 1 := by omega
      simpa [Code.msc, Outerplanar.msc] using pt_bij hw (Or.inr ⟨rfl, by norm_num⟩) h
    · subst h2
      simpa [Code.msc, Outerplanar.msc] using pt_bij hw (Or.inr ⟨rfl, le_rfl⟩) h
    all_goals simp [Code.isM] at hM
  · unfold code at hM
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hM
    split_ifs at hM <;> simp [Code.isM] at hM

theorem cap_pos (hw : 0 < w) (hM : (code k r).isM = true) (h : PT k r S T Y w) :
    ∀ c ∈ S, ∀ d ∈ T, c ≠ d → 0 < Y c d := by
  intro c hc d hd hcd
  rcases r_cases r with rfl | rfl | rfl
  · exact lt_of_lt_of_le hw ((h.1 rfl) c hc d hd hcd)
  · have hk := pt_one_ge hw h
    have h1 := h.2.1 rfl
    unfold code at hM
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hM
    split_ifs at hM with h1' h2
    · obtain rfl : k = 1 := by omega
      exact lt_of_lt_of_le (by positivity) (h1.1 c hc d hd hcd)
    · subst h2
      exact lt_of_lt_of_le (by positivity) (h1.1 c hc d hd hcd)
    all_goals simp [Code.isM] at hM
  · unfold code at hM
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hM
    split_ifs at hM <;> simp [Code.isM] at hM

theorem cap_hasPot (hS : S.card = 3) (hT : T.card = 3) (hw : 0 < w)
    (hM : (code k r).isM = true) (h : PT k r S T Y w) : HasPot S T Y (w * (code k r).msc) := by
  have := BijGe.hasPot hS hT (mul_pos hw (lt_of_lt_of_le one_pos (Code.msc_ge _))) one_pos
    (cap_pos hw hM h) (cap_M hw hM h)
  rwa [Real.one_rpow, mul_one] at this

theorem cap_B (hw : 0 < w) (h0 : ∀ c d, 0 ≤ Y c d) (hB : (code k r).hasB = true)
    (h : PT k r S T Y w) : InBall S T Y (w * (code k r).bsc) := by
  rcases r_cases r with rfl | rfl | rfl
  · simpa [code, Code.bsc] using pt_ball hw h0 (by decide) h
  · have hk := pt_one_ge hw h
    unfold code
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    split_ifs with h1 h2 h3 h4 h5
    · exact pt_ballA hk (by omega) h
    · exact pt_ballA hk (by omega) h
    · exact pt_ballA hk (by omega) h
    · simpa [Code.bsc] using pt_ball hw h0 (by decide) h
    · simpa [Code.bsc] using pt_ball hw h0 (by decide) h
    · simpa [Code.bsc] using pt_ball hw h0 (by decide) h
  · unfold code at hB
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hB
    split_ifs at hB <;> simp [Code.hasB] at hB

theorem cap_I (hI : code k r = .I) (h : PT k r S T Y w) : Dominant S T Y w := by
  rcases r_cases r with rfl | rfl | rfl
  · exact h.1 rfl
  · unfold code at hI
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hI
    split_ifs at hI
  · unfold code at hI
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hI
    split_ifs at hI

end Caps

/-! ### Closing with scales -/

/-- **Closing at `r` with scales**: the face read at `r` with the scales `s j` and the factor `κ`,
the root with the scale `t`, and `κ ∏ s · t ≥ 1`. -/
theorem close_scaled {m : ℕ} (C : Fin (m + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
    (G : Fin (m + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d) (w : Fin (m + 2) → ℝ)
    (hw : ∀ i, 0 < w i) (r : Fin (m + 2)) {κ t : ℝ} (s : Fin (m + 1) → ℝ) (hκ : 0 < κ)
    (hs : ∀ j, 0 < s j) (ht : 0 < t)
    (hface : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin m => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      (κ * faceConst3 m * ∏ j, (w (j.castSucc + (r + 1)) * s j)))
    (hroot : Hex (C r) (C (r + 1)) (G r) (w r * t)) (hsc : 1 ≤ κ * (∏ j, s j) * t) :
    6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
  have hP := Finset.prod_pos fun (j : Fin (m + 1)) (_ : j ∈ univ) => hw (j.castSucc + (r + 1))
  have hS := Finset.prod_pos fun (j : Fin (m + 1)) (_ : j ∈ univ) => hs j
  have hα := faceConst3_pos m
  have key := close_glue C hC G hG0 r (by
    rw [Finset.prod_mul_distrib]; positivity) (mul_pos (hw r) ht) hface hroot
  refine le_trans ?_ key
  rw [← prod_root w r, Finset.prod_mul_distrib]
  have e : κ * faceConst3 m * ((∏ j : Fin (m + 1), w (j.castSucc + (r + 1))) * ∏ j, s j)
      * (w r * t) = (κ * (∏ j, s j) * t)
        * (faceConst3 m * ((∏ j : Fin (m + 1), w (j.castSucc + (r + 1))) * w r)) := by ring
  rw [e]
  have h0 : 0 ≤ faceConst3 m * ((∏ j : Fin (m + 1), w (j.castSucc + (r + 1))) * w r) := by
    have := hw r; positivity
  have := mul_le_mul_of_nonneg_right hsc h0
  linarith

/-! ### The square laws at a root -/

section SqLaws

variable (C : Fin (2 + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
  (G : Fin (2 + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d) (w : Fin (2 + 2) → ℝ)
  (hw : ∀ i, 0 < w i) (τ : Fin (2 + 2) → ℕ) (ρ : Fin (2 + 2) → Fin 3)
  (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i))

include hC hG0 hw hpt

/-- The side at the path position `j` of the root `r`. -/
abbrev pos (r : Fin (2 + 2)) (j : Fin (2 + 1)) : Fin (2 + 2) := j.castSucc + (r + 1)

theorem sq_side (r : Fin (2 + 2)) (j : Fin (2 + 1)) :
    PT (τ (pos r j)) (ρ (pos r j))
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.castSucc)
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.succ)
      (G (pos r j)) (w (pos r j)) :=
  side_root (fun i S T Y => PT (τ i) (ρ i) S T Y (w i)) hpt r j

theorem sq_lists (r : Fin (2 + 2)) :
    (C r).card = 3 ∧ ∀ k : Fin 2, (C (k.castSucc.succ + (r + 1))).card = 3 :=
  ⟨hC r, fun k => hC _⟩

/-- `[M, M, M]` at the root `r`. -/
theorem sq_MMM (r : Fin (2 + 2)) (hM : ∀ j, (code (τ (pos r j)) (ρ (pos r j))).isM = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  have hP : ∀ j : Fin (2 + 1), HasPot
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.castSucc)
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.succ)
      (G (pos r j)) (w (pos r j) * (code (τ (pos r j)) (ρ (pos r j))).msc) := fun j => by
    have := sq_side C hC G hG0 w hw τ ρ hpt r j
    refine cap_hasPot ?_ ?_ (hw _) (hM j) this
    · rw [pathList_root]; exact hC _
    · rw [pathList_root]; exact hC _
  have key := hasPot_face3 (m := 2) le_rfl (C (r + 1)) (C r)
    (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) (hC _) (hC _) (fun k => hC _)
    (fun j => G (pos r j)) (fun j c d => hG0 _ c d) _
    (fun j => mul_pos (hw _) (lt_of_lt_of_le one_pos (Code.msc_ge _))) hP
  have hH := key.hex (hC _) (hC _) (by
    have := faceConst3_pos 2
    have := Finset.prod_pos fun j (_ : j ∈ univ) =>
      mul_pos (hw (pos r j)) (lt_of_lt_of_le one_pos (Code.msc_ge (code (τ (pos r j)) (ρ (pos r j)))))
    positivity)
  refine close_scaled C hC G hG0 w hw r (κ := 1) (t := (code (τ r) (ρ r)).hsc)
    (fun j => (code (τ (pos r j)) (ρ (pos r j))).msc) one_pos
    (fun j => lt_of_lt_of_le one_pos (Code.msc_ge _))
    (lt_of_lt_of_le one_pos (Code.hsc_ge _)) (by rw [one_mul]; exact hH)
    (cap_hex (hw r) (hG0 r) (hpt r)) ?_
  rw [one_mul]
  exact one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun j _ => Code.msc_ge _)
    (Code.hsc_ge _)

/-- `[B, M, M]` at the root `r`, the ball side at the position `q`. -/
theorem sq_BMM (r : Fin (2 + 2)) (q : Fin (2 + 1))
    (hB : (code (τ (pos r q)) (ρ (pos r q))).hasB = true)
    (hM : ∀ j, j ≠ q → (code (τ (pos r j)) (ρ (pos r j))).isM = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => if j = q then (code (τ (pos r j)) (ρ (pos r j))).bsc
    else (code (τ (pos r j)) (ρ (pos r j))).msc with hs
  have hspos : ∀ j, 0 < s j := fun j => by
    simp only [hs]; split_ifs
    · exact lt_of_lt_of_le one_pos (Code.bsc_ge _)
    · exact lt_of_lt_of_le one_pos (Code.msc_ge _)
  have key : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      (faceConst3 2 * ∏ j : Fin (2 + 1), (w (pos r j) * s j)) :=
    sqLawB (hC r) (fun k => hC _) (fun j => G (pos r j)) (fun j c d => hG0 _ c d)
      (fun j => w (pos r j) * s j) (fun j => mul_pos (hw _) (hspos j)) q
      (by simpa [hs] using cap_B (hw _) (hG0 _) hB (sq_side C hC G hG0 w hw τ ρ hpt r q))
      fun j hj => by
        simpa [hs, hj] using cap_M (hw _) (hM j hj) (sq_side C hC G hG0 w hw τ ρ hpt r j)
  refine close_scaled C hC G hG0 w hw r (κ := 1) (t := (code (τ r) (ρ r)).hsc) s one_pos hspos
    (lt_of_lt_of_le one_pos (Code.hsc_ge _)) (by rw [one_mul]; exact key)
    (cap_hex (hw r) (hG0 r) (hpt r)) ?_
  rw [one_mul]
  refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun j _ => ?_) (Code.hsc_ge _)
  simp only [hs]; split_ifs
  · exact Code.bsc_ge _
  · exact Code.msc_ge _

/-- `[H, M, M]` at the root `r`, the hexagon side at the position `q`. -/
theorem sq_HMM (r : Fin (2 + 2)) (q : Fin (2 + 1)) (hr : (code (τ r) (ρ r)).hbig = true)
    (hH : (code (τ (pos r q)) (ρ (pos r q))).hbig = true)
    (hM : ∀ j, j ≠ q → (code (τ (pos r j)) (ρ (pos r j))).isM = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => if j = q then (code (τ (pos r j)) (ρ (pos r j))).hsc
    else (code (τ (pos r j)) (ρ (pos r j))).msc with hs
  have hspos : ∀ j, 0 < s j := fun j => by
    simp only [hs]; split_ifs
    · exact lt_of_lt_of_le one_pos (Code.hsc_ge _)
    · exact lt_of_lt_of_le one_pos (Code.msc_ge _)
  have key : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      (56 / 59 * faceConst3 2 * ∏ j : Fin (2 + 1), (w (pos r j) * s j)) :=
    sqLawH (hC r) (fun k => hC _) (fun j => G (pos r j)) (fun j c d => hG0 _ c d)
      (fun j => w (pos r j) * s j) (fun j => mul_pos (hw _) (hspos j)) q
      (by simpa [hs] using cap_hex (hw _) (hG0 _) (sq_side C hC G hG0 w hw τ ρ hpt r q))
      fun j hj => by
        simpa [hs, hj] using cap_M (hw _) (hM j hj) (sq_side C hC G hG0 w hw τ ρ hpt r j)
  refine close_scaled C hC G hG0 w hw r (κ := 56 / 59) (t := (code (τ r) (ρ r)).hsc) s
    (by norm_num) hspos (lt_of_lt_of_le one_pos (Code.hsc_ge _)) key
    (cap_hex (hw r) (hG0 r) (hpt r)) ?_
  have hq : d6 ≤ s q := by simp only [hs, ite_true]; exact Code.hsc_big hH
  have hrest : s q ≤ ∏ j, s j := by
    rw [← Finset.mul_prod_erase univ s (mem_univ q)]
    have : 1 ≤ ∏ j ∈ univ.erase q, s j := Finset.one_le_prod₀ fun j hj => by
      simp only [hs, Finset.ne_of_mem_erase hj, ite_false]; exact Code.msc_ge _
    nlinarith [hspos q]
  have ht := Code.hsc_big hr
  have := d6_sq
  have := d6_pos
  nlinarith

/-- `[B, B, B]` at the root `r`. -/
theorem sq_BBB (r : Fin (2 + 2)) (hB : ∀ j, (code (τ (pos r j)) (ρ (pos r j))).hasB = true)
    (hA2 : 2 ≤ (if (code (τ r) (ρ r)).hA then 1 else 0)
      + ∑ j, (if (code (τ (pos r j)) (ρ (pos r j))).bA then 1 else 0)) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => (code (τ (pos r j)) (ρ (pos r j))).bsc with hs
  have hspos : ∀ j, 0 < s j := fun j => lt_of_lt_of_le one_pos (Code.bsc_ge _)
  have key : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      ((16 / 17) ^ 2 * faceConst3 2 * ∏ j : Fin (2 + 1), (w (pos r j) * s j)) :=
    sqLawBBB (hC r) (fun k => hC _) (fun j => G (pos r j)) (fun j c d => hG0 _ c d)
      (fun j => w (pos r j) * s j) (fun j => mul_pos (hw _) (hspos j))
      fun j => cap_B (hw _) (hG0 _) (hB j) (sq_side C hC G hG0 w hw τ ρ hpt r j)
  refine close_scaled C hC G hG0 w hw r (κ := (16 / 17) ^ 2) (t := (code (τ r) (ρ r)).hsc) s
    (by norm_num) hspos (lt_of_lt_of_le one_pos (Code.hsc_ge _)) key
    (cap_hex (hw r) (hG0 r) (hpt r)) ?_
  -- each `A` flag gives a factor `17/16`
  have hbnd : ∀ j, (17 / 16 : ℝ) ^ (if (code (τ (pos r j)) (ρ (pos r j))).bA then 1 else 0)
      ≤ s j := fun j => by
    simp only [hs]
    split_ifs with h
    · simpa using Code.bsc_A h
    · simpa using Code.bsc_ge _
  have hbt : (17 / 16 : ℝ) ^ (if (code (τ r) (ρ r)).hA then 1 else 0) ≤ (code (τ r) (ρ r)).hsc := by
    split_ifs with h
    · simpa using Code.hsc_A h
    · simpa using Code.hsc_ge _
  have hprod : (17 / 16 : ℝ) ^ (∑ j, (if (code (τ (pos r j)) (ρ (pos r j))).bA then 1 else 0))
      ≤ ∏ j, s j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => hbnd j
  have htot : (17 / 16 : ℝ) ^ 2 ≤ (∏ j, s j) * (code (τ r) (ρ r)).hsc := by
    calc (17 / 16 : ℝ) ^ 2 ≤ (17 / 16) ^ ((if (code (τ r) (ρ r)).hA then 1 else 0)
          + ∑ j, (if (code (τ (pos r j)) (ρ (pos r j))).bA then 1 else 0)) :=
          pow_le_pow_right₀ (by norm_num) hA2
      _ = (17 / 16 : ℝ) ^ (∑ j, (if (code (τ (pos r j)) (ρ (pos r j))).bA then 1 else 0))
          * (17 / 16) ^ (if (code (τ r) (ρ r)).hA then 1 else 0) := by rw [pow_add, mul_comm]
      _ ≤ _ := mul_le_mul hprod hbt (by positivity) (Finset.prod_pos fun j _ => hspos j).le
  calc (1 : ℝ) = (16 / 17) ^ 2 * (17 / 16) ^ 2 := by norm_num
    _ ≤ (16 / 17) ^ 2 * ((∏ j, s j) * (code (τ r) (ρ r)).hsc) :=
        mul_le_mul_of_nonneg_left htot (by norm_num)
    _ = _ := by ring

/-- `[H, H, H]` at the root `r`: all four sides in `A H`. -/
theorem sq_HHH (r : Fin (2 + 2)) (hr : (code (τ r) (ρ r)).hA = true)
    (hH : ∀ j, (code (τ (pos r j)) (ρ (pos r j))).hA = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => (code (τ (pos r j)) (ρ (pos r j))).hsc with hs
  have hspos : ∀ j, 0 < s j := fun j => lt_of_lt_of_le one_pos (Code.hsc_ge _)
  have key : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (r + 1))))
      ((16 / 17) ^ 4 * faceConst3 2 * ∏ j : Fin (2 + 1), (w (pos r j) * s j)) :=
    sqLawHHH (hC r) (fun k => hC _) (fun j => G (pos r j)) (fun j c d => hG0 _ c d)
      (fun j => w (pos r j) * s j) (fun j => mul_pos (hw _) (hspos j))
      fun j => cap_hex (hw _) (hG0 _) (sq_side C hC G hG0 w hw τ ρ hpt r j)
  refine close_scaled C hC G hG0 w hw r (κ := (16 / 17) ^ 4) (t := (code (τ r) (ρ r)).hsc) s
    (by norm_num) hspos (lt_of_lt_of_le one_pos (Code.hsc_ge _)) key
    (cap_hex (hw r) (hG0 r) (hpt r)) ?_
  have hprod : (17 / 16 : ℝ) ^ 3 ≤ ∏ j, s j := by
    rw [show (17 / 16 : ℝ) ^ 3 = ∏ _j : Fin (2 + 1), (17 / 16 : ℝ) by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    exact Finset.prod_le_prod₀ (fun j _ => by norm_num) fun j _ => Code.hsc_A (hH j)
  have ht := Code.hsc_A hr
  calc (1 : ℝ) = (16 / 17) ^ 4 * ((17 / 16) ^ 3 * (17 / 16)) := by norm_num
    _ ≤ (16 / 17) ^ 4 * ((∏ j, s j) * (code (τ r) (ρ r)).hsc) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hprod ht (by norm_num)
          (Finset.prod_pos fun j _ => hspos j).le) (by norm_num)
    _ = _ := by ring

/-- `three_heavy` at a constant root `r`: the three path sides in `A H`. -/
theorem sq_HHHc (r : Fin (2 + 2)) (hr : code (τ r) (ρ r) = .I)
    (hH : ∀ j, (code (τ (pos r j)) (ρ (pos r j))).hA = true) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set s : Fin (2 + 1) → ℝ := fun j => (code (τ (pos r j)) (ρ (pos r j))).hsc with hs
  have hspos : ∀ j, 0 < s j := fun j => lt_of_lt_of_le one_pos (Code.hsc_ge _)
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two (C (r + 1)) (C r)
    (fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
  have hX : ∀ j : Fin (2 + 1), Hex
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.castSucc)
      (pathList (C (r + 1)) (C r) (fun k : Fin 2 => C (k.castSucc.succ + (r + 1))) j.succ)
      (G (pos r j)) (w (pos r j) * s j) :=
    fun j => cap_hex (hw _) (hG0 _) (sq_side C hC G hG0 w hw τ ρ hpt r j)
  have h0 := hX 0
  have h1 := hX 1
  have h2 := hX 2
  rw [l0, l1] at h0
  rw [l2, l3] at h1
  rw [l4, l5] at h2
  have key := SqMulti.sq_HHH_close (Li := fun k : Fin 2 => C (k.castSucc.succ + (r + 1)))
    (hC (r + 1)) (hC r) (fun k => hC _) (W := fun j => G (pos r j))
    (fun j c d => hG0 _ c d) (N := fun j => w (pos r j) * s j)
    (fun j => mul_pos (hw _) (hspos j)) h0 h1 h2
  have hroot := cap_I hr (hpt r)
  have hcl := close_count C G hG0 r (hw r).le hroot key
  refine le_trans ?_ hcl
  rw [← prod_root w r]
  have a0 := Code.hsc_A (hH 0)
  have a1 := Code.hsc_A (hH 1)
  have a2 := Code.hsc_A (hH 2)
  have hprod : (17 / 16 : ℝ) ^ 3 ≤ s 0 * s 1 * s 2 := by
    have e3 : (17 / 16 : ℝ) ^ 3 = 17 / 16 * (17 / 16) * (17 / 16) := by ring
    rw [e3]
    exact mul_le_mul (mul_le_mul a0 a1 (by norm_num) (hspos 0).le) a2 (by norm_num)
      (mul_pos (hspos 0) (hspos 1)).le
  have hge : 1 ≤ (16 / 17 : ℝ) ^ 3 * (s 0 * s 1 * s 2) := by
    have : (1 : ℝ) = (16 / 17) ^ 3 * (17 / 16) ^ 3 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left hprod (by norm_num)
  have ep : ∏ j : Fin (2 + 1), w (pos r j) = w (pos r 0) * w (pos r 1) * w (pos r 2) := by
    exact Fin.prod_univ_three _
  rw [ep, faceConst3_two]
  have hW : 0 ≤ w (pos r 0) * w (pos r 1) * w (pos r 2) * w r := by
    have := hw (pos r 0); have := hw (pos r 1); have := hw (pos r 2); have := hw r
    positivity
  have e1 : 6 * (3 * (w (pos r 0) * w (pos r 1) * w (pos r 2) * w r))
      = (w (pos r 0) * w (pos r 1) * w (pos r 2) * w r) * 18 * 1 := by ring
  have e2 : w r * (18 * (16 / 17) ^ 3 * (w (pos r 0) * s 0 * (w (pos r 1) * s 1)
      * (w (pos r 2) * s 2)))
      = (w (pos r 0) * w (pos r 1) * w (pos r 2) * w r) * 18
        * ((16 / 17 : ℝ) ^ 3 * (s 0 * s 1 * s 2)) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hge (by positivity)

end SqLaws

end Outerplanar
