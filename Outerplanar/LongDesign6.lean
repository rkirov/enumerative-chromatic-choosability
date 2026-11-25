/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.WalkDesign

/-!
# Faces of length six with every path edge loaded

A hexagon maps the ball class on all its path edges to the ball class on its root edge, with the
factor `16/17` (**`ballHex`**). Together with `ballEvenLong` (`Outerplanar/LongDesign8.lean`) this
covers every even face of length at least six (`ballEvenSix`).

The five-step path is handled by `walks_ball_design` (`Outerplanar/WalkDesign.lean`), with one
certificate for each of the six bijections `σ` of the indices (`hexCert_*`). A certificate is a
list of integer multiplicities, `e = 360` in total, on the walks of each of the six cells; it is
balanced, and it comes with cell constants `num_k / 2^32` that satisfy
`num_k^360 · ∏ c^c ≤ 360^360 · 2^(32·360)` and
`(176/17)^600 ≤ (∏_{k ≠ j} N_k)^100 N_j^91 10^9` for every `j`. The moved weight is charged at the
walk count `10` of a cell whose ends have the same index. The numbers come from a maximum-entropy
program rounded to integers (`ai_research_notes/outerplanar/t4b_m1/emit_hex6.py`); the kernel checks
them by `decide +kernel`. The certified margins in logarithms are `0.059` (identity), `0.024`
(transpositions) and `0.0073` (rotations).

This is the hexagon lemma of the research note
`ai_research_notes/OUTERPLANAR_BRANCHING_SQUARES_2026-11-23.md` ("Hexagon L = 6"; another AI session
of this repository's collaboration). The note's certificate (`hexagon_gain.py`) uses different
weights and the total-variation form of the move; here the move is charged crudely and the weights
are re-derived. Formalized by Claude.
-/

namespace Outerplanar

open Finset

/-- The common denominator of the cell constants. -/
def hexD : ℕ := 2 ^ 32

/-- The multiplicities of the design for `σ = id`. -/
def hexNs_id : Fin 6 → List ℕ :=
  ![[33, 32, 32, 33, 32, 33, 33, 33, 33, 33, 33],
    [33, 33, 33, 33, 33, 33, 32, 32, 32, 33, 33],
    [33, 33, 32, 33, 32, 32, 33, 33, 33, 33, 33],
    [32, 33, 33, 33, 33, 33, 33, 33, 32, 32, 33],
    [33, 33, 32, 33, 33, 33, 32, 33, 33, 32, 33],
    [33, 33, 32, 32, 33, 33, 33, 33, 33, 33, 32]]

/-- The cell constants (over `2 ^ 32`) of the design for `σ = id`. -/
def hexNum_id : Fin 6 → ℕ := ![47240245425, 47240245425, 47240245425, 47240245425, 47240245425, 47240245425]

/-- The multiplicities of the design for `σ = p1`. -/
def hexNs_p1 : Fin 6 → List ℕ :=
  ![[40, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32],
    [40, 40, 40, 40, 32, 40, 32, 32, 32, 32],
    [40, 40, 40, 40, 32, 40, 32, 32, 32, 32],
    [40, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32],
    [40, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32],
    [40, 40, 40, 40, 32, 40, 32, 32, 32, 32]]

/-- The cell constants (over `2 ^ 32`) of the design for `σ = p1`. -/
def hexNum_p1 : Fin 6 → ℕ := ![47135118631, 42684823264, 42684823264, 47135118631, 47135118631, 42684823264]

/-- The multiplicities of the design for `σ = p2`. -/
def hexNs_p2 : Fin 6 → List ℕ :=
  ![[32, 32, 32, 32, 40, 32, 40, 40, 40, 40],
    [32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 40],
    [32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 40],
    [32, 32, 32, 32, 40, 32, 40, 40, 40, 40],
    [32, 32, 32, 32, 40, 32, 40, 40, 40, 40],
    [32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 40]]

/-- The cell constants (over `2 ^ 32`) of the design for `σ = p2`. -/
def hexNum_p2 : Fin 6 → ℕ := ![42684823264, 47135118631, 47135118631, 42684823264, 42684823264, 47135118631]

/-- The multiplicities of the design for `σ = t0`. -/
def hexNs_t0 : Fin 6 → List ℕ :=
  ![[39, 34, 34, 39, 39, 34, 34, 34, 39, 34],
    [34, 34, 39, 34, 34, 34, 29, 29, 29, 30, 34],
    [34, 39, 34, 34, 34, 39, 39, 34, 34, 39],
    [34, 30, 29, 29, 29, 34, 34, 34, 39, 34, 34],
    [34, 34, 29, 30, 34, 29, 29, 34, 34, 39, 34],
    [34, 39, 34, 34, 29, 29, 34, 30, 29, 34, 34]]

/-- The cell constants (over `2 ^ 32`) of the design for `σ = t0`. -/
def hexNum_t0 : Fin 6 → ℕ := ![42851199107, 47049248306, 42851199107, 47049248306, 47049248306, 47049248306]

/-- The multiplicities of the design for `σ = t1`. -/
def hexNs_t1 : Fin 6 → List ℕ :=
  ![[34, 34, 29, 30, 34, 29, 29, 34, 34, 39, 34],
    [34, 39, 34, 34, 29, 29, 34, 30, 29, 34, 34],
    [34, 34, 39, 34, 34, 34, 29, 29, 30, 29, 34],
    [39, 34, 34, 39, 39, 34, 34, 34, 39, 34],
    [34, 29, 30, 29, 29, 34, 34, 34, 39, 34, 34],
    [34, 39, 34, 34, 34, 39, 39, 34, 34, 39]]

/-- The cell constants (over `2 ^ 32`) of the design for `σ = t1`. -/
def hexNum_t1 : Fin 6 → ℕ := ![47049248306, 47049248306, 47049248306, 42851199107, 47049248306, 42851199107]

/-- The multiplicities of the design for `σ = t2`. -/
def hexNs_t2 : Fin 6 → List ℕ :=
  ![[34, 29, 30, 29, 29, 34, 34, 34, 39, 34, 34],
    [34, 39, 34, 34, 34, 39, 39, 34, 34, 39],
    [34, 39, 34, 34, 30, 29, 34, 29, 29, 34, 34],
    [34, 34, 29, 29, 34, 29, 30, 34, 34, 39, 34],
    [39, 34, 34, 39, 39, 34, 34, 34, 39, 34],
    [34, 34, 39, 34, 34, 34, 29, 29, 30, 29, 34]]

/-- The cell constants (over `2 ^ 32`) of the design for `σ = t2`. -/
def hexNum_t2 : Fin 6 → ℕ := ![47049248306, 42851199107, 47049248306, 47049248306, 42851199107, 47049248306]

/-- **The certificate of a hexagon design**: lengths, totals, balance, cell constants and the
final inequality. -/
def HexCert (σ : Fin 3 → Fin 3) (ns : Fin 6 → List ℕ) (num : Fin 6 → ℕ) : Prop :=
  (∀ k, (cw 5 (offPair k).1 (σ (offPair k).2)).length = (ns k).length) ∧
  (∀ k, (ns k).sum = 360) ∧ Balanced (dfam 5 σ ns) 5 360 ∧
  (∀ k, num k ^ 360 * ((ns k).map fun c => c ^ c).prod ≤ 360 ^ 360 * hexD ^ 360) ∧
  (∀ j, 176 ^ 600 * hexD ^ 591 ≤ 17 ^ 600 * (∏ k ∈ univ.erase j, num k) ^ 100 * num j ^ 91 * 10 ^ 9)

instance (σ : Fin 3 → Fin 3) (ns : Fin 6 → List ℕ) (num : Fin 6 → ℕ) :
    Decidable (HexCert σ ns num) := by
  unfold HexCert; infer_instance

theorem hexCert_id : HexCert id hexNs_id hexNum_id := by decide +kernel

theorem hexCert_p1 : HexCert (· + 1) hexNs_p1 hexNum_p1 := by decide +kernel

theorem hexCert_p2 : HexCert (· + 2) hexNs_p2 hexNum_p2 := by decide +kernel

theorem hexCert_t0 : HexCert (tr 0) hexNs_t0 hexNum_t0 := by decide +kernel

theorem hexCert_t1 : HexCert (tr 1) hexNs_t1 hexNum_t1 := by decide +kernel

theorem hexCert_t2 : HexCert (tr 2) hexNs_t2 hexNum_t2 := by decide +kernel

/-! ### The ball inequalities of a five-step path -/

theorem hex_designs (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ) :
    ∃ (ns : Fin 6 → List ℕ) (num : Fin 6 → ℕ), HexCert σ ns num := by
  rcases inj_cases σ hσ with rfl | rfl | rfl | ⟨a, rfl⟩
  · exact ⟨_, _, hexCert_id⟩
  · exact ⟨_, _, hexCert_p1⟩
  · exact ⟨_, _, hexCert_p2⟩
  · fin_cases a
    · exact ⟨_, _, hexCert_t0⟩
    · exact ⟨_, _, hexCert_t1⟩
    · exact ⟨_, _, hexCert_t2⟩

/-- Clearing the denominators of the final inequality. -/
theorem fin_bridge {a b P n D g : ℝ} (hb : 0 < b) (hD : 0 < D)
    (h : a * D ^ 591 ≤ b * P ^ 100 * n ^ 91 * g) :
    a / b ≤ (P / D ^ 5) ^ 100 * (n / D) ^ 91 * g := by
  rw [div_le_iff₀ hb]
  have e : (P / D ^ 5) ^ 100 * (n / D) ^ 91 * g * b = b * P ^ 100 * n ^ 91 * g / D ^ 591 := by
    field_simp
  rw [e, le_div_iff₀ (pow_pos hD _)]
  exact h

theorem hex_fin_real (num : Fin 6 → ℕ) (j : Fin 6)
    (h : 176 ^ 600 * hexD ^ 591 ≤ 17 ^ 600 * (∏ k ∈ univ.erase j, num k) ^ 100 * num j ^ 91 * 10 ^ 9) :
    (176 / 17 : ℝ) ^ 600
      ≤ (∏ k ∈ univ.erase j, ((num k : ℝ) / hexD)) ^ 100 * ((num j : ℝ) / hexD) ^ 91 * 10 ^ 9 := by
  have hD : (0 : ℝ) < hexD := by unfold hexD; positivity
  have e1 : ∏ k ∈ univ.erase j, ((num k : ℝ) / hexD)
      = ((∏ k ∈ univ.erase j, num k : ℕ) : ℝ) / (hexD : ℝ) ^ 5 := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_erase_of_mem (mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    push_cast
    rfl
  rw [e1, div_pow]
  refine fin_bridge (by positivity) hD ?_
  exact_mod_cast h

theorem ten_le_cnt_five (c d : Fin 3) : (10 : ℝ) ≤ cnt 5 c d := by
  have h1 : sN 5 = 10 := by decide
  have h2 : dN 5 = 11 := by decide
  unfold cnt
  split_ifs
  · rw [h1]; norm_num
  · rw [h2]; norm_num

/-- **The ball inequalities of a path of five steps**, for every bijection `σ`, weight being
moved to any cell, with the constant `176/17 = (16/17) · 11`. -/
theorem walks_ball_hex (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (hlen : Ms.length = 5)
    (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ)
    (j : Fin 6) (c d : Fin 3) :
    ((176 / 17 : ℝ) * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (σ (offPair k).2)) ^ 100
        * pw Ms (offPair j).1 (σ (offPair j).2) ^ 91 * pw Ms c d ^ 9 := by
  obtain ⟨ns, num, h1, h2, h3, h4, h5⟩ := hex_designs σ hσ
  exact walks_ball_design Ms As hM hA hball σ ns 360 (by norm_num) num hexD
    (by unfold hexD; positivity) (by norm_num) (by norm_num) (by rw [hlen]; exact h1) h2
    (by rw [hlen]; exact h3) h4 (fun j => hex_fin_real num j (h5 j))
    (by rw [hlen]; exact ten_le_cnt_five) j c d

/-! ### The face -/

/-- **A hexagon maps the ball class on all its path edges to the ball class on its root edge**,
with the factor `16/17`. -/
theorem ballHex (Lu Lv : Finset ℕ) (Li : Fin 4 → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin 5 → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin 5 → ℝ) (hA : ∀ j, 0 < A j)
    (hE : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (16 / 17 * faceConst3 4 * ∏ j, A j) := by
  refine inBall_of_idx hLu hLv fun α β hα hβ hαm hβm _ => ⟨id, Function.bijective_id, ?_⟩
  intro j c d _
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
  obtain ⟨ζs, hζs, hOff, hMnn⟩ := frames Vs (List.ofFn E) (List.ofFn A) Lu α hα hαm hVcard hEs0
    (chain_of_fin Lu Lv Li E A hE)
  have hlenV : Vs.length = 5 := by simp [hVs]
  have hlenE : (List.ofFn E).length = 5 := List.length_ofFn
  have hlenζ : ζs.length = 5 := by rw [hζs.length_eq, hlenV]
  set Ms := mkMs α ζs (List.ofFn E) with hMs
  have hlenM : Ms.length = 5 := by
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
  have key := walks_ball_hex Ms (List.ofFn A) hlenM hMnn hAs hOff σ hσinj j c (σ d)
  have hp := pw_nonneg Ms hMnn
  have hcell : ∀ a b : Fin 3, pw Ms a (σ b) ≤ faceSum Li (fun _ _ => 1) E (α a) (β b) :=
    fun a b => by
      rw [faceSum_eq_psum Li Lv E (α a) (β b) (hβm b), ← hσ b]
      exact pw_le_psum Vs (List.ofFn E) ζs α (by rw [hlenE, hlenV]) hζs hEs0 a (σ b)
  show (16 / 17 * faceConst3 4 * ∏ j, A j) ^ 600
    ≤ (∏ k ∈ univ.erase j, faceSum Li (fun _ _ => 1) E (α (offPair k).1) (β (offPair k).2)) ^ 100
      * faceSum Li (fun _ _ => 1) E (α (offPair j).1) (β (offPair j).2) ^ 91
      * faceSum Li (fun _ _ => 1) E (α c) (β d) ^ 9
  have h11 : faceConst3 4 = 11 := by
    rw [faceConst3_eq_dN, show dN (4 + 1) = 11 by decide]; norm_num
  calc (16 / 17 * faceConst3 4 * ∏ j, A j) ^ 600
      = ((176 / 17 : ℝ) * (List.ofFn A).prod) ^ 600 := by
        rw [h11, List.prod_ofFn]; norm_num
    _ ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (σ (offPair k).2)) ^ 100
        * pw Ms (offPair j).1 (σ (offPair j).2) ^ 91 * pw Ms c (σ d) ^ 9 := key
    _ ≤ _ := by
        refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (prod_nonneg fun k _ => hp _ _)
          (Finset.prod_le_prod₀ (fun k _ => hp _ _) fun k _ => hcell _ _) _)
          (pow_le_pow_left₀ (hp _ _) (hcell _ _) _) (pow_nonneg (hp _ _) _)
          (pow_nonneg (prod_nonneg fun k _ => (hp _ _).trans (hcell _ _)) _))
          (pow_le_pow_left₀ (hp _ _) (hcell _ _) _) (pow_nonneg (hp _ _) _)
          (mul_nonneg (pow_nonneg (prod_nonneg fun k _ => (hp _ _).trans (hcell _ _)) _)
            (pow_nonneg ((hp _ _).trans (hcell _ _)) _))

/-- **Every even face of length at least six maps the ball class on all its path edges to the
ball class on its root edge**, with the factor `16/17`. -/
theorem ballEvenSix (m : ℕ) (hev : Even m) (h4 : 4 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (16 / 17 * faceConst3 m * ∏ j, A j) := by
  rcases Nat.lt_or_ge m 6 with h | h
  · obtain rfl : m = 4 := by obtain ⟨k, hk⟩ := hev; omega
    exact ballHex Lu Lv Li hLu hLv hLi E hE0 A hA hE
  · exact ballEvenLong m hev h Lu Lv Li hLu hLv hLi E hE0 A hA hE

end Outerplanar

/-- info: 'Outerplanar.ballEvenSix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Outerplanar.ballEvenSix
