/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Sq15Check
import Outerplanar.SqMultiCover
import Outerplanar.MarkFiveSix

/-!
# Squares with three loaded edges: soundness of the fifteen-face records

* `GoodB md tn td Q` — every choice of tables in the classes `md` puts the face of the pattern
  `Q` in the ball class at the root (`IdxBallAt id`, constant `N₀ N₁ N₂ tn / td`); monotone
  under `PatLE` (`GoodB.mono`), and it follows from the ball data of `Outerplanar/Sq15Check.lean`
  (`goodB_of_data`): one `checkR` record per test `(j, c)`; the test `c = j` (the hexagon bound)
  is the geometric mean of the tests `(j, j + 1)` and `(j + 1, j)`.
* `LCls md S T W N` — the class of a path edge with the constants of a `Mode`, on lists
  (floor: `Dominant`; bijections: `BijGe`; six-families; ball: `InBall`), read in index form by
  `edgeOK_of_lcls`; `LCls.swap`.
* `sq_ball_of_good'`, `sq_hex_of_good'`, `sq_close_of_good'` — the list-level theorems for the
  52 patterns of the cover `SqData.qs`, for any three modes (the analogues of `sq_hex_of_good`).
* Reflection of a square (`revL`, `revW`, `faceSum_rev`; `inBall_rev`, `hex_rev`, `close_rev`):
  the square `u x₀ x₁ v` read from `v` is the square `v x₁ x₀ u` with transposed tables.
* The classes of the fifteen-face square lemmas on lists (`ClsZ`, `ClsW`, `ClsABf`, `ClsBAHf`,
  `ClsBf5`, `ClsBf6`, `ClsH7f`, and `Dominant · · · N` for a plain side), with `.lcls` and `.swap`.

Part of milestone M4 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`.
-/

namespace Outerplanar.SqMulti

open Finset

/-! ### The ball property of a pattern -/

/-- The ball class at the root of a pattern, for tables in the classes `md`. -/
def GoodB (md : ℕ → Mode) (tn td : ℕ) (Q : Pat) : Prop :=
  ∀ (w : ℕ → Fin 3 → Fin 3 → ℝ) (N : ℕ → ℝ), (∀ j < 3, 0 < N j) →
    (∀ j < 3, EdgeOK (md j) (patE Q j) (w j) (N j)) →
    IdxBallAt id Q.e03 (faceP Q w) (N 0 * N 1 * N 2 * tn / td)

theorem GoodB.mono {md : ℕ → Mode} {tn td : ℕ} {P Q : Pat} (h : PatLE P Q)
    (hQ : GoodB md tn td Q) : GoodB md tn td P := by
  intro w N hN hE
  have hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y := fun j hj => (hE j hj).nonneg
  have key := hQ w N hN fun j hj => (hE j hj).mono_E (patE_le h)
  rw [h.h03]
  exact key.mono (faceP_nonneg hw) (faceP_mono h hw)

/-! ### From the records to the ball property -/

theorem bw_self (j : ℕ) : bw j j = 91 := by simp [bw]

theorem bw_ne {j k : ℕ} (h : k ≠ j) : bw j k = 100 := by simp [bw, h]

/-- The exponents of a ball test against the product over the family. -/
theorem ballAt_eq (F : Fin 6 → ℝ) (j : Fin 6) :
    (∏ k ∈ univ.erase j, F k) ^ 100 * F j ^ 91 = ∏ k, F k ^ bw j.val k.val := by
  rw [← Finset.mul_prod_erase univ (fun k => F k ^ bw j.val k.val) (mem_univ j), bw_self,
    ← Finset.prod_pow]
  have : ∀ k ∈ univ.erase j, F k ^ bw j.val k.val = F k ^ 100 := fun k hk => by
    rw [bw_ne fun e => (Finset.mem_erase.mp hk).1 (Fin.ext e)]
  rw [Finset.prod_congr rfl this]
  ring

theorem ball_mid (F : Fin 6 → ℝ) (j : Fin 6) :
    (∏ k, F k ^ bw j.val k.val) * F j ^ 9 = (∏ k, F k) ^ 100 := by
  rw [← ballAt_eq, ← Finset.prod_erase_mul univ F (mem_univ j)]
  ring

theorem rTot_bRows {j : ℕ} (hj : j < 6) (c : ℕ) : rTot (bRows j c) = 600 := by
  interval_cases j <;> rfl

theorem famCell_spec : ∀ j : Fin 6, famCell j.val = 3 * (offPair j).1.val + (offPair j).2.val := by
  decide

theorem famCell_inj : ∀ j j' : Fin 6, famCell j.val = famCell j'.val → j = j' := by decide

theorem cell_fam : ∀ (j : Fin 6) (c d : Fin 3), 3 * c.val + d.val = famCell j.val →
    (c, d) = offPair j := by decide

theorem eqc_root (pat : ℕ) (c d : Fin 3) :
    (patOfCode pat).e03 c d = eqc pat 3 (3 * c.val + d.val) := by
  show bitAt pat (27 + 3 * c.val + d.val) = bit pat (9 * 3 + (3 * c.val + d.val))
  rw [bit_eq]
  congr 1
  omega

theorem fin6_succ_ne : ∀ j : Fin 6, j + 1 ≠ j := by decide

/-- The product over the rows of a ball test. -/
theorem rows_prod (pat : ℕ) (w : ℕ → Fin 3 → Fin 3 → ℝ) (j : Fin 6) (c d : Fin 3) :
    ∏ i ∈ range (bRows j.val (3 * c.val + d.val)).length,
        faceN pat w (rA (bRows j.val (3 * c.val + d.val)) i)
          (rB (bRows j.val (3 * c.val + d.val)) i) ^ rN (bRows j.val (3 * c.val + d.val)) i
      = (∏ k : Fin 6, faceP (patOfCode pat) w (offPair k).1 (offPair k).2 ^ bw j.val k.val)
        * faceP (patOfCode pat) w c d ^ 9 := by
  have hl : (bRows j.val (3 * c.val + d.val)).length = 7 := rfl
  rw [hl]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Fin.prod_univ_six]
  have e : ∀ (a b : Fin 3), faceN pat w a.val b.val = faceP (patOfCode pat) w a b :=
    faceN_faceP pat w
  have hc : faceN pat w ((3 * c.val + d.val) / 3) ((3 * c.val + d.val) % 3)
      = faceP (patOfCode pat) w c d := by rw [cell_div, cell_mod]; exact e c d
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e01 e02 e10 e12 e20 e21
  simp only [rA, rB, rN, bRows, List.getD_cons_zero, List.getD_cons_succ]
  rw [e01, e02, e10, e12, e20, e21, hc]
  rfl

theorem allCert_mem {md : ℕ → Mode} {pat tn td : ℕ} :
    ∀ {l : List Cert}, AllCert md pat tn td l → ∀ x ∈ l, certB md pat tn td x = true
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: l, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact allCert_mem h.2 x hx

theorem covers_spec {pat : ℕ} {l : List Cert} (h : covers pat l = true) :
    (∀ j < 6, eqc pat 3 (famCell j) = false) ∧
    ∀ j < 6, ∀ c < 9, eqc pat 3 c = false → c ≠ famCell j → ∃ x ∈ l, x.1 = j ∧ x.2.1 = c := by
  unfold covers at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj => by simpa using allN_iff.mp h1 j hj, fun j hj c hc he hne => ?_⟩
  have := allN_iff.mp (allN_iff.mp h2 j hj) c hc
  simp only [he, Bool.false_or, Bool.or_eq_true, beq_iff_eq, hne, false_or, List.any_eq_true,
    Bool.and_eq_true] at this
  obtain ⟨x, hx, h1, h2⟩ := this
  exact ⟨x, hx, h1, h2⟩

/-- **Ball data give the ball property of the pattern.** -/
theorem goodB_of_data {md : ℕ → Mode} {pat tn td : ℕ} {l : List Cert}
    (h : BallData md pat tn td l) : GoodB md tn td (patOfCode pat) := by
  intro w N hN hE j c d hcd
  obtain ⟨hcov, hall⟩ := h
  obtain ⟨hfam, hcv⟩ := covers_spec hcov
  have hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y := fun j hj => (hE j hj).nonneg
  set Q := patOfCode pat with hQ
  set A := N 0 * N 1 * N 2 * tn / td with hA
  have hA0 : 0 ≤ A := by
    have := hN 0 (by norm_num)
    have := hN 1 (by norm_num)
    have := hN 2 (by norm_num)
    positivity
  set F : Fin 6 → ℝ := fun k => faceP Q w (offPair k).1 (offPair k).2 with hF
  have hF0 : ∀ k, 0 ≤ F k := fun k => faceP_nonneg hw _ _
  -- one test with a record
  have test : ∀ (j' : Fin 6) (c' d' : Fin 3), eqc pat 3 (3 * c'.val + d'.val) = false →
      3 * c'.val + d'.val ≠ famCell j'.val →
      A ^ 600 ≤ (∏ k, F k ^ bw j'.val k.val) * faceP Q w c' d' ^ 9 := by
    intro j' c' d' he hne
    obtain ⟨x, hx, hx1, hx2⟩ := hcv j'.val j'.isLt _ (by omega) he hne
    have hc := allCert_mem hall x hx
    unfold certB at hc
    rw [hx1, hx2] at hc
    have key := checkR_sound hc hN fun j hj => by rw [edgeE_patE hj]; exact hE j hj
    rw [rTot_bRows j'.isLt, rows_prod] at key
    exact key
  show A ^ 600 ≤ (∏ k ∈ univ.erase j, faceP Q w (gp id k).1 (gp id k).2) ^ 100
    * faceP Q w (gp id j).1 (gp id j).2 ^ 91 * faceP Q w c d ^ 9
  simp only [gp, id]
  rw [ballAt_eq F j]
  have hcd' : eqc pat 3 (3 * c.val + d.val) = false := by rw [← eqc_root]; exact hcd
  by_cases hcc : 3 * c.val + d.val = famCell j.val
  · -- the hexagon test: the geometric mean of two tests
    have e := cell_fam j c d hcc
    have hcF : faceP Q w c d = F j := by
      simp only [hF]; rw [← e]
    rw [hcF, ball_mid]
    set j' : Fin 6 := j + 1 with hj'
    have hjj : j' ≠ j := fin6_succ_ne j
    have hf : ∀ k : Fin 6, eqc pat 3 (3 * (offPair k).1.val + (offPair k).2.val) = false :=
      fun k => by rw [← famCell_spec]; exact hfam k.val k.isLt
    have hne : ∀ k k' : Fin 6, k ≠ k' →
        3 * (offPair k).1.val + (offPair k).2.val ≠ famCell k'.val := fun k k' hk e => by
      rw [← famCell_spec] at e; exact hk (famCell_inj k k' e)
    have t1 := test j (offPair j').1 (offPair j').2 (hf j') (hne j' j hjj)
    have t2 := test j' (offPair j).1 (offPair j).2 (hf j) (hne j j' hjj.symm)
    have hP0 : 0 ≤ (∏ k, F k) ^ 100 := pow_nonneg (Finset.prod_nonneg fun k _ => hF0 k) _
    have hprod : (A ^ 600) ^ 2 ≤ ((∏ k, F k) ^ 100) ^ 2 := by
      have := mul_le_mul t1 t2 (pow_nonneg hA0 _) ((pow_nonneg hA0 _).trans t1)
      calc (A ^ 600) ^ 2 = A ^ 600 * A ^ 600 := by ring
        _ ≤ _ := this
        _ = ((∏ k, F k ^ bw j.val k.val) * F j ^ 9) * ((∏ k, F k ^ bw j'.val k.val) * F j' ^ 9) := by
          simp only [hF]; ring
        _ = _ := by rw [ball_mid, ball_mid]; ring
    exact (pow_le_pow_iff_left₀ (pow_nonneg hA0 _) hP0 (by norm_num)).mp hprod
  · exact test j c d hcd' hcc

/-! ### The classes of the path edges, on lists -/

/-- The class of a path edge with the constants of the mode `md`, on lists. -/
structure LCls (md : Mode) (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop where
  fl : 0 < md.fl.1 → Dominant S T W ((md.fl.1 : ℝ) / md.fl.2 * N)
  bij : 0 < md.bij.1 → BijGe S T W N ((md.bij.1 : ℝ) / md.bij.2)
  hx : 0 < md.hx.1 → ∀ p q : Fin 6 → ℕ, Matched S T p q → (∀ i, p i ≠ q i) →
    (md.hx.1 : ℝ) / md.hx.2 * N ^ 6 ≤ ∏ i, W (p i) (q i)
  ball : 0 < md.ball.1 → InBall S T W ((md.ball.1 : ℝ) / md.ball.2 * N)

theorem LCls.swap {md : Mode} {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N : ℝ} (h : LCls md S T W N) :
    LCls md T S (fun d c => W c d) N :=
  ⟨fun h1 => (h.fl h1).swap, fun h1 => (h.bij h1).swap,
    fun h1 p q hm hpq => h.hx h1 q p hm.symm fun i => (hpq i).symm, fun h1 => (h.ball h1).swap⟩

/-- The class of a path edge read through enumerations of its two lists. -/
theorem edgeOK_of_lcls {md : Mode} {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N : ℝ}
    (hW : ∀ c d, 0 ≤ W c d) (h : LCls md S T W N) {ζ ξ : Fin 3 → ℕ}
    (hζ : Function.Injective ζ) (hξ : Function.Injective ξ) (hζm : ∀ a, ζ a ∈ S)
    (hξm : ∀ b, ξ b ∈ T) :
    EdgeOK md (fun x y => decide (ζ x = ξ y)) (fun x y => W (ζ x) (ξ y)) N := by
  refine ⟨fun x y => hW _ _, fun h1 x y hxy => ?_, fun h1 σ hσ hp => ?_,
    fun h1 σ ⟨hσ, hc⟩ => ?_, fun h1 => (h.ball h1).idx hζ hξ hζm hξm⟩
  · exact h.fl h1 _ (hζm x) _ (hξm y) (by simpa using hxy)
  · have := h.bij h1 ζ (ξ ∘ σ) hζ (hξ.comp hσ.1) hζm (fun b => hξm _)
      (fun a e => by have := hp a; simp [e] at this)
    simpa using this
  · have hm : Matched S T (fun k => ζ (offPair k).1) (fun k => ξ (σ (offPair k).2)) :=
      ⟨ζ, ξ ∘ σ, hζ, hξ.comp hσ, hζm, fun b => hξm _, fun a b hab => by
        obtain ⟨i, hi⟩ := offPair_surj a b hab
        exact ⟨i, by show ζ (offPair i).1 = ζ a; rw [hi],
          by show ξ (σ (offPair i).2) = ξ (σ b); rw [hi]⟩⟩
    have hne : ∀ i, ζ (offPair i).1 ≠ ξ (σ (offPair i).2) := fun i e =>
      offPair_ne i (hσ (hc _ _ (decide_eq_true e)))
    exact h.hx h1 _ _ hm hne

theorem edgeOK_wOf' {a b c : Mode} {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ}
    {W : Fin 3 → ℕ → ℕ → ℝ} (hW : ∀ j c d, 0 ≤ W j c d) {N : Fin 3 → ℝ}
    (h0 : LCls a Lu (Li 0) (W 0) (N 0)) (h1 : LCls b (Li 0) (Li 1) (W 1) (N 1))
    (h2 : LCls c (Li 1) Lv (W 2) (N 2)) {α γ₀ γ₁ β : Fin 3 → ℕ}
    (hα : Function.Injective α) (hγ₀ : Function.Injective γ₀) (hγ₁ : Function.Injective γ₁)
    (hβ : Function.Injective β) (hαm : ∀ a, α a ∈ Lu) (hγ₀m : ∀ s, γ₀ s ∈ Li 0)
    (hγ₁m : ∀ t, γ₁ t ∈ Li 1) (hβm : ∀ b, β b ∈ Lv) :
    ∀ j < 3, EdgeOK (modes3 a b c j) (patE (patOf α γ₀ γ₁ β) j) (wOf W α γ₀ γ₁ β j)
      (nOf N j) := by
  intro j hj
  interval_cases j
  · exact edgeOK_of_lcls (hW 0) h0 hα hγ₀ hαm hγ₀m
  · exact edgeOK_of_lcls (hW 1) h1 hγ₀ hγ₁ hγ₀m hγ₁m
  · exact edgeOK_of_lcls (hW 2) h2 hγ₁ hβ hγ₁m hβm

/-! ### The list-level theorems -/

/-- **A square with three loaded path edges in the classes `a, b, c` is in the ball class at
its root edge**, given the ball property for the 52 patterns. -/
theorem sq_ball_of_good' {a b c : Mode} {tn td : ℕ}
    (hgood : ∀ q, q < SqData.qs.length →
      GoodB (modes3 a b c) tn td (patOfCode (SqData.qs.getD q 0)))
    {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) {W : Fin 3 → ℕ → ℕ → ℝ} (hW : ∀ j c d, 0 ≤ W j c d)
    {N : Fin 3 → ℝ} (hN : ∀ j, 0 < N j)
    (h0 : LCls a Lu (Li 0) (W 0) (N 0)) (h1 : LCls b (Li 0) (Li 1) (W 1) (N 1))
    (h2 : LCls c (Li 1) Lv (W 2) (N 2)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) W) (N 0 * N 1 * N 2 * tn / td) := by
  refine inBall_of_idx hLu hLv fun α β hα hβ hαm hβm hal => ?_
  obtain ⟨π, hπ, γ₀, γ₁, hγ₀, hγ₁, hγ₀m, hγ₁m, hG⟩ :=
    sq_frame (fun P Q h hq => GoodB.mono h hq) hgood hLv hLi hα hβ hβm hal
  refine ⟨π, hπ, ?_⟩
  have key := hG _ _ (nOf_pos hN) (edgeOK_wOf' hW h0 h1 h2 (hα.comp hπ.1) hγ₀ hγ₁
    (hβ.comp hπ.1) (fun a => hαm _) hγ₀m hγ₁m fun b => hβm _)
  simp only [nOf, ite_true, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    ite_false] at key
  exact key.mono (faceP_nonneg (wOf_nonneg hW _ _ _ _))
    (faceP_le_faceSum hLi hγ₀ hγ₁ hγ₀m hγ₁m hW)

/-- **A square with three loaded path edges in the classes `a, b, c` has the hexagon bound at
its root edge**, given the hexagon property for the 52 patterns. -/
theorem sq_hex_of_good' {a b c : Mode} {tn td : ℕ}
    (hgood : ∀ q, q < SqData.qs.length →
      GoodH (modes3 a b c) tn td (patOfCode (SqData.qs.getD q 0)))
    {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    {W : Fin 3 → ℕ → ℕ → ℝ} (hW : ∀ j c d, 0 ≤ W j c d) {N : Fin 3 → ℝ} (hN : ∀ j, 0 < N j)
    (h0 : LCls a Lu (Li 0) (W 0) (N 0)) (h1 : LCls b (Li 0) (Li 1) (W 1) (N 1))
    (h2 : LCls c (Li 1) Lv (W 2) (N 2)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) W) (N 0 * N 1 * N 2 * tn / td) := by
  refine hex_of_idx_perm fun α β hα hβ hαm hβm hal => ?_
  obtain ⟨π, hπ, γ₀, γ₁, hγ₀, hγ₁, hγ₀m, hγ₁m, hG⟩ :=
    sq_frame (fun P Q h hq => GoodH.mono h hq) hgood hLv hLi hα hβ hβm hal
  refine ⟨π, hπ, ?_⟩
  have key := hG _ _ (nOf_pos hN) (edgeOK_wOf' hW h0 h1 h2 (hα.comp hπ.1) hγ₀ hγ₁
    (hβ.comp hπ.1) (fun a => hαm _) hγ₀m hγ₁m fun b => hβm _)
  simp only [nOf, ite_true, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    ite_false] at key
  refine key.trans (Finset.prod_le_prod₀ (fun k _ => faceP_nonneg (wOf_nonneg hW _ _ _ _) _ _)
    fun k _ => ?_)
  exact faceP_le_faceSum hLi hγ₀ hγ₁ hγ₀m hγ₁m hW _ _

/-- **A square with three loaded path edges in the classes `a, b, c`, closed by its root edge,
has the closing count**, given the closing property for the 52 patterns. -/
theorem sq_close_of_good' {a b c : Mode} {tn td : ℕ}
    (hgood : ∀ q, q < SqData.qs.length →
      GoodC (modes3 a b c) tn td (patOfCode (SqData.qs.getD q 0)))
    {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3)
    {W : Fin 3 → ℕ → ℕ → ℝ} (hW : ∀ j c d, 0 ≤ W j c d) {N : Fin 3 → ℝ} (hN : ∀ j, 0 < N j)
    (h0 : LCls a Lu (Li 0) (W 0) (N 0)) (h1 : LCls b (Li 0) (Li 1) (W 1) (N 1))
    (h2 : LCls c (Li 1) Lv (W 2) (N 2)) :
    N 0 * N 1 * N 2 * tn / td
      ≤ ∑ x ∈ Lu, ∑ y ∈ Lv, if x = y then 0 else faceSum Li (fun _ _ => 1) W x y := by
  obtain ⟨α, hα, hαm⟩ := exists_enum hLu
  obtain ⟨β, hβ, hβm, hβa⟩ := exists_aligned hLv hα
  have hal : ∀ a b, α a = β b → a = b := fun a b e => hβa b a e.symm
  obtain ⟨π, hπ, γ₀, γ₁, hγ₀, hγ₁, hγ₀m, hγ₁m, hG⟩ :=
    sq_frame (fun P Q h hq => GoodC.mono h hq) hgood hLv hLi hα hβ hβm hal
  have key := hG _ _ (nOf_pos hN) (edgeOK_wOf' hW h0 h1 h2 (hα.comp hπ.1) hγ₀ hγ₁
    (hβ.comp hπ.1) (fun a => hαm _) hγ₀m hγ₁m fun b => hβm _)
  simp only [nOf, ite_true, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    ite_false] at key
  refine key.trans ?_
  calc _ ≤ ∑ a, ∑ b, (if α (π a) = β (π b) then 0
        else faceSum Li (fun _ _ => 1) W (α (π a)) (β (π b))) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        simp only [patOf]
        by_cases h : α (π a) = β (π b)
        · simp [h]
        · simp only [h, decide_false, Bool.false_eq_true, ite_false]
          exact faceP_le_faceSum hLi hγ₀ hγ₁ hγ₀m hγ₁m hW _ _
    _ = _ := by
        rw [sum_enum hLu (hα.comp hπ.1) (fun a => hαm _)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sum_enum hLv (hβ.comp hπ.1) (fun b => hβm _)]
        rfl

/-! ### Reflection -/

/-- The interior lists of the reflected square. -/
def revL (Li : Fin 2 → Finset ℕ) : Fin 2 → Finset ℕ := ![Li 1, Li 0]

/-- The tables of the reflected square. -/
def revW (W : Fin 3 → ℕ → ℕ → ℝ) : Fin 3 → ℕ → ℕ → ℝ :=
  ![fun a b => W 2 b a, fun a b => W 1 b a, fun a b => W 0 b a]

theorem faceSum_rev (Li : Fin 2 → Finset ℕ) (W : Fin 3 → ℕ → ℕ → ℝ) (x y : ℕ) :
    faceSum (revL Li) (fun _ _ => 1) (revW W) y x = faceSum Li (fun _ _ => 1) W x y := by
  rw [faceSum_two, faceSum_two, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  simp only [revW, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem revW_nonneg {W : Fin 3 → ℕ → ℕ → ℝ} (hW : ∀ j c d, 0 ≤ W j c d) :
    ∀ j c d, 0 ≤ revW W j c d := by
  intro j c d
  fin_cases j <;> simp [revW, hW]

theorem revL_card {Li : Fin 2 → Finset ℕ} (hLi : ∀ j, (Li j).card = 3) :
    ∀ j, (revL Li j).card = 3 := by
  intro j
  fin_cases j <;> simp [revL, hLi]

/-- The scales of the reflected square. -/
def revN (N : Fin 3 → ℝ) : Fin 3 → ℝ := ![N 2, N 1, N 0]

theorem revN_pos {N : Fin 3 → ℝ} (hN : ∀ j, 0 < N j) : ∀ j, 0 < revN N j := by
  intro j
  fin_cases j <;> simp [revN, hN]

theorem revN_prod (N : Fin 3 → ℝ) : revN N 0 * revN N 1 * revN N 2 = N 0 * N 1 * N 2 := by
  simp only [revN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem inBall_rev {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} {W : Fin 3 → ℕ → ℕ → ℝ} {A : ℝ}
    (h : InBall Lv Lu (faceSum (revL Li) (fun _ _ => 1) (revW W)) A) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) W) A := by
  have := h.swap
  simp only [faceSum_rev] at this
  exact this

theorem hex_rev {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} {W : Fin 3 → ℕ → ℕ → ℝ} {A : ℝ}
    (h : Hex Lv Lu (faceSum (revL Li) (fun _ _ => 1) (revW W)) A) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) W) A := by
  have := h.swap'
  simp only [faceSum_rev] at this
  exact this

theorem close_rev {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} {W : Fin 3 → ℕ → ℕ → ℝ} {A : ℝ}
    (h : A ≤ ∑ x ∈ Lv, ∑ y ∈ Lu,
      if x = y then 0 else faceSum (revL Li) (fun _ _ => 1) (revW W) x y) :
    A ≤ ∑ x ∈ Lu, ∑ y ∈ Lv, if x = y then 0 else faceSum Li (fun _ _ => 1) W x y := by
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [faceSum_rev]
  by_cases e : x = y
  · simp [e]
  · simp [e, Ne.symm e]

/-! ### The classes of the fifteen-face square lemmas -/

section Classes

variable {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N : ℝ}

/-- `Z` (one active mark): floor `2/3`, bijections `32/27`, in `A · B`. -/
def ClsZ (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  Dominant S T W (2 / 3 * N) ∧ BijGe S T W N (32 / 27) ∧ InBall S T W (17 / 16 * N)

/-- `W` (two active marks): floor `4/9`, bijections `17/16`, in `A · B`. -/
def ClsW (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  Dominant S T W (4 / 9 * N) ∧ BijGe S T W N (17 / 16) ∧ InBall S T W (17 / 16 * N)

/-- `AB_f` (three active marks): floor `8/27`, in `A · B`. -/
def ClsABf (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  Dominant S T W (8 / 27 * N) ∧ InBall S T W (17 / 16 * N)

/-- `BAH_f` (four active marks): floor `16/81`, in `B` and in `A · H`. -/
def ClsBAHf (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  Dominant S T W (16 / 81 * N) ∧ InBall S T W N ∧ Hex S T W (17 / 16 * N)

/-- `B_f5` (five marks): floor `32/243`, in `B`. -/
def ClsBf5 (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  Dominant S T W (32 / 243 * N) ∧ InBall S T W N

/-- `B_f6` (six marks): floor `64/729`, in `B`. -/
def ClsBf6 (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  Dominant S T W (64 / 729 * N) ∧ InBall S T W N

/-- `H7_f` (seven marks): floor `128/2187`, in `D₆ · H`. -/
def ClsH7f (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  Dominant S T W (128 / 2187 * N) ∧ Hex S T W (d6 * N)

theorem ClsZ.swap (h : ClsZ S T W N) : ClsZ T S (fun d c => W c d) N :=
  ⟨h.1.swap, h.2.1.swap, h.2.2.swap⟩

theorem ClsW.swap (h : ClsW S T W N) : ClsW T S (fun d c => W c d) N :=
  ⟨h.1.swap, h.2.1.swap, h.2.2.swap⟩

theorem ClsABf.swap (h : ClsABf S T W N) : ClsABf T S (fun d c => W c d) N :=
  ⟨h.1.swap, h.2.swap⟩

theorem ClsBAHf.swap (h : ClsBAHf S T W N) : ClsBAHf T S (fun d c => W c d) N :=
  ⟨h.1.swap, h.2.1.swap, h.2.2.swap'⟩

theorem ClsBf5.swap (h : ClsBf5 S T W N) : ClsBf5 T S (fun d c => W c d) N :=
  ⟨h.1.swap, h.2.swap⟩

theorem ClsBf6.swap (h : ClsBf6 S T W N) : ClsBf6 T S (fun d c => W c d) N :=
  ⟨h.1.swap, h.2.swap⟩

theorem ClsH7f.swap (h : ClsH7f S T W N) : ClsH7f T S (fun d c => W c d) N :=
  ⟨h.1.swap, h.2.swap'⟩

theorem hex_lcls {h : ℝ} {n d : ℕ} (hh : (n : ℝ) / d ≤ h ^ 6)
    (hx : Hex S T W (h * N)) :
    ∀ p q : Fin 6 → ℕ, Matched S T p q → (∀ i, p i ≠ q i) →
      (n : ℝ) / d * N ^ 6 ≤ ∏ i, W (p i) (q i) := fun p q hm hpq =>
  le_trans (by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hh (by positivity))
    (hx p q hm hpq)

theorem m1_lcls (h : Dominant S T W N) : LCls m1 S T W N :=
  ⟨fun _ => by simpa [m1] using h, fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem mB_lcls (h : InBall S T W N) : LCls mB S T W N :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun _ => by simpa [mB] using h⟩

theorem ClsZ.lcls (h : ClsZ S T W N) : LCls mZ S T W N :=
  ⟨fun _ => by convert h.1 using 2; simp [mZ], fun _ => by convert h.2.1 using 1; simp [mZ],
    fun h => absurd h (by decide), fun _ => by convert h.2.2 using 2; simp [mZ]⟩

theorem ClsW.lcls (h : ClsW S T W N) : LCls mW S T W N :=
  ⟨fun _ => by convert h.1 using 2; simp [mW], fun _ => by convert h.2.1 using 1; simp [mW],
    fun h => absurd h (by decide), fun _ => by convert h.2.2 using 2; simp [mW]⟩

theorem ClsABf.lcls (h : ClsABf S T W N) : LCls mABf S T W N :=
  ⟨fun _ => by convert h.1 using 2; simp [mABf], fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun _ => by convert h.2 using 2; simp [mABf]⟩

theorem ClsBAHf.lcls (h : ClsBAHf S T W N) : LCls mBAHf S T W N :=
  ⟨fun _ => by convert h.1 using 2; simp [mBAHf], fun h => absurd h (by decide),
    fun _ => hex_lcls (by norm_num [mBAHf]) h.2.2,
    fun _ => by simpa [mBAHf] using h.2.1⟩

theorem ClsBf5.lcls (h : ClsBf5 S T W N) : LCls mBf5 S T W N :=
  ⟨fun _ => by convert h.1 using 2; simp [mBf5], fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun _ => by simpa [mBf5] using h.2⟩

theorem ClsBf6.lcls (h : ClsBf6 S T W N) : LCls mBf6 S T W N :=
  ⟨fun _ => by convert h.1 using 2; simp [mBf6], fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun _ => by simpa [mBf6] using h.2⟩

theorem d6_six : ((17 ^ 8 * 56 ^ 6 : ℕ) : ℝ) / ((16 ^ 8 * 59 ^ 6 : ℕ) : ℝ) = d6 ^ 6 := by
  rw [show d6 ^ 6 = (d6 ^ 3) ^ 2 by ring, d6_cube]
  norm_num

theorem ClsH7f.lcls (h : ClsH7f S T W N) : LCls mH7f S T W N :=
  ⟨fun _ => by convert h.1 using 2; simp [mH7f], fun h => absurd h (by decide),
    fun _ => hex_lcls (le_of_eq d6_six) h.2, fun h => absurd h (by decide)⟩

end Classes

end Outerplanar.SqMulti
