/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Seam5
import GridGen.Five.Quads

/-!
# Height five, `k = 6`: the averaged certificate on its quads, and the quad `(0,0,0,0)`

* **The table** (`F5_nonneg`). `F5 ≥ 0` at every mismatch quad in `[0,6]⁴` other than
  `(0,0,0,0)`, the exact quads `exactQuads5` and the bit quads `bitQuads5`: with the rational
  bounds of `GridGen/Five/LogB5.lean` this is one integer check per quad (`f5OK`, by `decide`).
  The smallest value is about `6.8·10⁻⁴`, at `(2,0,0,2)`; next come `(1,0,0,3)`, `(3,0,0,1)`
  (`2.3·10⁻³`) and `(0,2,2,1)` and its relatives (`3.1·10⁻³`). (The review of 2026-10-23 moved
  `(2,0,0,2)`, `(1,0,0,3)` and `(3,0,0,1)` to the bit-LP because of rounding concerns; with these
  rigorous bounds they pass `F5` directly.)
* **The quad `(0,0,0,0)`** (`seam_zero5`): all `Bᵢ` equal one `6`-list `B`. A pattern-preserving
  relabelling `s'` of the previous column with its colours in `B`, fixing those already there,
  has `Bᵢ ∖ {sᵢ} ⊇ B ∖ {s'ᵢ}`, so `GB(s) ≥ G(B ∖ s') = GU(s')= GU(s)` state by state.
* `seam_F5_quads`: the seam inequality on the quads of the table.
-/

namespace GridGen.Five

open Finset Real

/-! ### The table -/

/-- The rational bound of `K̄`, times `10⁹`. -/
def KBz : ℤ := -71987317

theorem Kbar_ge : (KBz : ℝ) / 10 ^ 9 ≤ Kbar := by
  unfold Kbar K0 KBz qe5 qm5; norm_num

theorem hrow_comm (qa qb μ : ℝ) : hrow qa qb μ = hrow qb qa μ := by
  unfold hrow; ring

/-- The check of one quad. -/
def f5At (a b c d : ℕ) : Bool :=
  decide ((a, b, c, d) ∈ exactQuads5) || decide ((a, b, c, d) ∈ bitQuads5) ||
    decide (a + b + c + d = 0) ||
    decide (0 ≤ HEL.getD a 0 + HML.getD b 0 + HML.getD c 0 + HEL.getD d 0 + KBz)

/-- The check of all quads in `[0,6]⁴`. -/
def f5OK : Bool :=
  allUpTo (fun a => allUpTo (fun b => allUpTo (fun c => allUpTo (fun d => f5At a b c d) 6) 6) 6) 6

theorem f5OK_true : f5OK = true := by decide +kernel

/-- **The averaged certificate holds on the table quads.** -/
theorem F5_nonneg {m2 m3 m4 m5 : ℕ} (h2 : m2 ≤ 6) (h3 : m3 ≤ 6) (h4 : m4 ≤ 6) (h5 : m5 ≤ 6)
    (hq : (m2, m3, m4, m5) ∉ exactQuads5) (hb : (m2, m3, m4, m5) ∉ bitQuads5)
    (hz : m2 + m3 + m4 + m5 ≠ 0) : 0 ≤ F5 m2 m3 m4 m5 := by
  have h := allUpTo_spec (allUpTo_spec (allUpTo_spec (allUpTo_spec f5OK_true m2 h2) m3 h3)
    m4 h4) m5 h5
  simp only [f5At, Bool.or_eq_true, decide_eq_true_eq] at h
  have hz' : ¬ (m2 + m3 + m4 + m5 = 0) := hz
  have hv : 0 ≤ HEL.getD m2 0 + HML.getD m3 0 + HML.getD m4 0 + HEL.getD m5 0 + KBz := by
    rcases h with ((h | h) | h) | h
    · exact absurd h hq
    · exact absurd h hb
    · exact absurd h hz'
    · exact h
  have hvR : (0 : ℝ) ≤ ((HEL.getD m2 0 + HML.getD m3 0 + HML.getD m4 0 + HEL.getD m5 0 + KBz
      : ℤ) : ℝ) := by exact_mod_cast hv
  push_cast at hvR
  have e2 := HE_le h2
  have e3 := HM_le h3
  have e4 := HM_le h4
  have e5 := HE_le h5
  have kb := Kbar_ge
  unfold F5
  rw [hrow_comm qm5 qe5]
  linarith

/-! ### The quad `(0,0,0,0)` -/

/-- Weighted counts are monotone in the lists. -/
theorem G_mono {w : Wt5} (hw : InBox5 w) {A B C D E A' B' C' D' E' : Finset ℕ} (hA : A ⊆ A')
    (hB : B ⊆ B') (hC : C ⊆ C') (hD : D ⊆ D') (hE : E ⊆ E') :
    G w A B C D E ≤ G w A' B' C' D' E' := by
  unfold G
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => ?_)
  · intro t ht
    rw [mem_sts] at ht ⊢
    obtain ⟨h1, h2, h3, h4, h5, p⟩ := ht
    exact ⟨hA h1, hB h2, hC h3, hD h4, hE h5, p⟩
  · unfold gw
    have h : ((959 / 1000 : ℚ) : ℝ) ≤ (lo5 (orb t) : ℝ) := by exact_mod_cast lo5_ge (orb t)
    have := (hw (orb t)).1
    push_cast at h
    linarith

/-- A pattern-preserving relabelling of a proper column into a `6`-list, fixing the colours
already in the list. -/
theorem exists_relabel {B : Finset ℕ} (hB : B.card = 6) {s : T5} (hs : Proper s) :
    ∃ s' : T5, Proper s' ∧ SamePat s' s ∧ RowsIn s' B ∧
      (r1 s ∈ B → r1 s' = r1 s) ∧ (r2 s ∈ B → r2 s' = r2 s) ∧ (r3 s ∈ B → r3 s' = r3 s) ∧
      (r4 s ∈ B → r4 s' = r4 s) ∧ (r5 s ∈ B → r5 s' = r5 s) := by
  classical
  set O := rowSet s \ B with hO
  set K := rowSet s ∩ B with hK
  have hcard : O.card ≤ (B \ K).card := by
    have h1 : O.card + K.card = (rowSet s).card := by
      rw [hO, hK, Finset.card_sdiff_add_card_inter]
    have h2 : (rowSet s).card ≤ 5 := by
      unfold rowSet
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp
    have h3 : (B \ K).card = 6 - K.card := by
      rw [Finset.card_sdiff_of_subset inter_subset_right, hB]
    omega
  obtain ⟨e⟩ : Nonempty ({x // x ∈ O} ↪ {x // x ∈ B \ K}) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_coe, Fintype.card_coe]; exact hcard)
  let f : ℕ → ℕ := fun x => if hx : x ∈ O then (e ⟨x, hx⟩ : ℕ) else x
  have fO : ∀ x (hx : x ∈ O), f x ∈ B \ K := fun x hx => by
    simp only [f, hx, dite_true]; exact (e ⟨x, hx⟩).2
  have fK : ∀ x, x ∉ O → f x = x := fun x hx => by simp only [f, hx, dite_false]
  have hinj : Set.InjOn f ↑(rowSet s) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    by_cases hxO : x ∈ O <;> by_cases hyO : y ∈ O
    · have h' : (e ⟨x, hxO⟩ : ℕ) = e ⟨y, hyO⟩ := by
        simpa only [f, hxO, hyO, dite_true] using hxy
      have := e.injective (Subtype.ext h')
      exact congrArg Subtype.val this
    · exfalso
      have h1 := fO x hxO
      rw [hxy, fK y hyO] at h1
      have : y ∈ K := by
        rw [hK, Finset.mem_inter]; refine ⟨hy, ?_⟩
        by_contra hyB; exact hyO (by rw [hO, Finset.mem_sdiff]; exact ⟨hy, hyB⟩)
      exact (Finset.mem_sdiff.mp h1).2 this
    · exfalso
      have h1 := fO y hyO
      rw [← hxy, fK x hxO] at h1
      have : x ∈ K := by
        rw [hK, Finset.mem_inter]; refine ⟨hx, ?_⟩
        by_contra hxB; exact hxO (by rw [hO, Finset.mem_sdiff]; exact ⟨hx, hxB⟩)
      exact (Finset.mem_sdiff.mp h1).2 this
    · rwa [fK x hxO, fK y hyO] at hxy
  have hrows : RowsIn s (rowSet s) := by
    unfold RowsIn rowSet; simp
  refine ⟨mapT f s, ?_, samePat_mapT hinj hrows, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p1, p2, p3, p4⟩ := hs
    obtain ⟨m1, m2, m3, m4, m5⟩ := hrows
    exact ⟨fun h => p1 (hinj m1 m2 h), fun h => p2 (hinj m2 m3 h), fun h => p3 (hinj m3 m4 h),
      fun h => p4 (hinj m4 m5 h)⟩
  · have hin : ∀ x ∈ rowSet s, f x ∈ B := by
      intro x hx
      by_cases hxO : x ∈ O
      · exact (Finset.mem_sdiff.mp (fO x hxO)).1
      · rw [fK x hxO]
        by_contra hxB; exact hxO (by rw [hO, Finset.mem_sdiff]; exact ⟨hx, hxB⟩)
    obtain ⟨m1, m2, m3, m4, m5⟩ := hrows
    exact ⟨hin _ m1, hin _ m2, hin _ m3, hin _ m4, hin _ m5⟩
  all_goals
    intro hm
    show f _ = _
    apply fK
    rw [hO, Finset.mem_sdiff]; exact fun h => h.2 hm

/-- **The seam inequality at `(0,0,0,0)`**, state by state. -/
theorem GB_ge_GU_zero {w : Wt5} (hw : InBox5 w) {B : Finset ℕ} (hB : B.card = 6) {s : T5}
    (hs : Proper s) : GU 6 w s ≤ GB w B B B B B s := by
  obtain ⟨s', hs', hsame, hrows, e1, e2, e3, e4, e5⟩ := exists_relabel hB hs
  have hsub : ∀ (c c' : ℕ), (c ∈ B → c' = c) → B.erase c' ⊆ B.erase c := by
    intro c c' h
    by_cases hc : c ∈ B
    · rw [h hc]
    · rw [Finset.erase_eq_of_notMem hc]; exact Finset.erase_subset _ _
  have hmono := G_mono hw (hsub _ _ e1) (hsub _ _ e2) (hsub _ _ e3) (hsub _ _ e4) (hsub _ _ e5)
  rw [G_erase_eq_GU w (by norm_num) hs' hB hrows, GU_congr 6 w (canon_congr hsame)] at hmono
  exact hmono

theorem seam_zero5 {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ B : Finset ℕ} (hB : B.card = 6) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B B B B B s :=
  Finset.sum_le_sum fun _ hs => GB_ge_GU_zero hw hB (proper_of_mem_sts hs)

/-! ### The seam on the table quads -/

theorem mu_eq_of {B C : Finset ℕ} {m : ℕ} (h : (B ∩ C).card + m = 6) :
    Four.mu 6 B C = m := by
  unfold Four.mu
  have : ((B ∩ C).card : ℝ) + m = 6 := by exact_mod_cast h
  push_cast; linarith

/-- **The seam inequality on the quads of the averaged certificate.** -/
theorem seam_F5_quads {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hX₅ : 5 ≤ X₅.card) (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) {m2 m3 m4 m5 : ℕ}
    (hm2 : m2 ≤ 6) (hm3 : m3 ≤ 6) (hm4 : m4 ≤ 6) (hm5 : m5 ≤ 6)
    (hq : (m2, m3, m4, m5) ∉ exactQuads5) (hb : (m2, m3, m4, m5) ∉ bitQuads5)
    (hz : m2 + m3 + m4 + m5 ≠ 0)
    (c2 : (B₁ ∩ B₂).card + m2 = 6) (c3 : (B₂ ∩ B₃).card + m3 = 6)
    (c4 : (B₃ ∩ B₄).card + m4 = 6) (c5 : (B₄ ∩ B₅).card + m5 = 6) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  refine seam_of_F5 hw hX₁ hX₂ hX₃ hX₄ hX₅ hB₁ hB₂ hB₃ hB₄ hB₅ ?_
  rw [mu_eq_of c2, mu_eq_of c3, mu_eq_of c4, mu_eq_of c5]
  exact F5_nonneg hm2 hm3 hm4 hm5 hq hb hz

end GridGen.Five
