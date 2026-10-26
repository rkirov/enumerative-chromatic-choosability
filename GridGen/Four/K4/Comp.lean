/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.CompData

/-!
# Height four at `k = 4`: the compensation lemma

Codex's (OpenAI) endpoint compensation (`ai_research_notes/cx/h4k4/NOTE.md`, step 3), in the
reduced form of `ai_research_notes/H4_K4_REVIEW_2026-10-26.md` Part 1(d). Let `(Y, B)` be bad, `r`
its endpoint row (the last for `BadF`, the first for `BadR` and `BadM`), `p ∉ Yᵣ` and `q ≠ p`.
Then the seam vectors of `Y` and of `Y` with `Yᵣ` replaced by `(Yᵣ + p) − q` have a sum that is
nonnegative on `K` (`compF`, `compR`, `compM`).

The colours of a bad pattern are five named ones and `p`; the map `fm` sends `0, …, 4` to the
named colours and everything else to `p`, injectively on the colours used, so the renaming
invariance (`dvec_image`) reduces each case to the concrete certificate of `CompData`.
-/

namespace GridGen.Four.K4

open Finset

/-- The colour map `0, 1, 2, 3, 4 ↦ x, y, z, a, b`, everything else `↦ p`. -/
def fm (x y z a b p : ℕ) (n : ℕ) : ℕ :=
  if n = 0 then x else if n = 1 then y else if n = 2 then z else if n = 3 then a
  else if n = 4 then b else p

/-- `p` is a sixth colour. -/
def Fresh (x y z a b p : ℕ) : Prop := p ≠ x ∧ p ≠ y ∧ p ≠ z ∧ p ≠ a ∧ p ≠ b

theorem fm_inj5 {x y z a b : ℕ} (hd : Dist5 x y z a b) (p : ℕ) :
    Set.InjOn (fm x y z a b p) ↑(range 5) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hd
  intro m hm n hn h
  simp only [coe_range, Set.mem_Iio] at hm hn
  interval_cases m <;> interval_cases n <;> first | rfl | (simp [fm] at h; omega)

theorem fm_inj6 {x y z a b p : ℕ} (hd : Dist5 x y z a b) (hp : Fresh x y z a b p) :
    Set.InjOn (fm x y z a b p) ↑(range 6) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hd
  obtain ⟨e1, e2, e3, e4, e5⟩ := hp
  intro m hm n hn h
  simp only [coe_range, Set.mem_Iio] at hm hn
  interval_cases m <;> interval_cases n <;> first | rfl | (simp [fm] at h; omega)

/-- Injectivity of `fm` on the colours of a case: `range 5`, or `range 6` when `p` is fresh
(`j = 2`). -/
theorem fm_inj {x y z a b p j : ℕ} (hd : Dist5 x y z a b) (hfr : j = 2 → Fresh x y z a b p)
    {S : Finset ℕ} (h5 : j ≠ 2 → S ⊆ range 5) (h6 : S ⊆ range 6) :
    Set.InjOn (fm x y z a b p) ↑S := by
  by_cases hj : j = 2
  · exact (fm_inj6 hd (hfr hj)).mono (coe_subset.mpr h6)
  · exact (fm_inj5 hd p).mono (coe_subset.mpr (h5 hj))

/-! ### The colours of the concrete cases -/

theorem subF5 : ∀ i, i < 4 → uni (YF i) ∪ uni BF ⊆ range 5 := by decide

theorem subF6 : ∀ i, i < 4 → ∀ j, j < 3 → ∀ k, k < 4 →
    uni (setL4 (YF i) (LF j k)) ∪ uni BF ⊆ range 6 := by decide

theorem subF5' : ∀ i, i < 4 → ∀ j, j < 3 → ∀ k, k < 4 → j ≠ 2 →
    uni (setL4 (YF i) (LF j k)) ∪ uni BF ⊆ range 5 := by decide

theorem subLF6 : ∀ j, j < 3 → ∀ k, k < 3 →
    insert (qcF k) (insert (pcF j) ({0, 1, 4} : Finset ℕ)) ⊆ range 6 := by decide

theorem subLF5 : ∀ j, j < 3 → ∀ k, k < 3 → j ≠ 2 →
    insert (qcF k) (insert (pcF j) ({0, 1, 4} : Finset ℕ)) ⊆ range 5 := by decide

theorem LF_three : ∀ j, j < 3 → LF j 3 = insert (pcF j) ({0, 1, 4} : Finset ℕ) := by decide

theorem subM5 : uni YM ∪ uni BM ⊆ range 5 := by decide

theorem subM6 : ∀ j, j < 3 → ∀ k, k < 4 → uni (setL1 YM (LM j k)) ∪ uni BM ⊆ range 6 := by
  decide

theorem subM5' : ∀ j, j < 3 → ∀ k, k < 4 → j ≠ 2 →
    uni (setL1 YM (LM j k)) ∪ uni BM ⊆ range 5 := by decide

theorem subLM6 : ∀ j, j < 3 → ∀ k, k < 3 →
    insert (qcM k) (insert (pcM j) ({0, 1, 2} : Finset ℕ)) ⊆ range 6 := by decide

theorem subLM5 : ∀ j, j < 3 → ∀ k, k < 3 → j ≠ 2 →
    insert (qcM k) (insert (pcM j) ({0, 1, 2} : Finset ℕ)) ⊆ range 5 := by decide

theorem LM_three : ∀ j, j < 3 → LM j 3 = insert (pcM j) ({0, 1, 2} : Finset ℕ) := by decide

/-! ### Transfer to the concrete certificate -/

theorem transfer {f : ℕ → ℕ} {Yc Yc' Bc : Col} (h1 : Set.InjOn f ↑(uni Yc ∪ uni Bc))
    (h2 : Set.InjOn f ↑(uni Yc' ∪ uni Bc)) (hc : RaysOK (dvec Yc Bc + dvec Yc' Bc)) :
    RaysOK (dvec (imgC f Yc) (imgC f Bc) + dvec (imgC f Yc') (imgC f Bc)) := by
  rw [dvec_image h1, dvec_image h2]
  exact hc

/-- One case of the forward edge families. -/
theorem leafF {x y z a b p q : ℕ} {Y0 : Finset ℕ} (hd : Dist5 x y z a b) (i j k : ℕ)
    (hi : i < 4) (hj : j < 3) (hk : k < 4) (hfr : j = 2 → Fresh x y z a b p)
    (hY0 : Y0 = (YF0 i).image (fm x y z a b p))
    (hL : (insert p ({x, y, b} : Finset ℕ)).erase q = (LF j k).image (fm x y z a b p)) :
    RaysOK (dvec (Y0, {x, y, z}, {x, y, a}, {x, y, b}) (edgeB x y z a b)
      + dvec (setL4 (Y0, {x, y, z}, {x, y, a}, {x, y, b})
          ((insert p ({x, y, b} : Finset ℕ)).erase q))
          (edgeB x y z a b)) := by
  have eY : ((Y0, {x, y, z}, {x, y, a}, {x, y, b}) : Col) = imgC (fm x y z a b p) (YF i) := by
    rw [hY0]; simp [imgC, YF, fm]
  have eB : edgeB x y z a b = imgC (fm x y z a b p) BF := by
    simp [imgC, BF, edgeB, fm]
  have e' : setL4 (imgC (fm x y z a b p) (YF i)) ((LF j k).image (fm x y z a b p))
      = imgC (fm x y z a b p) (setL4 (YF i) (LF j k)) := rfl
  rw [hL, eY, eB, e']
  exact transfer (fm_inj hd hfr (fun _ => subF5 i hi) ((subF5 i hi).trans (fun c hc => by
    simp only [Finset.mem_range] at hc ⊢; omega)))
    (fm_inj hd hfr (subF5' i hi j hj k hk) (subF6 i hi j hj k hk))
    (certF i j k hi hj hk)

/-- **Compensation, forward edge families E1, E2, E3.** -/
theorem compF {Y B : Col} (h : BadF Y B) {p q : ℕ} (hp : p ∉ Y.2.2.2) (hq : q ≠ p) :
    RaysOK (dvec Y B + dvec (setL4 Y ((insert p Y.2.2.2).erase q)) B) := by
  obtain ⟨x, y, z, a, b, hd, rfl, h1, h2, h3, h0⟩ := h
  obtain ⟨Y0, Y1, Y2, Y3⟩ := Y
  simp only at h1 h2 h3 h0 hp ⊢
  subst h1 h2 h3
  have hd' := hd
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hd'
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  obtain ⟨j, hj, hpj, hfr⟩ : ∃ j, j < 3 ∧ fm x y z a b p (pcF j) = p ∧
      (j = 2 → Fresh x y z a b p) := by
    by_cases hpz : p = z
    · exact ⟨0, by norm_num, by simp [fm, pcF, hpz], fun h => absurd h (by norm_num)⟩
    by_cases hpa : p = a
    · exact ⟨1, by norm_num, by simp [fm, pcF, hpa], fun h => absurd h (by norm_num)⟩
    · exact ⟨2, by norm_num, by simp [fm, pcF], fun _ => ⟨hp.1, hp.2.1, hpz, hpa, hp.2.2⟩⟩
  have himg : ∀ k, k < 3 → (LF j k).image (fm x y z a b p)
      = (insert p ({x, y, b} : Finset ℕ)).erase (fm x y z a b p (qcF k)) := by
    intro k hk
    unfold LF
    rw [image_erase_injOn (fm_inj hd hfr (subLF5 j hj k hk) (subLF6 j hj k hk)),
      Finset.image_insert, hpj]
    simp [fm]
  obtain ⟨k, hk, hL⟩ : ∃ k, k < 4 ∧
      (insert p ({x, y, b} : Finset ℕ)).erase q = (LF j k).image (fm x y z a b p) := by
    by_cases hqx : q = x
    · exact ⟨0, by norm_num, by rw [himg 0 (by norm_num)]; try simp [fm, qcF, hqx]⟩
    by_cases hqy : q = y
    · exact ⟨1, by norm_num, by rw [himg 1 (by norm_num)]; try simp [fm, qcF, hqy]⟩
    by_cases hqb : q = b
    · exact ⟨2, by norm_num, by rw [himg 2 (by norm_num)]; try simp [fm, qcF, hqb]⟩
    · refine ⟨3, by norm_num, ?_⟩
      rw [LF_three j hj, Finset.image_insert, hpj, Finset.erase_eq_of_notMem]
      · simp [fm]
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  obtain ⟨i, hi, hY0⟩ : ∃ i, i < 4 ∧ Y0 = (YF0 i).image (fm x y z a b p) := by
    rcases h0 with rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, by simp [YF0, fm]⟩
    · exact ⟨1, by norm_num, by simp [YF0, fm]⟩
    · exact ⟨2, by norm_num, by simp [YF0, fm]⟩
    · exact ⟨3, by norm_num, by simp [YF0, fm]⟩
  exact leafF hd i j k hi hj hk hfr hY0 hL

/-- **Compensation, reversed edge families.** -/
theorem compR {Y B : Col} (h : BadR Y B) {p q : ℕ} (hp : p ∉ Y.1) (hq : q ≠ p) :
    RaysOK (dvec Y B + dvec (setL1 Y ((insert p Y.1).erase q)) B) := by
  have := compF h (p := p) (q := q) hp hq
  have e : setL4 (revC Y) ((insert p (revC Y).2.2.2).erase q)
      = revC (setL1 Y ((insert p Y.1).erase q)) := rfl
  rw [e, dvec_rev, dvec_rev] at this
  exact this

/-- One case of the central family. -/
theorem leafM {x y z a b p q : ℕ} (hd : Dist5 x y z a b) (j k : ℕ) (hj : j < 3) (hk : k < 4)
    (hfr : j = 2 → Fresh x y z a b p)
    (hL : (insert p ({x, y, z} : Finset ℕ)).erase q = (LM j k).image (fm x y z a b p)) :
    RaysOK (dvec ({x, y, z}, {x, y, a}, {x, y, b}, {x, y, z}) (centB x y z a b)
      + dvec (setL1 ({x, y, z}, {x, y, a}, {x, y, b}, {x, y, z})
          ((insert p ({x, y, z} : Finset ℕ)).erase q))
          (centB x y z a b)) := by
  have eY : (({x, y, z}, {x, y, a}, {x, y, b}, {x, y, z}) : Col) = imgC (fm x y z a b p) YM := by
    simp [imgC, YM, fm]
  have eB : centB x y z a b = imgC (fm x y z a b p) BM := by
    simp [imgC, BM, centB, fm]
  have e' : setL1 (imgC (fm x y z a b p) YM) ((LM j k).image (fm x y z a b p))
      = imgC (fm x y z a b p) (setL1 YM (LM j k)) := rfl
  rw [hL, eY, eB, e']
  exact transfer (fm_inj hd hfr (fun _ => subM5) (subM5.trans (fun c hc => by
    simp only [Finset.mem_range] at hc ⊢; omega)))
    (fm_inj hd hfr (subM5' j hj k hk) (subM6 j hj k hk))
    (certM j k hj hk)

/-- **Compensation, the central family M.** -/
theorem compM {Y B : Col} (h : BadM Y B) {p q : ℕ} (hp : p ∉ Y.1) (hq : q ≠ p) :
    RaysOK (dvec Y B + dvec (setL1 Y ((insert p Y.1).erase q)) B) := by
  obtain ⟨x, y, z, a, b, hd, rfl, rfl⟩ := h
  simp only at hp ⊢
  have hd' := hd
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hd'
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  obtain ⟨j, hj, hpj, hfr⟩ : ∃ j, j < 3 ∧ fm x y z a b p (pcM j) = p ∧
      (j = 2 → Fresh x y z a b p) := by
    by_cases hpa : p = a
    · exact ⟨0, by norm_num, by simp [fm, pcM, hpa], fun h => absurd h (by norm_num)⟩
    by_cases hpb : p = b
    · exact ⟨1, by norm_num, by simp [fm, pcM, hpb], fun h => absurd h (by norm_num)⟩
    · exact ⟨2, by norm_num, by simp [fm, pcM], fun _ => ⟨hp.1, hp.2.1, hp.2.2, hpa, hpb⟩⟩
  have himg : ∀ k, k < 3 → (LM j k).image (fm x y z a b p)
      = (insert p ({x, y, z} : Finset ℕ)).erase (fm x y z a b p (qcM k)) := by
    intro k hk
    unfold LM
    rw [image_erase_injOn (fm_inj hd hfr (subLM5 j hj k hk) (subLM6 j hj k hk)),
      Finset.image_insert, hpj]
    simp [fm]
  obtain ⟨k, hk, hL⟩ : ∃ k, k < 4 ∧
      (insert p ({x, y, z} : Finset ℕ)).erase q = (LM j k).image (fm x y z a b p) := by
    by_cases hqx : q = x
    · exact ⟨0, by norm_num, by rw [himg 0 (by norm_num)]; try simp [fm, qcM, hqx]⟩
    by_cases hqy : q = y
    · exact ⟨1, by norm_num, by rw [himg 1 (by norm_num)]; try simp [fm, qcM, hqy]⟩
    by_cases hqz : q = z
    · exact ⟨2, by norm_num, by rw [himg 2 (by norm_num)]; try simp [fm, qcM, hqz]⟩
    · refine ⟨3, by norm_num, ?_⟩
      rw [LM_three j hj, Finset.image_insert, hpj, Finset.erase_eq_of_notMem]
      · simp [fm]
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  exact leafM hd j k hj hk hfr hL

end GridGen.Four.K4
