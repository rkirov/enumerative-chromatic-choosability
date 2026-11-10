/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Cover

/-!
# Maximal partial covers

Adding a matched pair to a partial cover only removes colourings, so the capacity lemma need
only be proved for covers to which no pair can be added without closing a thread (Step 1 of the
proof draft). Such a *maximal* cover is either full or has a cut section, and removing a cut
section from a maximal cover leaves a maximal cover.
-/

namespace Outerplanar

open Finset

namespace Cover

variable {n : ℕ} [NeZero n] (P : Cover n)

/-- The cover with the extra matched pair `x`–`y` on the edge `e → e + 1`. -/
def add (P : Cover n) (e : Fin n) (x y : ℕ) : Cover n where
  F := P.F
  M i x' y' := P.M i x' y' ∨ (i = e ∧ x' = x ∧ y' = y)

/-- `x` over `e` and `y` over `e + 1` are both unmatched on the edge `e → e + 1`. -/
def Unmatched (e : Fin n) (x y : ℕ) : Prop :=
  x ∈ P.F e ∧ y ∈ P.F (e + 1) ∧ (∀ y' ∈ P.F (e + 1), ¬ P.M e x y') ∧ ∀ x' ∈ P.F e, ¬ P.M e x' y

/-- No pair can be added without closing a thread. -/
def Maximal : Prop := ∀ e x y, P.Unmatched e x y → ¬ (P.add e x y).NoClosedThread

variable {P}

theorem add_isMatching (hM : P.IsMatching) {e : Fin n} {x y : ℕ} (h : P.Unmatched e x y) :
    (P.add e x y).IsMatching := by
  intro i
  refine ⟨fun a ha c hc c' hc' h1 h2 => ?_, fun a ha a' ha' c hc h1 h2 => ?_⟩
  · rcases h1 with h1 | ⟨rfl, rfl, rfl⟩ <;> rcases h2 with h2 | ⟨hie, hax, rfl⟩
    · exact (hM i).1 a ha c hc c' hc' h1 h2
    · subst hie; subst hax
      exact absurd h1 (h.2.2.1 c hc)
    · exact absurd h2 (h.2.2.1 c' hc')
    · rfl
  · rcases h1 with h1 | ⟨rfl, rfl, rfl⟩ <;> rcases h2 with h2 | ⟨hie, rfl, hcy⟩
    · exact (hM i).2 a ha a' ha' c hc h1 h2
    · subst hie; subst hcy
      exact absurd h1 (h.2.2.2 a ha)
    · exact absurd h2 (h.2.2.2 a' ha')
    · rfl

theorem cols_add_subset (e : Fin n) (x y : ℕ) (A : Finset (Fin n)) (b : Fin n → ℕ) :
    (P.add e x y).cols A b ⊆ P.cols A b := by
  intro f hf
  rw [mem_cols] at hf ⊢
  exact ⟨hf.1, fun i hi hi1 hMi => hf.2 i hi hi1 (Or.inl hMi)⟩

theorem CapGE.of_add {e : Fin n} {x y : ℕ} {b : Fin n → ℕ} {C : ℝ}
    (h : (P.add e x y).CapGE univ b C) : P.CapGE univ b C := by
  intro w hw
  refine (h w hw).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (cols_add_subset e x y univ b) fun f hf _ =>
    Finset.prod_nonneg fun i hi => ((hw i hi).1 _ (((P.mem_cols.mp hf).1 i).1 hi)).le

/-- A property of the vertices of the cycle that holds somewhere and is preserved by the
successor holds everywhere. -/
theorem forall_of_succ {Q : Fin n → Prop} {i0 : Fin n} (h0 : Q i0)
    (hs : ∀ j, Q j → Q (j + 1)) : ∀ j, Q j := by
  classical
  by_contra hne
  have hA : (univ.filter Q) ≠ univ := fun h => hne fun j => by
    have := Finset.mem_univ j
    rw [← h] at this
    exact (Finset.mem_filter.mp this).2
  obtain ⟨i, hi, hi1⟩ := exists_last ⟨i0, by simpa using h0⟩ hA
  exact hi1 (by simpa using hs i (by simpa using hi))

/-- A closed thread of the cover with one more pair runs through that pair. -/
theorem thread_of_add (hno : P.NoClosedThread) {e : Fin n} {x y : ℕ} {f : Fin n → ℕ}
    (hfF : ∀ i, f i ∈ P.F i) (hfM : ∀ i, (P.add e x y).M i (f i) (f (i + 1))) :
    (f e = x ∧ f (e + 1) = y) ∧ ∀ j, j ≠ e → P.M j (f j) (f (j + 1)) := by
  have hex : ∃ i, ¬ P.M i (f i) (f (i + 1)) := by
    by_contra h
    exact hno ⟨f, hfF, fun i => by
      by_contra h'
      exact h ⟨i, h'⟩⟩
  obtain ⟨i, hi⟩ := hex
  obtain ⟨rfl, hfx, hfy⟩ : i = e ∧ f i = x ∧ f (i + 1) = y := by
    rcases hfM i with h | h
    · exact absurd h hi
    · exact h
  refine ⟨⟨hfx, hfy⟩, fun j hj => ?_⟩
  rcases hfM j with h | h
  · exact h
  · exact absurd h.1 hj

/-- A maximal cover without a closed thread is full or has a cut section. -/
theorem full_or_cutSection {k : ℕ} (hcard : ∀ i, (P.F i).card = k) (hM : P.IsMatching)
    (hno : P.NoClosedThread) (hmax : P.Maximal) :
    (∀ i, ∀ x ∈ P.F i, ∃ y ∈ P.F (i + 1), P.M i x y) ∨ ∃ b e, P.IsCutSection b e := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfull, hcut⟩ := hcon
  apply hfull
  intro e x hx
  by_contra hxun
  have hxun' : ∀ y' ∈ P.F (e + 1), ¬ P.M e x y' := fun y' hy' h => hxun ⟨y', hy', h⟩
  -- some colour over `e + 1` is unmatched as well
  obtain ⟨y, hy, hyun⟩ : ∃ y ∈ P.F (e + 1), ∀ x' ∈ P.F e, ¬ P.M e x' y := by
    by_contra hall
    have hall' : ∀ y ∈ P.F (e + 1), ∃ x' ∈ P.F e, P.M e x' y := fun y hy => by
      by_contra h
      exact hall ⟨y, hy, fun x' hx' hm => h ⟨x', hx', hm⟩⟩
    choose! g hg using hall'
    have hginj : Set.InjOn g (P.F (e + 1)) := fun y hy y' hy' hgy =>
      (hM e).1 (g y) (hg y hy).1 y hy y' hy' (hg y hy).2 (hgy ▸ (hg y' hy').2)
    have hsub : (P.F (e + 1)).image g ⊆ (P.F e).erase x := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_erase.mpr ⟨fun h => hxun' y hy (h ▸ (hg y hy).2), (hg y hy).1⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hginj, Finset.card_erase_of_mem hx, hcard, hcard] at h1
    have : 0 < k := by rw [← hcard e]; exact Finset.card_pos.mpr ⟨x, hx⟩
    omega
  have hun : P.Unmatched e x y := ⟨hx, hy, hxun', hyun⟩
  have hthread := hmax e x y hun
  rw [NoClosedThread, not_not] at hthread
  obtain ⟨f, hfF, hfM⟩ := hthread
  -- the closed thread uses the new pair
  have hex : ∃ i, ¬ P.M i (f i) (f (i + 1)) := by
    by_contra h
    exact hno ⟨f, hfF, fun i => by
      by_contra h'
      exact h ⟨i, h'⟩⟩
  obtain ⟨i, hi⟩ := hex
  obtain ⟨rfl, hfx, hfy⟩ : i = e ∧ f i = x ∧ f (i + 1) = y := by
    rcases hfM i with h | h
    · exact absurd h hi
    · exact h
  refine hcut ⟨f, i, hfF, fun j hj => ?_, ?_, ?_⟩
  · rcases hfM j with h | h
    · exact h
    · exact absurd h.1 hj
  · rw [hfx]; exact hxun'
  · rw [hfy]; exact hyun

open Classical in
/-- The unmatched pairs of a cover. -/
noncomputable def unm (P : Cover n) : Finset (Fin n × ℕ × ℕ) :=
  ((univ : Finset (Fin n)) ×ˢ (univ.biUnion P.F ×ˢ univ.biUnion P.F)).filter
    fun t => P.Unmatched t.1 t.2.1 t.2.2

theorem mem_unm {t : Fin n × ℕ × ℕ} : t ∈ P.unm ↔ P.Unmatched t.1 t.2.1 t.2.2 := by
  classical
  simp only [unm, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_biUnion, and_iff_right_iff_imp]
  exact fun h => ⟨⟨_, h.1⟩, ⟨_, h.2.1⟩⟩

theorem unm_add_ssubset {e : Fin n} {x y : ℕ} (h : P.Unmatched e x y) :
    (P.add e x y).unm ⊂ P.unm := by
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(e, x, y), mem_unm.mpr h, fun hmem => ?_⟩
    exact (mem_unm.mp hmem).2.2.1 y h.2.1 (Or.inr ⟨rfl, rfl, rfl⟩)
  · intro t ht
    rw [mem_unm] at ht ⊢
    exact ⟨ht.1, ht.2.1, fun y' hy' hm => ht.2.2.1 y' hy' (Or.inl hm),
      fun x' hx' hm => ht.2.2.2 x' hx' (Or.inl hm)⟩

/-- **Reduction to maximal covers.** -/
theorem capGE_of_maximal {k : ℕ} {C : ℝ}
    (hstep : ∀ P : Cover n, (∀ i, (P.F i).card = k) → P.IsMatching → P.NoClosedThread →
      P.Maximal → ∀ b, P.CapGE univ b C) :
    ∀ P : Cover n, (∀ i, (P.F i).card = k) → P.IsMatching → P.NoClosedThread →
      ∀ b, P.CapGE univ b C := by
  have key : ∀ N, ∀ P : Cover n, P.unm.card = N → (∀ i, (P.F i).card = k) → P.IsMatching →
      P.NoClosedThread → ∀ b, P.CapGE univ b C := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro P hN hcard hM hno b
      by_cases hmax : P.Maximal
      · exact hstep P hcard hM hno hmax b
      · rw [Maximal] at hmax
        obtain ⟨e, x, y, hun, hno'⟩ :
            ∃ e x y, P.Unmatched e x y ∧ (P.add e x y).NoClosedThread := by
          by_contra h
          exact hmax fun e x y hun hno' => h ⟨e, x, y, hun, hno'⟩
        exact CapGE.of_add (ih _ (hN ▸ Finset.card_lt_card (unm_add_ssubset hun)) (P.add e x y)
          rfl hcard (add_isMatching hM hun) hno' b)
  exact fun P => key _ P rfl

/-! ### Removing a cut section -/

omit [NeZero n] in
theorem erase_card {k : ℕ} (hcard : ∀ i, (P.F i).card = k) {b : Fin n → ℕ}
    (hb : ∀ i, b i ∈ P.F i) (i : Fin n) : ((P.erase b).F i).card = k - 1 := by
  show ((P.F i).erase (b i)).card = k - 1
  rw [Finset.card_erase_of_mem (hb i), hcard]

theorem erase_isMatching (hM : P.IsMatching) (b : Fin n → ℕ) : (P.erase b).IsMatching :=
  fun i =>
    ⟨fun x hx y hy y' hy' => (hM i).1 x (Finset.mem_of_mem_erase hx) y
        (Finset.mem_of_mem_erase hy) y' (Finset.mem_of_mem_erase hy'),
      fun x hx x' hx' y hy => (hM i).2 x (Finset.mem_of_mem_erase hx) x'
        (Finset.mem_of_mem_erase hx') y (Finset.mem_of_mem_erase hy)⟩

theorem erase_noClosedThread (hno : P.NoClosedThread) (b : Fin n → ℕ) :
    (P.erase b).NoClosedThread :=
  fun ⟨f, hf, hfM⟩ => hno ⟨f, fun i => Finset.mem_of_mem_erase (hf i), hfM⟩

/-- An unmatched pair of the cover without `b` is an unmatched pair of the cover. -/
theorem unmatched_of_erase (hM : P.IsMatching) {b : Fin n → ℕ} {e : Fin n}
    (hb : P.IsCutSection b e) {e' : Fin n} {x y : ℕ} (h : (P.erase b).Unmatched e' x y) :
    P.Unmatched e' x y := by
  obtain ⟨hx, hy, hxu, hyu⟩ := h
  have hx' := Finset.mem_erase.mp hx
  have hy' := Finset.mem_erase.mp hy
  refine ⟨hx'.2, hy'.2, fun y' hy'' hm => ?_, fun x' hx'' hm => ?_⟩
  · by_cases hyb : y' = b (e' + 1)
    · subst hyb
      by_cases he : e' = e
      · subst he
        exact hb.2.2.2 x hx'.2 hm
      · exact hx'.1 ((hM e').2 x hx'.2 (b e') (hb.1 e') _ (hb.1 _) hm (hb.2.1 e' he))
    · exact hxu y' (Finset.mem_erase.mpr ⟨hyb, hy''⟩) hm
  · by_cases hxb : x' = b e'
    · subst hxb
      by_cases he : e' = e
      · subst he
        exact hb.2.2.1 y hy'.2 hm
      · exact hy'.1 ((hM e').1 (b e') (hb.1 e') y hy'.2 _ (hb.1 _) hm (hb.2.1 e' he))
    · exact hyu x' (Finset.mem_erase.mpr ⟨hxb, hx''⟩) hm

/-- A cut section of the cover without `b` is a cut section of the cover. -/
theorem isCutSection_of_erase (hM : P.IsMatching) {b : Fin n → ℕ} {e : Fin n}
    (hb : P.IsCutSection b e) {b' : Fin n → ℕ} {e' : Fin n}
    (hb' : (P.erase b).IsCutSection b' e') : P.IsCutSection b' e' := by
  have hun : (P.erase b).Unmatched e' (b' e') (b' (e' + 1)) :=
    ⟨hb'.1 _, hb'.1 _, hb'.2.2.1, hb'.2.2.2⟩
  have hun' := unmatched_of_erase hM hb hun
  exact ⟨fun i => Finset.mem_of_mem_erase (hb'.1 i), hb'.2.1, hun'.2.2.1, hun'.2.2.2⟩

/-- Removing a cut section from a maximal cover leaves a maximal cover. -/
theorem maximal_erase (hM : P.IsMatching) (hno : P.NoClosedThread) (hmax : P.Maximal) {b : Fin n → ℕ} {e : Fin n}
    (hb : P.IsCutSection b e) : (P.erase b).Maximal := by
  intro e' x y hun hno'
  have hunP := unmatched_of_erase hM hb hun
  have hthread := hmax e' x y hunP
  rw [NoClosedThread, not_not] at hthread
  obtain ⟨f, hfF, hfM⟩ := hthread
  -- the thread through the new pair
  obtain ⟨hfe, hfM'⟩ := thread_of_add hno hfF hfM
  have hxb : x ≠ b e' := (Finset.mem_erase.mp hun.1).1
  -- it never meets `b`
  have hne : ∀ j, f j ≠ b j := by
    intro j hj
    have hall : ∀ t, f t = b t := by
      refine forall_of_succ (Q := fun t => f t = b t) hj fun t ht => ?_
      by_cases hte' : t = e'
      · subst hte'
        exact absurd (hfe.1.symm.trans ht) hxb
      · have hm := hfM' t hte'
        rw [ht] at hm
        by_cases hte : t = e
        · subst hte
          exact absurd hm (hb.2.2.1 _ (hfF _))
        · exact (hM t).1 (b t) (hb.1 t) _ (hfF _) _ (hb.1 _) hm (hb.2.1 t hte)
    exact hxb (hfe.1.symm.trans (hall e'))
  exact hno' ⟨f, fun i => Finset.mem_erase.mpr ⟨hne i, hfF i⟩, hfM⟩

/-- Two cut sections of a maximal cover that differ over `e` are not cut at the same edge. -/
theorem cut_edge_ne (hM : P.IsMatching) (hno : P.NoClosedThread) (hmax : P.Maximal) {b b' : Fin n → ℕ} {e e' : Fin n}
    (hb : P.IsCutSection b e) (hb' : P.IsCutSection b' e') (hne : b e ≠ b' e) : e ≠ e' := by
  rintro rfl
  have hun : P.Unmatched e (b e) (b' (e + 1)) := ⟨hb.1 _, hb'.1 _, hb.2.2.1, hb'.2.2.2⟩
  have hthread := hmax e _ _ hun
  rw [NoClosedThread, not_not] at hthread
  obtain ⟨f, hfF, hfM⟩ := hthread
  obtain ⟨hfe, hfM'⟩ := thread_of_add hno hfF hfM
  have hall : ∀ t, f t = b' t := by
    refine forall_of_succ (Q := fun t => f t = b' t) hfe.2 fun t ht => ?_
    by_cases hte : t = e
    · subst hte
      exact absurd (hfe.1.symm.trans ht) hne
    · have h := hfM' t hte
      rw [ht] at h
      exact (hM t).1 (b' t) (hb'.1 t) _ (hfF _) _ (hb'.1 _) h (hb'.2.1 t hte)
  exact hne (hfe.1.symm.trans (hall e))

end Cover

end Outerplanar
