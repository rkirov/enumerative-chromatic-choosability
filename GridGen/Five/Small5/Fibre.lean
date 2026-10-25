/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Cone

/-!
# Height five: fibre bounds and row reflection for the exact certificates

**Fibres.** `GridGen/Four/Fibre6.lean` with five rows. Under the uniform weighting
`u = GU 6 w` of the proper columns of lists `X₁, …, X₅` of at least five colours, any property
that pins one row to a function of the others has weight at most `q · Σ u`, with
`q = 1000/3877` for an end row (four other admissible colours) and `q = 1000/2918` for a middle
row (three): the weights of two proper columns differ by at most the factor `1000/959`
(`GU_ratio`, from the invariant box), and the sharp double counting of `Four.fibre_row_sharp`
applies (`fibre_row`). Pinning to a colour of a set `S` costs `q · |S|` (`fibre_set`), and an
equality `sᵢ = sⱼ` is a pin of row `i` (`fibre_pair`).

**Reflection.** Reversing the rows maps the proper columns of `X₁, …, X₅` onto those of
`X₅, …, X₁`, preserves the orbit (`orb_rev`), hence `GU` and `GB` with reversed lists, so the seam
inequality for reversed lists implies it for the original ones (`seam_of_rev`).
-/

namespace GridGen.Five.Ex5

open Finset

/-! ### The sharp one-row fibre bound, for any finite set -/

theorem fibre_row_sharp {α : Type*} [DecidableEq α] {Ω : Finset α} (w : α → ℝ)
    (hw : ∀ t, 0 ≤ w t) (P : α → Prop) [DecidablePred P] (get : α → ℕ) (set : α → ℕ → α)
    (φ : α → ℕ) (opts : α → Finset ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hopts : ∀ t ∈ Ω, m ≤ (opts t).card) (hcur : ∀ t ∈ Ω, get t ∈ opts t)
    (hmem : ∀ t ∈ Ω, ∀ x ∈ opts t, set t x ∈ Ω) (hget : ∀ t x, get (set t x) = x)
    (hset : ∀ t₁ t₂ x₁ x₂, set t₁ x₁ = set t₂ x₂ → get t₁ = get t₂ → t₁ = t₂)
    (hφ : ∀ t x, φ (set t x) = φ t) (hP : ∀ t, P t → get t = φ t)
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, w t ≤ R * w t') :
    (R + ((m : ℝ) - 1)) * ∑ t ∈ Ω.filter P, w t ≤ R * ∑ t ∈ Ω, w t := by
  classical
  set S := (Ω.filter P).sigma (fun t => (opts t).erase (get t)) with hS
  have h1 : ((m : ℝ) - 1) * ∑ t ∈ Ω.filter P, w t ≤ ∑ p ∈ S, w p.1 := by
    rw [hS, Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨htΩ, -⟩ := Finset.mem_filter.mp ht
    show ((m : ℝ) - 1) * w t ≤ ∑ _x ∈ (opts t).erase (get t), w t
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (m : ℝ) - 1 ≤ ((opts t).erase (get t)).card := by
      rw [Finset.card_erase_of_mem (hcur t htΩ)]
      have := hopts t htΩ
      have h1 : 1 ≤ (opts t).card := le_trans hm this
      rw [Nat.cast_sub h1]; push_cast
      have : (m : ℝ) ≤ (opts t).card := by exact_mod_cast this
      linarith
    exact mul_le_mul_of_nonneg_right hc (hw t)
  have h2 : ∑ p ∈ S, w p.1 ≤ ∑ p ∈ S, R * w (set p.1 p.2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨ht, hx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨htΩ, -⟩ := Finset.mem_filter.mp ht
    exact hR p.1 htΩ _ (hmem p.1 htΩ p.2 (Finset.mem_of_mem_erase hx))
  have hinjS : Set.InjOn (fun p : (_ : α) × ℕ => set p.1 p.2) S := by
    intro p hp q hq hpq
    obtain ⟨hpt, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hqt, hqx⟩ := Finset.mem_sigma.mp hq
    obtain ⟨-, hpP⟩ := Finset.mem_filter.mp hpt
    obtain ⟨-, hqP⟩ := Finset.mem_filter.mp hqt
    have hx : p.2 = q.2 := by
      have := congrArg get hpq; simp only [hget] at this; exact this
    have hg : get p.1 = get q.1 := by
      rw [hP _ hpP, hP _ hqP, ← hφ p.1 p.2, ← hφ q.1 q.2]
      exact congrArg φ hpq
    exact Sigma.ext (hset _ _ _ _ hpq hg) (heq_of_eq hx)
  have h3 : ∑ p ∈ S, w (set p.1 p.2) ≤ ∑ t ∈ Ω.filter (fun t => ¬ P t), w t := by
    rw [← Finset.sum_image (f := w) hinjS]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => hw t)
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hpt, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpΩ, hpP⟩ := Finset.mem_filter.mp hpt
    refine Finset.mem_filter.mpr ⟨hmem p.1 hpΩ p.2 (Finset.mem_of_mem_erase hpx), fun hP' => ?_⟩
    have e1 := hP _ hP'
    rw [hget, hφ, ← hP _ hpP] at e1
    exact (Finset.ne_of_mem_erase hpx) e1
  have h4 : ∑ t ∈ Ω, w t = ∑ t ∈ Ω.filter P, w t + ∑ t ∈ Ω.filter (fun t => ¬ P t), w t :=
    (Finset.sum_filter_add_sum_filter_not Ω P w).symm
  have h5 : ∑ p ∈ S, R * w (set p.1 p.2) = R * ∑ p ∈ S, w (set p.1 p.2) := by
    rw [Finset.mul_sum]
  have h6 := mul_le_mul_of_nonneg_left h3 hR0.le
  nlinarith

/-! ### Rows of a column by index -/

/-- Row `i + 1` of a column (row 5 for `i ≥ 4`). -/
def rowAt (i : ℕ) (t : T5) : ℕ :=
  match i with
  | 0 => r1 t
  | 1 => r2 t
  | 2 => r3 t
  | 3 => r4 t
  | _ => r5 t

/-- Overwrite row `i + 1`. -/
def setAt (i : ℕ) (t : T5) (x : ℕ) : T5 :=
  match i with
  | 0 => (x, t.2)
  | 1 => (t.1, x, t.2.2)
  | 2 => (t.1, t.2.1, x, t.2.2.2)
  | 3 => (t.1, t.2.1, t.2.2.1, x, t.2.2.2.2)
  | _ => (t.1, t.2.1, t.2.2.1, t.2.2.2.1, x)

/-- The admissible new colours of row `i + 1`: its list minus the neighbouring colours. -/
def optsAt (X₁ X₂ X₃ X₄ X₅ : Finset ℕ) (i : ℕ) (t : T5) : Finset ℕ :=
  match i with
  | 0 => X₁.erase (r2 t)
  | 1 => (X₂.erase (r1 t)).erase (r3 t)
  | 2 => (X₃.erase (r2 t)).erase (r4 t)
  | 3 => (X₄.erase (r3 t)).erase (r5 t)
  | _ => X₅.erase (r4 t)

/-- The number of admissible colours: `|X| - 1` at an end row, `|X| - 2` in the middle. -/
def nopt (i : ℕ) : ℕ := if i = 0 ∨ 4 ≤ i then 4 else 3

theorem getAt_setAt (i : ℕ) (t : T5) (x : ℕ) : rowAt i (setAt i t x) = x := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

theorem setAt_inj (i : ℕ) (t₁ t₂ : T5) (x₁ x₂ : ℕ) (he : setAt i t₁ x₁ = setAt i t₂ x₂)
    (hg : rowAt i t₁ = rowAt i t₂) : t₁ = t₂ := by
  obtain ⟨a, b, c, d, e⟩ := t₁
  obtain ⟨a', b', c', d', e'⟩ := t₂
  match i with
  | 0 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5]
  | 1 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5]
  | 2 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5]
  | 3 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5]
  | _ + 4 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5]

theorem rowAt_setAt_ne {i j : ℕ} (hij : i ≠ j) (hi : i < 5) (hj : j < 5) (t : T5) (x : ℕ) :
    rowAt j (setAt i t x) = rowAt j t := by
  obtain ⟨a, b, c, d, e⟩ := t
  interval_cases i <;> interval_cases j <;> first | omega | rfl

theorem card_erase_ge (A : Finset ℕ) (a : ℕ) : A.card - 1 ≤ (A.erase a).card :=
  Finset.pred_card_le_card_erase

theorem optsAt_card {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card)
    (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card) (hX₅ : 5 ≤ X₅.card) {i : ℕ} (hi : i < 5) (t : T5) :
    nopt i ≤ (optsAt X₁ X₂ X₃ X₄ X₅ i t).card := by
  interval_cases i <;> simp only [nopt, optsAt] <;> norm_num
  · have := card_erase_ge X₁ (r2 t); omega
  · have := card_erase_ge X₂ (r1 t); have := card_erase_ge (X₂.erase (r1 t)) (r3 t); omega
  · have := card_erase_ge X₃ (r2 t); have := card_erase_ge (X₃.erase (r2 t)) (r4 t); omega
  · have := card_erase_ge X₄ (r3 t); have := card_erase_ge (X₄.erase (r3 t)) (r5 t); omega
  · have := card_erase_ge X₅ (r4 t); omega

theorem optsAt_cur {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} {i : ℕ} (hi : i < 5) {t : T5}
    (ht : t ∈ sts X₁ X₂ X₃ X₄ X₅) : rowAt i t ∈ optsAt X₁ X₂ X₃ X₄ X₅ i t := by
  rw [mem_sts] at ht
  obtain ⟨h1, h2, h3, h4, h5, p1, p2, p3, p4⟩ := ht
  interval_cases i <;> simp only [rowAt, optsAt, Finset.mem_erase] <;> grind

theorem optsAt_mem {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} {i : ℕ} (hi : i < 5) {t : T5}
    (ht : t ∈ sts X₁ X₂ X₃ X₄ X₅) {x : ℕ} (hx : x ∈ optsAt X₁ X₂ X₃ X₄ X₅ i t) :
    setAt i t x ∈ sts X₁ X₂ X₃ X₄ X₅ := by
  obtain ⟨a, b, c, d, e⟩ := t
  rw [mem_sts] at ht ⊢
  interval_cases i <;> simp only [optsAt, setAt, Finset.mem_erase, r1, r2, r3, r4, r5] at hx ht ⊢ <;>
    grind

/-! ### Weights of the uniform successors -/

theorem lo5_ge : ∀ j : Fin 11, (959 / 1000 : ℚ) ≤ lo5 j := by decide +kernel

theorem rowV_ratio {w : Wt5} (hw : InBox5 w) (i j : Fin 11) :
    rowV i w ≤ (1000 / 959) * rowV j w := by
  have hpos := rowV_pos hw
  have hb := nextW_inBox hw
  obtain ⟨-, hi⟩ := hb i
  obtain ⟨hj, -⟩ := hb j
  unfold nextW at hi hj
  rw [div_le_one hpos] at hi
  rw [le_div_iff₀ hpos] at hj
  have h959 : ((959 / 1000 : ℚ) : ℝ) ≤ (lo5 j : ℝ) := by exact_mod_cast lo5_ge j
  push_cast at h959
  nlinarith

theorem gw_nonneg {w : Wt5} (hw : InBox5 w) (t : T5) : 0 ≤ gw w t := by
  have h959 : ((959 / 1000 : ℚ) : ℝ) ≤ (lo5 (orb t) : ℝ) := by exact_mod_cast lo5_ge (orb t)
  have := (hw (orb t)).1
  unfold gw; push_cast at h959; linarith

theorem G_nonneg {w : Wt5} (hw : InBox5 w) (A B C D E : Finset ℕ) : 0 ≤ G w A B C D E :=
  Finset.sum_nonneg fun t _ => gw_nonneg hw t

theorem GU_nonneg {w : Wt5} (hw : InBox5 w) (s : T5) : 0 ≤ GU 6 w s := G_nonneg hw _ _ _ _ _

theorem GU_ratio {w : Wt5} (hw : InBox5 w) {s t : T5} (hs : Proper s) (ht : Proper t) :
    GU 6 w s ≤ (1000 / 959) * GU 6 w t := by
  rw [GU_six w hs, GU_six w ht]; exact rowV_ratio hw _ _

/-! ### Fibre bounds under the uniform weighting -/

/-- The fibre ratio of row `i + 1`. -/
noncomputable def qrow (i : ℕ) : ℝ := if i = 0 ∨ 4 ≤ i then 1000 / 3877 else 1000 / 2918

/-- **One-row fibres**: a property pinning row `i + 1` to a function of the other rows has
uniform weight at most `qrow i` of the total. -/
theorem fibre_row {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (hX₁ : 5 ≤ X₁.card)
    (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card) (hX₅ : 5 ≤ X₅.card)
    {i : ℕ} (hi : i < 5) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (setAt i t x) = φ t) (hP : ∀ t, P t → rowAt i t = φ t) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter P, GU 6 w t
      ≤ qrow i * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := by
  have h := fibre_row_sharp (Ω := sts X₁ X₂ X₃ X₄ X₅) (GU 6 w) (GU_nonneg hw) P (rowAt i) (setAt i) φ
    (optsAt X₁ X₂ X₃ X₄ X₅ i) (nopt i) (by unfold nopt; split_ifs <;> norm_num)
    (fun t _ => optsAt_card hX₁ hX₂ hX₃ hX₄ hX₅ hi t) (fun t ht => optsAt_cur hi ht)
    (fun t ht x hx => optsAt_mem hi ht hx) (getAt_setAt i)
    (fun t₁ t₂ x₁ x₂ he hg => setAt_inj i t₁ t₂ x₁ x₂ he hg) hφ hP (R := 1000 / 959)
    (by norm_num) (fun t ht t' ht' => GU_ratio hw (proper_of_mem_sts ht) (proper_of_mem_sts ht'))
  have hW : 0 ≤ ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter P, GU 6 w t :=
    Finset.sum_nonneg fun t _ => GU_nonneg hw t
  unfold qrow nopt at *
  split_ifs at h ⊢ <;> push_cast at h <;> nlinarith

/-- **Fibres over a colour set.** -/
theorem fibre_set {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (hX₁ : 5 ≤ X₁.card)
    (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card) (hX₅ : 5 ≤ X₅.card)
    {i : ℕ} (hi : i < 5) (S : Finset ℕ) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter (fun t => rowAt i t ∈ S), GU 6 w t
      ≤ qrow i * S.card * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := by
  have e : ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter (fun t => rowAt i t ∈ S), GU 6 w t
      = ∑ c ∈ S, ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter (fun t => rowAt i t = c), GU 6 w t := by
    rw [Finset.sum_filter]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
  rw [e]
  have hc : ∀ c ∈ S, ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter (fun t => rowAt i t = c), GU 6 w t
      ≤ qrow i * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := fun c _ =>
    fibre_row hw hX₁ hX₂ hX₃ hX₄ hX₅ hi _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  calc _ ≤ ∑ _c ∈ S, qrow i * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := Finset.sum_le_sum hc
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Fibres of an equality**, pinned through row `i + 1`. -/
theorem fibre_pair {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (hX₁ : 5 ≤ X₁.card)
    (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card) (hX₅ : 5 ≤ X₅.card)
    {i j : ℕ} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter (fun t => rowAt i t = rowAt j t), GU 6 w t
      ≤ qrow i * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t :=
  fibre_row hw hX₁ hX₂ hX₃ hX₄ hX₅ hi _ (rowAt j) (fun t x => rowAt_setAt_ne hij hi hj t x)
    (fun _ h => h)

/-! ### Row reflection -/

/-- Reverse the rows of a column. -/
def rev5 (t : T5) : T5 := (r5 t, r4 t, r3 t, r2 t, r1 t)

theorem samePat_rev {s t : T5} (h : SamePat s t) : SamePat (rev5 s) (rev5 t) := by
  obtain ⟨h13, h24, h35, h14, h25, h15⟩ := h
  simp only [SamePat, rev5, r1, r2, r3, r4, r5] at *
  exact ⟨eq_comm.trans (h35.trans eq_comm), eq_comm.trans (h24.trans eq_comm),
    eq_comm.trans (h13.trans eq_comm), eq_comm.trans (h25.trans eq_comm),
    eq_comm.trans (h14.trans eq_comm), eq_comm.trans (h15.trans eq_comm)⟩

theorem orb_rev_canons : ∀ c ∈ canons, orb (rev5 c) = orb c := by decide +kernel

theorem orb_rev {t : T5} (ht : Proper t) : orb (rev5 t) = orb t := by
  have hs := samePat_canon ht
  rw [orb_congr (samePat_rev hs), orb_congr hs]
  exact orb_rev_canons _ (canon_mem ht)

theorem mem_sts_rev {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} {t : T5} :
    rev5 t ∈ sts X₅ X₄ X₃ X₂ X₁ ↔ t ∈ sts X₁ X₂ X₃ X₄ X₅ := by
  simp only [mem_sts, rev5, r1, r2, r3, r4, r5]
  grind

theorem sum_sts_rev {β : Type*} [AddCommMonoid β] (X₁ X₂ X₃ X₄ X₅ : Finset ℕ) (f : T5 → β) :
    ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, f t = ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, f (rev5 t) := by
  refine Finset.sum_nbij' rev5 rev5 (fun t ht => ?_) (fun t ht => ?_) (fun t _ => rfl)
    (fun t _ => rfl) (fun t _ => rfl)
  · exact mem_sts_rev.mpr ht
  · exact mem_sts_rev.mpr ht

theorem G_rev (w : Wt5) (A B C D E : Finset ℕ) : G w A B C D E = G w E D C B A := by
  unfold G
  rw [sum_sts_rev]
  refine Finset.sum_congr rfl fun t ht => ?_
  unfold gw
  rw [orb_rev (proper_of_mem_sts ht)]

theorem GU_rev (w : Wt5) {s : T5} (hs : Proper s) : GU 6 w (rev5 s) = GU 6 w s := by
  have hs' : Proper (rev5 s) := by
    obtain ⟨p1, p2, p3, p4⟩ := hs
    exact ⟨Ne.symm p4, Ne.symm p3, Ne.symm p2, Ne.symm p1⟩
  rw [GU_six w hs, GU_six w hs', orb_rev hs]

theorem GB_rev (w : Wt5) (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) :
    GB w B₅ B₄ B₃ B₂ B₁ (rev5 s) = GB w B₁ B₂ B₃ B₄ B₅ s := by
  unfold GB
  rw [G_rev]
  rfl

/-- **Row reflection**: the seam inequality for the reversed lists gives it for the lists. -/
theorem seam_of_rev {w : Wt5} {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (h : ∑ s ∈ sts X₅ X₄ X₃ X₂ X₁, GU 6 w s ≤ ∑ s ∈ sts X₅ X₄ X₃ X₂ X₁, GB w B₅ B₄ B₃ B₂ B₁ s) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  rw [sum_sts_rev X₁, sum_sts_rev X₁ X₂ X₃ X₄ X₅ (GB w B₁ B₂ B₃ B₄ B₅)]
  have e1 : ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GU 6 w (rev5 t) = ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GU 6 w t :=
    Finset.sum_congr rfl fun t ht => GU_rev w (proper_of_mem_sts ht)
  have e2 : ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GB w B₁ B₂ B₃ B₄ B₅ (rev5 t)
      = ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GB w B₅ B₄ B₃ B₂ B₁ t :=
    Finset.sum_congr rfl fun t _ => by rw [← GB_rev w B₅ B₄ B₃ B₂ B₁ t]
  rw [e1, e2]; exact h

end GridGen.Five.Ex5
