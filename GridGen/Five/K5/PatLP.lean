/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.Peel

/-!
# Height five at `k = 5`: the chain polytope and its dual certificates

The pattern lemma of `ai_research_notes/cx/h5k5/NOTE.md` §2 (Codex) and
`H5_K5_REVIEW_2026-10-28.md` (b). For lists `A₁, …, A₅` of sizes `nᵢ`, a row has
`frc nᵢ i` free colours (`nᵢ - 1` at an end, `nᵢ - 2` in the middle), and an event given by
equalities `rᵢ = jᵢ`, peeled in a valid order, holds on at most a `1/B` share of the proper
columns, `B` the product of the free counts of the peeled rows (`ev_count`, from
`peel_chain5` with unit weights).

A dual certificate (`PatCert`) of the resulting linear programme in the pattern shares, at a
weight `g` (a ray `F_d` or `2·10⁶` times the midpoint of `Q`), is a level `Λ` and multipliers `Z`
with `Λ ≤ D · g(o(c)) + Σ_e Z_e B_e [c ∈ e]` at each canonical pattern `c` (`ptOK`); it gives
`Λ · N ≤ D · Σₜ g(o(t)) + (Σ Z) · N` (`lp_count5`).
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-- A pattern certificate for one size vector: the events (peel lists of equalities), the levels
at the six generators, the multipliers, and the ratio bounds `R(n, o) · 10⁹`. -/
structure PatCert where
  ev : List (List (ℕ × ℕ))
  lam : List ℕ
  zs : List (List ℕ)
  R : List ℕ

instance : Inhabited PatCert := ⟨⟨[], [], [], []⟩⟩

/-- The scale of the dual certificates. -/
def DP : ℕ := 100000000

/-! ### Events -/

/-- The free count of row `r` for the size vector `nv`. -/
def frcL (nv : List ℕ) (r : ℕ) : ℕ := frc (nv.getD r 0) r

/-- The product of the free counts of the peeled rows. -/
def evB (nv : List ℕ) (ev : List (ℕ × ℕ)) : ℕ := (ev.map (fun e => frcL nv e.1)).prod

/-- A valid peel order of equalities. -/
def peelOKB : List (ℕ × ℕ) → Bool
  | [] => true
  | e :: es => decide (e.1 < 5 ∧ e.2 < 5 ∧ e.2 ≠ e.1) &&
      es.all (fun g => g.1 != e.1 && g.2 != e.1) && peelOKB es

/-- The event holds on a column. -/
def evHolds (ev : List (ℕ × ℕ)) (c : T5) : Bool := ev.all (fun e => rowAt e.1 c == rowAt e.2 c)

/-- The factors of an event. -/
def evFacs (ev : List (ℕ × ℕ)) : List Fac5 := ev.map (fun e => Fac5.eqr e.1 e.2)

theorem allEv5_evFacs (ev : List (ℕ × ℕ)) (t : T5) : allEv5 (evFacs ev) t = evHolds ev t := by
  unfold allEv5 evFacs evHolds
  rw [List.all_map]
  congr 1

theorem peelOK_evFacs : ∀ ev : List (ℕ × ℕ), peelOKB ev = true →
    PeelOK5 (fun _ => false) (evFacs ev)
  | [], _ => trivial
  | e :: es, h => by
    simp only [peelOKB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩ := h
    refine ⟨rfl, ?_, ⟨h1, h2, h3⟩, peelOK_evFacs es h5⟩
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have := h4 g' hg'
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    simp only [Fac5.row, Fac5.reads, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨decide_eq_false this.1, decide_eq_false this.2⟩

theorem evFacs_bnd (nv : List ℕ) (q : ℕ → ℚ) (hq : ∀ r < 5, q r = 1 / frcL nv r) :
    ∀ ev : List (ℕ × ℕ), peelOKB ev = true →
      ((evFacs ev).map (Fac5.bnd q)).prod = 1 / (evB nv ev : ℚ)
  | [], _ => by simp [evFacs, evB]
  | e :: es, h => by
    simp only [peelOKB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := evFacs_bnd nv q hq es h.2
    simp only [evFacs, List.map_cons, List.prod_cons, evB] at ih ⊢
    rw [ih, Fac5.bnd, hq e.1 h.1.1.1]
    push_cast
    rw [one_div_mul_one_div]

theorem evB_pos {nv : List ℕ} (hn : ∀ i < 5, 1 ≤ frcL nv i) :
    ∀ ev : List (ℕ × ℕ), peelOKB ev = true → 0 < evB nv ev
  | [], _ => by simp [evB]
  | e :: es, h => by
    simp only [peelOKB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := evB_pos hn es h.2
    simp only [evB, List.map_cons, List.prod_cons] at ih ⊢
    exact Nat.mul_pos (hn _ h.1.1.1) ih

/-- **The chain bound of an event.** -/
theorem ev_count {A₁ A₂ A₃ A₄ A₅ : Finset ℕ} {nv : List ℕ}
    (hX : ∀ i < 5, nv.getD i 0 ≤ (bl A₁ A₂ A₃ A₄ A₅ i).card)
    (hn : ∀ i < 5, 1 ≤ frcL nv i) (ev : List (ℕ × ℕ)) (hev : peelOKB ev = true) :
    evB nv ev * ((sts A₁ A₂ A₃ A₄ A₅).filter (fun t => evHolds ev t = true)).card
      ≤ (sts A₁ A₂ A₃ A₄ A₅).card := by
  set q : ℕ → ℚ := fun r => 1 / frcL nv r with hq
  have hF := fibOK_sts (fun i => nv.getD i 0) hX hn (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (R := 1) one_pos (fun _ _ _ _ => by norm_num) q
    (fun i _ => by simp only [hq, frcL]; push_cast; ring)
  have hq0 : ∀ i, 0 ≤ q i := fun i => by simp only [hq]; positivity
  have h := peel_chain5 hF (fun _ => zero_le_one) hq0 (fun _ => false) (fun _ => true)
    (fun _ _ _ _ _ => rfl) (evFacs ev) (peelOK_evFacs ev hev)
  rw [evFacs_bnd nv q (fun r _ => rfl) ev hev] at h
  simp only [Bool.and_true, allEv5_evFacs, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_true_of_mem (fun _ _ => rfl)] at h
  have hB : (0 : ℕ) < evB nv ev := evB_pos hn ev hev
  have hB' : (0 : ℝ) < evB nv ev := by exact_mod_cast hB
  have : (evB nv ev : ℝ) * ((sts A₁ A₂ A₃ A₄ A₅).filter (fun t => evHolds ev t = true)).card
      ≤ (sts A₁ A₂ A₃ A₄ A₅).card := by
    push_cast at h
    rw [Finset.filter_true] at h
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hB'] at h
    linarith
  exact_mod_cast this

/-! ### Weak duality -/

/-- The multiplier sum of the events containing a column. -/
def ptSumL (nv : List ℕ) (c : T5) : List (List (ℕ × ℕ)) → List ℕ → ℕ
  | ev :: evs, z :: zs => (if evHolds ev c = true then z * evB nv ev else 0) + ptSumL nv c evs zs
  | _, _ => 0

/-- The multiplier total. -/
def zsumL : List (List (ℕ × ℕ)) → List ℕ → ℕ
  | _ :: evs, z :: zs => z + zsumL evs zs
  | _, _ => 0

theorem ptSumL_congr (nv : List ℕ) {s t : T5} (h : ∀ i < 5, ∀ j < 5, rowAt i s = rowAt j s ↔
    rowAt i t = rowAt j t) : ∀ evs zs, (∀ ev ∈ evs, peelOKB ev = true) →
    ptSumL nv s evs zs = ptSumL nv t evs zs
  | ev :: evs, z :: zs, hv => by
    have he : evHolds ev s = evHolds ev t := by
      have hev := hv ev List.mem_cons_self
      unfold evHolds
      clear hv
      induction ev with
      | nil => rfl
      | cons e es ih =>
        simp only [peelOKB, Bool.and_eq_true, decide_eq_true_eq] at hev
        simp only [List.all_cons]
        rw [ih hev.2]
        congr 1
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        exact h _ hev.1.1.1 _ hev.1.1.2.1
    simp only [ptSumL, he, ptSumL_congr nv h evs zs (fun e he => hv e (List.mem_cons_of_mem _ he))]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem sum_ptSumL {Ω : Finset T5} {nv : List ℕ} :
    ∀ evs zs, (∀ ev ∈ evs, evB nv ev * (Ω.filter (fun t => evHolds ev t = true)).card ≤ Ω.card) →
      ∑ t ∈ Ω, ptSumL nv t evs zs ≤ zsumL evs zs * Ω.card
  | ev :: evs, z :: zs, h => by
    have ih := sum_ptSumL (Ω := Ω) (nv := nv) evs zs (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [ptSumL, zsumL, Finset.sum_add_distrib]
    have h1 : ∑ t ∈ Ω, (if evHolds ev t = true then z * evB nv ev else 0)
        = z * evB nv ev * (Ω.filter (fun t => evHolds ev t = true)).card := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    have h2 := h ev List.mem_cons_self
    rw [h1]
    calc z * evB nv ev * (Ω.filter (fun t => evHolds ev t = true)).card + ∑ t ∈ Ω, ptSumL nv t evs zs
        ≤ z * Ω.card + zsumL evs zs * Ω.card := by
          refine Nat.add_le_add ?_ ih
          rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left z h2
      _ = (z + zsumL evs zs) * Ω.card := by ring
  | [], _, _ => by simp [ptSumL, zsumL]
  | _ :: _, [], _ => by simp [ptSumL, zsumL]

/-- The generator values: the rays `F_k` (`k < 5`) and `qL + qU` (`k = 5`). -/
def gval (k : ℕ) (o : Fin 11) : ℕ := if k < 5 then Fv k o else qL o + qU o

/-- The pointwise dual check at generator `k`. -/
def ptOK (nv : List ℕ) (C : PatCert) (k : ℕ) : Bool :=
  canons.all fun c => decide (C.lam.getD k 0 ≤ DP * gval k (orb c) + ptSumL nv c C.ev (C.zs.getD k []))

theorem eqv_canon' {s : T5} (hs : Proper s) :
    ∀ i < 5, ∀ j < 5, rowAt i (canon s) = rowAt j (canon s) ↔ rowAt i s = rowAt j s :=
  fun i hi j hj => (eqv_canon hs hi hj).symm

/-- **Weak duality, in counts.** -/
theorem lp_count5 {A₁ A₂ A₃ A₄ A₅ : Finset ℕ} {nv : List ℕ} {C : PatCert} {k : ℕ}
    (hev : ∀ ev ∈ C.ev, peelOKB ev = true)
    (hB : ∀ ev ∈ C.ev, evB nv ev * ((sts A₁ A₂ A₃ A₄ A₅).filter (fun t => evHolds ev t = true)).card
      ≤ (sts A₁ A₂ A₃ A₄ A₅).card)
    (hpt : ptOK nv C k = true) :
    C.lam.getD k 0 * (sts A₁ A₂ A₃ A₄ A₅).card
      ≤ DP * ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, gval k (orb t)
        + zsumL C.ev (C.zs.getD k []) * (sts A₁ A₂ A₃ A₄ A₅).card := by
  set Ω := sts A₁ A₂ A₃ A₄ A₅
  have hpt' : ∀ t ∈ Ω, C.lam.getD k 0 ≤ DP * gval k (orb t) + ptSumL nv t C.ev (C.zs.getD k []) := by
    intro t ht
    have hs := proper_of_mem_sts ht
    have hc := List.all_eq_true.mp hpt (canon t) (canon_mem hs)
    rw [decide_eq_true_eq] at hc
    rw [orb_congr (samePat_canon hs), ← ptSumL_congr nv (eqv_canon' hs) _ _ hev]
    exact hc
  have h1 : C.lam.getD k 0 * Ω.card ≤ ∑ t ∈ Ω, (DP * gval k (orb t) + ptSumL nv t C.ev (C.zs.getD k [])) := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hpt'
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have h2 := sum_ptSumL (Ω := Ω) (nv := nv) C.ev (C.zs.getD k []) hB
  omega

end GridGen.Five.K5
