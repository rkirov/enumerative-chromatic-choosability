/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Box

/-!
# The slab with a relaxed first future column

In the gauge telescope the next column's states are coloured from lists, so two adjacent cells
of that column clash only on a *shared* colour. Read through the next gauge, which is vertically
consistent, a clash is an equal label of a shared colour. The other diagonal label pairs are
allowed. `slabR` is the slab with those pairs allowed: `R v` holds the labels that the cells
`(2, v)` and `(2, v + 1)` may share.

* `slabR_empty`: with nothing relaxed it is the slab.
* `card_relax`: relaxing one more label adds exactly the solutions that use it on both cells.
* `card_Ω_R`: its solutions are counted by past, seam and a relaxed first future column
  (`statesR`), then uniform futures.
-/

open Finset SimpleGraph
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-- The pair of cells `x, y` is a vertical edge of the first future column whose lower row is
relaxed at the label `a`. -/
def relaxV (R : Fin m → Finset ℕ) (x y : Cell c m) (a : ℕ) : Prop :=
  x.1.val = 2 ∧ y.1.val = 2 ∧ ((x.2.val + 1 = y.2.val ∧ a ∈ R x.2) ∨ (y.2.val + 1 = x.2.val ∧ a ∈ R y.2))

/-- **The relaxed slab.** -/
def slabR (c m k : ℕ) (P A : Fin m → Finset ℕ) (M : Fin m → ℕ → ℕ) (R : Fin m → Finset ℕ) :
    CSP (Cell c m) where
  adj := slabAdj
  D := (slab c m k P A M).D
  conf x y a b := (slab c m k P A M).conf x y a b ∧ ¬ (a = b ∧ relaxV R x y a)

variable {R : Fin m → Finset ℕ}

theorem slabR_D (x : Cell c m) : (slabR c m k P A M R).D x = (slab c m k P A M).D x := rfl

theorem slabR_conf {x y : Cell c m} {a b : ℕ} :
    (slabR c m k P A M R).conf x y a b ↔
      (slab c m k P A M).conf x y a b ∧ ¬ (a = b ∧ relaxV R x y a) := Iff.rfl

theorem slabR_empty : (slabR c m k P A M (fun _ => ∅)).Ω = (slab c m k P A M).Ω := by
  unfold CSP.Ω
  refine filter_congr fun f _ => ?_
  unfold CSP.Valid
  refine and_congr Iff.rfl (forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl ?_)
  show ¬ ((slab c m k P A M).conf x y (f x) (f y) ∧ _) ↔ _
  simp [relaxV]

theorem slabR_irrefl : (slabR c m k P A M R).Irrefl := slab_irrefl (k := k) (P := P) (A := A) (N := M)

theorem slabR_match (hK : KeyInj k A M) : (slabR c m k P A M R).Match := by
  intro x y b hb a a' ha ha' h h'
  exact slab_match (c := c) (P := P) hK x y b hb a a' ha ha'
    (h.imp (fun h => h.1) (fun h => h.1)) (h'.imp (fun h => h.1) (fun h => h.1))

/-! ### Relaxing one more label -/

/-- `R` with the label `ℓ` added at row `v`. -/
def Radd (R : Fin m → Finset ℕ) (v : Fin m) (ℓ : ℕ) : Fin m → Finset ℕ :=
  fun v' => if v' = v then insert ℓ (R v) else R v'

/-- Both cells of the edge below row `v` carry `ℓ`. -/
def HitV (hc : 1 ≤ c) {v : Fin m} (h : v.val + 1 < m) (ℓ : ℕ) (f : Cell c m → ℕ) : Prop :=
  f (fut0 hc, v) = ℓ ∧ f (fut0 hc, ⟨v.val + 1, h⟩) = ℓ

theorem relaxV_mono {R : Fin m → Finset ℕ} {v : Fin m} {ℓ : ℕ} {x y : Cell c m} {a : ℕ}
    (h : relaxV R x y a) : relaxV (Radd R v ℓ) x y a := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  simp only [Radd]
  rcases h3 with ⟨e, ha⟩ | ⟨e, ha⟩
  · left; refine ⟨e, ?_⟩; split_ifs with hv
    · subst hv; exact mem_insert_of_mem ha
    · exact ha
  · right; refine ⟨e, ?_⟩; split_ifs with hv
    · subst hv; exact mem_insert_of_mem ha
    · exact ha

/-- **The relaxation identity.** -/
theorem card_relax (hc : 1 ≤ c) {v : Fin m} (h : v.val + 1 < m) {ℓ : ℕ} (hℓ : ℓ ∉ R v) :
    (slabR c m k P A M (Radd R v ℓ)).Ω.card =
      (slabR c m k P A M R).Ω.card +
        ((slabR c m k P A M (Radd R v ℓ)).Ω.filter (HitV hc h ℓ)).card := by
  set Ω₁ := (slabR c m k P A M (Radd R v ℓ)).Ω
  set Ω₀ := (slabR c m k P A M R).Ω
  have hsub : Ω₀ ⊆ Ω₁ := by
    intro f hf
    rw [CSP.mem_Ω] at hf ⊢
    exact ⟨hf.1, fun x y hxy hc' => hf.2 x y hxy ⟨hc'.1, fun hh => hc'.2 ⟨hh.1, relaxV_mono hh.2⟩⟩⟩
  have hx2 : (fut0 hc : Fin (c + 2)).val = 2 := rfl
  have hdiff : Ω₁ \ Ω₀ = Ω₁.filter (HitV hc h ℓ) := by
    ext f
    rw [mem_sdiff, mem_filter]
    constructor
    · rintro ⟨h1, h0⟩
      refine ⟨h1, ?_⟩
      rw [CSP.mem_Ω] at h1 h0
      have hD := h1.1
      by_contra hn
      apply h0
      refine ⟨hD, fun x y hxy hcf => ?_⟩
      have h1' := h1.2 x y hxy
      -- the conflict is undone only by the new relaxation
      have hR' : f x = f y ∧ relaxV (Radd R v ℓ) x y (f x) := by
        by_contra hne; exact h1' ⟨hcf.1, hne⟩
      have hR : ¬ relaxV R x y (f x) := fun hr => hcf.2 ⟨hR'.1, hr⟩
      obtain ⟨hx, hy, hr⟩ := hR'.2
      apply hn
      simp only [Radd] at hr
      rcases hr with ⟨e, hm⟩ | ⟨e, hm⟩
      · split_ifs at hm with hv
        · subst hv
          rcases mem_insert.mp hm with hm | hm
          · refine ⟨?_, ?_⟩
            · rw [← hm]; congr 1; exact cell_eq (by rw [hx]; rfl) rfl
            · rw [← hm, hR'.1]; congr 1; exact cell_eq (by rw [hy]; rfl) (by simp; omega)
          · exact absurd ⟨hx, hy, Or.inl ⟨e, hm⟩⟩ hR
        · exact absurd ⟨hx, hy, Or.inl ⟨e, hm⟩⟩ hR
      · split_ifs at hm with hv
        · subst hv
          rcases mem_insert.mp hm with hm | hm
          · refine ⟨?_, ?_⟩
            · rw [← hm, hR'.1]; congr 1; exact cell_eq (by rw [hy]; rfl) rfl
            · rw [← hm]; congr 1; exact cell_eq (by rw [hx]; rfl) (by simp; omega)
          · exact absurd ⟨hx, hy, Or.inr ⟨e, hm⟩⟩ hR
        · exact absurd ⟨hx, hy, Or.inr ⟨e, hm⟩⟩ hR
    · rintro ⟨h1, hhit⟩
      refine ⟨h1, fun h0 => ?_⟩
      rw [CSP.mem_Ω] at h0
      have hadj : slabAdj (fut0 hc, v) ((fut0 hc, ⟨v.val + 1, h⟩) : Cell c m) :=
        Or.inl ⟨rfl, Or.inl rfl⟩
      apply h0.2 _ _ hadj
      refine ⟨?_, ?_⟩
      · rw [slab_conf_eq (by rw [hx2]; omega) (by rw [hx2]; omega), hhit.1, hhit.2]
      · rintro ⟨-, -, -, hr⟩
        rcases hr with ⟨-, hm⟩ | ⟨e, -⟩
        · rw [hhit.1] at hm; exact hℓ hm
        · simp at e; omega
  rw [← hdiff, card_sdiff_of_subset hsub, Nat.add_sub_cancel' (card_le_card hsub)]

/-! ### Counting the relaxed slab -/

/-- The relaxed first future column: labels below `k`, adjacent rows equal only on relaxed labels. -/
noncomputable def statesR (k : ℕ) (R : Fin m → Finset ℕ) : Finset (State (Fin m)) :=
  (Fintype.piFinset fun _ : Fin m => range k).filter
    (fun u => ∀ v v' : Fin m, v.val + 1 = v'.val → u v = u v' → u v ∈ R v)

theorem mem_statesR {u : State (Fin m)} :
    u ∈ statesR k R ↔ (∀ v, u v < k) ∧
      ∀ v v' : Fin m, v.val + 1 = v'.val → u v = u v' → u v ∈ R v := by
  unfold statesR; simp [Fintype.mem_piFinset]

/-- Valid futures after a seam state `q`, the first column relaxed. -/
def FutValidR (k : ℕ) (R : Fin m → Finset ℕ) (q : State (Fin m)) (ψ : Fin c → State (Fin m)) :
    Prop :=
  (∀ t : Fin c, t.val ≠ 0 → ψ t ∈ states (rowG m) (unif k)) ∧
    (∀ t : Fin c, t.val = 0 → ψ t ∈ statesR k R) ∧ (∀ t : Fin c, t.val = 0 → Compat q (ψ t)) ∧
      ∀ t t' : Fin c, t.val + 1 = t'.val → Compat (ψ t) (ψ t')

theorem slabR_conf_off {x y : Cell c m} (hx : ¬ (x.1.val = 2 ∧ y.1.val = 2)) {a b : ℕ} :
    (slabR c m k P A M R).conf x y a b ↔ (slab c m k P A M).conf x y a b := by
  rw [slabR_conf]
  exact ⟨fun h => h.1, fun h => ⟨h, fun h' => hx ⟨h'.2.1, h'.2.2.1⟩⟩⟩

theorem slabR_conf_two {x y : Cell c m} (hx : x.1.val = 2) (hy : y.1.val = 2) {a b : ℕ} :
    (slabR c m k P A M R).conf x y a b ↔ a = b ∧ ¬ relaxV R x y a := by
  rw [slabR_conf, slab_conf_eq (by omega) (by omega)]
  exact ⟨fun h => ⟨h.1, fun hr => h.2 ⟨h.1, hr⟩⟩, fun h => ⟨h.1, fun h' => h.2 h'.2⟩⟩

/-- **Relaxed-slab validity, column by column.** -/
theorem valid_iff_R (f : Cell c m → ℕ) :
    (slabR c m k P A M R).Valid f ↔
      colOf f 0 ∈ states (rowG m) P ∧ colOf f 1 ∈ states (rowG m) A ∧
        Compat (colOf f 0) (colOf f 1) ∧ FutValidR k R (keyed M (colOf f 1)) (futOf f) := by
  have hD : ∀ x, (slabR c m k P A M R).D x = (slab c m k P A M).D x := fun _ => rfl
  -- edges off the first future column's verticals behave as in the slab
  have hoff : ∀ x y : Cell c m, slabAdj x y → ¬ (x.1.val = 2 ∧ y.1.val = 2) →
      ((slabR c m k P A M R).conf x y (f x) (f y) ↔ (slab c m k P A M).conf x y (f x) (f y)) :=
    fun x y _ h => slabR_conf_off h
  have e2 : ∀ (i : Fin (c + 2)) (hi : 2 ≤ i.val) (w : Fin m),
      futOf f ⟨i.val - 2, by omega⟩ w = f (i, w) := by
    intro i hi w; simp only [futOf]; congr 2; ext; simp; omega
  constructor
  · rintro ⟨hDf, hC⟩
    have hvert : ∀ (j : Fin (c + 2)), j.val ≠ 2 → ∀ (u v : Fin m), (rowG m).Adj u v →
        f (j, u) ≠ f (j, v) := by
      intro j hj u v huv
      have := hC _ _ (show slabAdj (j, u) (j, v) from Or.inl ⟨rfl, huv⟩)
      rwa [slabR_conf_off (by simp; omega), slab_conf_eq (show ¬ (j.val = 1 ∧ j.val = 2) by omega)
        (show ¬ (j.val = 2 ∧ j.val = 1) by omega)] at this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_states]
      refine ⟨fun v => ?_, fun u v huv => hvert 0 (by simp) u v huv⟩
      have := hDf (0, v); rwa [hD, slab_D_zero (show (0 : Fin (c + 2)).val = 0 from rfl)] at this
    · rw [mem_states]
      refine ⟨fun v => ?_, fun u v huv => hvert 1 (by simp) u v huv⟩
      have := hDf (1, v)
      rwa [hD, slab_D_one (x := ((1 : Fin (c + 2)), v)) (Fin.val_one _)] at this
    · intro v
      have hadj : slabAdj ((0 : Fin (c + 2)), v) (1, v) :=
        Or.inr ⟨rfl, Or.inl (show (0 : Fin (c + 2)).val + 1 = (1 : Fin (c + 2)).val by
          rw [Fin.val_one]; rfl)⟩
      have := hC _ _ hadj
      rwa [hoff _ _ hadj (by simp), slab_conf_eq (show ¬ ((0 : Fin (c + 2)).val = 1 ∧
        (1 : Fin (c + 2)).val = 2) by simp) (show ¬ ((0 : Fin (c + 2)).val = 2 ∧
          (1 : Fin (c + 2)).val = 1) by simp)] at this
    · intro t ht
      rw [mem_states]
      refine ⟨fun v => ?_, fun u v huv => hvert _ (by simp; omega) u v huv⟩
      have := hDf (⟨t.val + 2, by omega⟩, v)
      rwa [hD, slab_D_fut (show 2 ≤ t.val + 2 by omega)] at this
    · intro t ht
      rw [mem_statesR]
      refine ⟨fun v => ?_, fun v v' hvv e => ?_⟩
      · have := hDf (⟨t.val + 2, by omega⟩, v)
        rw [hD, slab_D_fut (show 2 ≤ t.val + 2 by omega), mem_range] at this
        exact this
      · have hadj : slabAdj ((⟨t.val + 2, by omega⟩ : Fin (c + 2)), v) (⟨t.val + 2, by omega⟩, v') :=
          Or.inl ⟨rfl, Or.inl hvv⟩
        have := hC _ _ hadj
        rw [slabR_conf_two (by simp; omega) (by simp; omega)] at this
        by_contra hn
        refine this ⟨e, fun hr => hn ?_⟩
        obtain ⟨-, -, hr⟩ := hr
        rcases hr with ⟨-, hm⟩ | ⟨e', -⟩
        · exact hm
        · simp at e'; omega
    · intro t ht v
      have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
      have hadj : slabAdj ((1 : Fin (c + 2)), v) (⟨t.val + 2, by omega⟩, v) :=
        Or.inr ⟨rfl, Or.inl (show (1 : Fin (c + 2)).val + 1 = t.val + 2 by omega)⟩
      have := hC _ _ hadj
      rw [hoff _ _ hadj (by simp), slab_conf_seam h1 (show t.val + 2 = 2 by omega)] at this
      exact this
    · intro t t' htt v
      have hadj : slabAdj ((⟨t.val + 2, by omega⟩ : Fin (c + 2)), v) (⟨t'.val + 2, by omega⟩, v) :=
        Or.inr ⟨rfl, Or.inl (show t.val + 2 + 1 = t'.val + 2 by omega)⟩
      have := hC _ _ hadj
      rwa [hoff _ _ hadj (by simp; omega), slab_conf_eq (show ¬ (t.val + 2 = 1 ∧ t'.val + 2 = 2) by
        omega) (show ¬ (t.val + 2 = 2 ∧ t'.val + 2 = 1) by omega)] at this
  · rintro ⟨h0, h1, h01, hψ1, hψ0, hseam, hcons⟩
    rw [mem_states] at h0 h1
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · obtain ⟨j, v⟩ := x
      rw [hD]
      by_cases hj0 : j.val = 0
      · rw [slab_D_zero hj0]
        have : j = 0 := Fin.ext hj0
        subst this; exact h0.1 v
      by_cases hj1 : j.val = 1
      · rw [slab_D_one hj1]
        have : j = 1 := Fin.ext (by rw [Fin.val_one]; exact hj1)
        subst this; exact h1.1 v
      · rw [slab_D_fut (show 2 ≤ j.val by omega), mem_range, ← e2 j (by omega) v]
        by_cases hj2 : j.val = 2
        · exact (mem_statesR.mp (hψ0 ⟨j.val - 2, by omega⟩ (by simp; omega))).1 v
        · have := ((mem_states (rowG m)).mp (hψ1 ⟨j.val - 2, by omega⟩ (by simp; omega))).1 v
          simpa [unif] using this
    · obtain ⟨j, v⟩ := x
      obtain ⟨j', v'⟩ := y
      rcases hxy with ⟨hjj, hvv⟩ | ⟨hvv, hjj⟩
      · -- vertical edge
        simp only at hjj hvv
        subst hjj
        by_cases hj2 : j.val = 2
        · rw [slabR_conf_two hj2 hj2]
          rintro ⟨e, hn⟩
          apply hn
          have hst := mem_statesR.mp (hψ0 ⟨j.val - 2, by omega⟩ (by simp; omega))
          rcases hvv with hvv | hvv
          · have := hst.2 v v' hvv (by rw [e2 j (by omega), e2 j (by omega)]; exact e)
            rw [e2 j (by omega)] at this
            exact ⟨hj2, hj2, Or.inl ⟨hvv, this⟩⟩
          · have := hst.2 v' v hvv (by rw [e2 j (by omega), e2 j (by omega)]; exact e.symm)
            rw [e2 j (by omega), ← e] at this
            exact ⟨hj2, hj2, Or.inr ⟨hvv, this⟩⟩
        rw [slabR_conf_off (by simp; omega), slab_conf_eq (show ¬ (j.val = 1 ∧ j.val = 2) by omega)
          (show ¬ (j.val = 2 ∧ j.val = 1) by omega)]
        by_cases hj0 : j.val = 0
        · have : j = 0 := Fin.ext hj0
          subst this; exact h0.2 hvv
        by_cases hj1 : j.val = 1
        · have : j = 1 := Fin.ext (by rw [Fin.val_one]; exact hj1)
          subst this; exact h1.2 hvv
        · have := ((mem_states (rowG m)).mp (hψ1 ⟨j.val - 2, by omega⟩ (by simp; omega))).2 hvv
          rwa [e2 j (by omega), e2 j (by omega)] at this
      · -- horizontal edge
        simp only at hjj hvv
        subst hvv
        rw [slabR_conf_off (show ¬ (j.val = 2 ∧ j'.val = 2) by omega)]
        rcases hjj with hjj | hjj
        · by_cases hj0 : j.val = 0
          · rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j'.val = 2) by omega)
              (show ¬ (j.val = 2 ∧ j'.val = 1) by omega)]
            have e0 : j = 0 := Fin.ext hj0
            have e1 : j' = 1 := Fin.ext (by rw [Fin.val_one]; omega)
            subst e0; subst e1; exact h01 v
          by_cases hj1 : j.val = 1
          · rw [slab_conf_seam (show j.val = 1 from hj1) (show j'.val = 2 by omega)]
            have e1 : j = 1 := Fin.ext (by rw [Fin.val_one]; exact hj1)
            subst e1
            have := hseam ⟨0, by omega⟩ rfl v
            rw [show (⟨0, by omega⟩ : Fin c) = ⟨j'.val - 2, by omega⟩ from Fin.ext (by simp; omega),
              e2 j' (by omega)] at this
            exact this
          · rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j'.val = 2) by omega)
              (show ¬ (j.val = 2 ∧ j'.val = 1) by omega)]
            have := hcons ⟨j.val - 2, by omega⟩ ⟨j'.val - 2, by omega⟩
              (show j.val - 2 + 1 = j'.val - 2 by omega) v
            rwa [e2 j (by omega), e2 j' (by omega)] at this
        · by_cases hj0 : j'.val = 0
          · rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j'.val = 2) by omega)
              (show ¬ (j.val = 2 ∧ j'.val = 1) by omega)]
            have e0 : j' = 0 := Fin.ext hj0
            have e1 : j = 1 := Fin.ext (by rw [Fin.val_one]; omega)
            subst e0; subst e1; exact fun h => h01 v h.symm
          by_cases hj1 : j'.val = 1
          · rw [slab_conf_seam' (show j.val = 2 by omega) (show j'.val = 1 from hj1)]
            have e1 : j' = 1 := Fin.ext (by rw [Fin.val_one]; exact hj1)
            subst e1
            have := hseam ⟨0, by omega⟩ rfl v
            rw [show (⟨0, by omega⟩ : Fin c) = ⟨j.val - 2, by omega⟩ from Fin.ext (by simp; omega),
              e2 j (by omega)] at this
            exact fun h => this h.symm
          · rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j'.val = 2) by omega)
              (show ¬ (j.val = 2 ∧ j'.val = 1) by omega)]
            have := hcons ⟨j'.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩
              (show j'.val - 2 + 1 = j.val - 2 by omega) v
            rw [e2 j' (by omega), e2 j (by omega)] at this
            exact fun h => this h.symm

/-- All label columns below `k`. -/
noncomputable def labCols (k m : ℕ) : Finset (State (Fin m)) :=
  Fintype.piFinset fun _ : Fin m => range k

theorem mem_labCols_of_states {u : State (Fin m)} (h : u ∈ states (rowG m) (unif k)) :
    u ∈ labCols k m := by
  rw [labCols, Fintype.mem_piFinset]
  intro v; simpa [unif] using ((mem_states (rowG m)).mp h).1 v

theorem mem_labCols_of_statesR {u : State (Fin m)} (h : u ∈ statesR k R) : u ∈ labCols k m := by
  rw [labCols, Fintype.mem_piFinset]
  intro v; exact mem_range.mpr ((mem_statesR.mp h).1 v)

/-- The valid relaxed futures. -/
noncomputable def futsR (c k : ℕ) (R : Fin m → Finset ℕ) (q : State (Fin m)) :
    Finset (Fin c → State (Fin m)) :=
  (Fintype.piFinset fun _ : Fin c => labCols k m).filter (FutValidR k R q)

theorem mem_futsR {q : State (Fin m)} {ψ : Fin c → State (Fin m)} :
    ψ ∈ futsR c k R q ↔ FutValidR k R q ψ := by
  unfold futsR
  rw [mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun t => ?_, h⟩⟩
  by_cases ht : t.val = 0
  · exact mem_labCols_of_statesR (h.2.1 t ht)
  · exact mem_labCols_of_states (h.1 t ht)

/-- **The relaxed futures count.** -/
theorem card_futsR (c : ℕ) (q : State (Fin m)) :
    (futsR (c + 1) k R q).card = ∑ u ∈ (statesR k R).filter (Compat q), F (rowG m) k c u := by
  rw [← sum_congr rfl fun u _ => card_futs (m := m) k c u]
  rw [card_eq_sum_card_fiberwise (f := fun ψ : Fin (c + 1) → State (Fin m) => ψ 0)
    (t := (statesR k R).filter (Compat q))]
  · refine sum_congr rfl fun u hu => ?_
    rw [mem_filter] at hu
    refine card_bij (fun ψ _ => Fin.tail ψ) ?_ ?_ ?_
    · intro ψ hψ
      rw [mem_filter, mem_futsR] at hψ
      rw [mem_futs]
      refine ⟨fun s => hψ.1.1 s.succ (by simp), fun s hs => ?_, fun s s' hss => ?_⟩
      · have := hψ.1.2.2.2 0 s.succ (by simp [hs])
        rw [hψ.2] at this
        exact this
      · exact hψ.1.2.2.2 s.succ s'.succ (by simp [hss])
    · intro ψ hψ ψ' hψ' he
      rw [mem_filter] at hψ hψ'
      funext s
      refine Fin.cases ?_ (fun s => ?_) s
      · rw [hψ.2, hψ'.2]
      · exact congrFun he s
    · intro χ hχ
      rw [mem_futs] at hχ
      refine ⟨Fin.cons u χ, ?_, by simp⟩
      rw [mem_filter, mem_futsR]
      refine ⟨⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s s' hss => ?_⟩, by simp⟩
      · obtain ⟨σ, rfl⟩ : ∃ σ : Fin c, s = σ.succ := ⟨⟨s.val - 1, by omega⟩, by ext; simp; omega⟩
        simpa using hχ.1 σ
      · have : s = 0 := Fin.ext hs
        subst this; simpa using hu.1
      · have : s = 0 := Fin.ext hs
        subst this; simpa using hu.2
      · obtain ⟨σ', rfl⟩ : ∃ σ' : Fin c, s' = σ'.succ :=
          ⟨⟨s'.val - 1, by omega⟩, by ext; simp; omega⟩
        by_cases h0 : s.val = 0
        · have : s = 0 := Fin.ext h0
          subst this
          simpa using hχ.2.1 σ' (by simp at hss; omega)
        · obtain ⟨σ, rfl⟩ : ∃ σ : Fin c, s = σ.succ :=
            ⟨⟨s.val - 1, by omega⟩, by ext; simp; omega⟩
          simpa using hχ.2.2 σ σ' (by simp at hss; omega)
  · intro ψ hψ
    rw [Finset.mem_coe, mem_futsR] at hψ
    rw [Finset.mem_coe, mem_filter]
    exact ⟨hψ.2.1 0 rfl, hψ.2.2.1 0 rfl⟩

/-- **The relaxed slab count.** -/
theorem card_Ω_R :
    (slabR (c + 1) m k P A M R).Ω.card = ∑ p ∈ states (rowG m) P,
      ∑ s ∈ (states (rowG m) A).filter (Compat p),
        ∑ u ∈ (statesR k R).filter (Compat (keyed M s)), F (rowG m) k c u := by
  set T := (states (rowG m) P ×ˢ states (rowG m) A).filter
    (fun ps : State (Fin m) × State (Fin m) => Compat ps.1 ps.2)
  rw [card_eq_sum_card_fiberwise (f := fun f => (colOf f 0, colOf f 1)) (t := T)]
  · rw [Finset.sum_filter, Finset.sum_product]
    refine sum_congr rfl fun p _ => ?_
    rw [Finset.sum_filter]
    refine sum_congr rfl fun s _ => ?_
    split_ifs with hps
    · rw [← card_futsR]
      refine card_bij (fun f _ => futOf f) ?_ ?_ ?_
      · intro f hf
        rw [mem_filter, CSP.mem_Ω, valid_iff_R] at hf
        obtain ⟨⟨_, _, _, hψ⟩, he⟩ := hf
        simp only [Prod.mk.injEq] at he
        rw [mem_futsR, ← he.2]; exact hψ
      · intro f hf f' hf' hff
        rw [mem_filter] at hf hf'
        simp only [Prod.mk.injEq] at hf hf'
        rw [← glue_cols f, ← glue_cols f', hf.2.1, hf.2.2, hf'.2.1, hf'.2.2, hff]
      · intro ψ hψ
        refine ⟨glue p s ψ, ?_, futOf_glue _ _ _⟩
        rw [mem_filter, CSP.mem_Ω, valid_iff_R, colOf_glue_zero, colOf_glue_one, futOf_glue]
        rw [mem_futsR] at hψ
        refine ⟨⟨by assumption, by assumption, hps, hψ⟩, rfl⟩
    · rfl
  · intro f hf
    rw [Finset.mem_coe, CSP.mem_Ω, valid_iff_R] at hf
    rw [Finset.mem_coe, mem_filter, mem_product]
    exact ⟨⟨hf.1, hf.2.1⟩, hf.2.2.1⟩

end GridGen.Gauge
