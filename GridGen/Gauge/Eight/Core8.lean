/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Eight.Seam8

/-!
# The slab inequality at `k ≥ 8`

Passing from the old column's gauge `β` to the new column's gauge `β' = glueLabH (tilde β)`:

1. the star phase: `H` stars, each gaining `γ`;
2. the moves through holes: `T ≤ H + D_A` transpositions, each losing at most `ε`. Here `D_A` is
   the vertical difference of the old column (`length_rhoH_le`);
3. the relaxation of the new column's vertical diagonals that are not labels of shared colours,
   `D_B` of them, each gaining `γ_V`.

The constants are those of a `Bounds8 k` (`Seam8.lean`). With `ε ≤ γ` the stars pay for `H` of
the moves, and the slab inequality is `(1 - ε)^{D_A} Z(old) ≤ (1 - γ_V)^{D_B} Z_R(new)`
(`slab_core8`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ}

/-! ### The star phase -/

/-- **The star phase.** -/
theorem star_phase8 (Bd : Bounds8 k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k)
    {B : Fin m → Finset ℕ}
    (β : ℕ → ℕ → ℕ) (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < k)
    (hP : ∀ v a, a ∈ A v → k - 1 ≤ (P v).card ∨ a ∉ P v) :
    ∀ T : Finset (Fin m × ℕ), T ⊆ stars A B →
      (Z c m k P A (fun v a => β v.val a) : ℚ) ≤
        (1 - Bd.γ) ^ T.card * Z c m k P A (starKeys k β T) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simp only [card_empty, pow_zero, one_mul, Nat.cast_le]
      exact le_of_eq (congrArg _ (by funext v a; simp [starKeys]))
  | insert p T hp ih =>
      intro hsub
      have hpS := hsub (mem_insert_self p T)
      rw [mem_stars] at hpS
      have h1 := ih (fun q hq => hsub (mem_insert_of_mem hq))
      have hK : KeyInj k A (starKeys k β T) := by
        intro v a a' ha ha' e hlt
        unfold starKeys at e hlt
        split_ifs at e hlt with h1 h2 h2 <;> try omega
        exact (hβ v).1 ha ha' e
      have hx : starKeys k β T p.1 p.2 < k := by
        unfold starKeys; rw [ite_eq_right (by simpa using hp)]; exact (hβ p.1).2 _ hpS.1
      have hstep := Bd.star (P := P) hc hA hK p.1 hpS.1 hx (hP p.1 p.2 hpS.1)
      have e : unpair k (starKeys k β T) p.1 p.2 = starKeys k β (insert p T) := by
        funext v a
        unfold unpair starKeys
        by_cases h : v = p.1 ∧ a = p.2
        · rw [ite_eq_left h, ite_eq_left]; rw [h.1, h.2]; exact mem_insert_self _ _
        · rw [ite_eq_right h]
          have hne : (v, a) ≠ p := fun e' => h ⟨congrArg Prod.fst e', congrArg Prod.snd e'⟩
          simp only [mem_insert, hne, false_or]
      rw [e] at hstep
      have hγ : 0 ≤ 1 - Bd.γ := by linarith [Bd.hγ1]
      rw [card_insert_of_notMem hp, pow_succ]
      calc (Z c m k P A (fun v a => β v.val a) : ℚ)
          ≤ (1 - Bd.γ) ^ T.card * Z c m k P A (starKeys k β T) := h1
        _ ≤ (1 - Bd.γ) ^ T.card * ((1 - Bd.γ) * Z c m k P A (starKeys k β (insert p T))) :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg hγ _)
        _ = _ := by ring

/-! ### The moves through holes -/

/-- **The moves of one edge, through holes.** -/
theorem applyEdgeH_step (Bd : Bounds8 k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k) (e : ℕ)
    {K : Fin m → ℕ → ℕ}
    {T Bp : ℕ → Prop}
    (hT : ∀ x, x < k → ¬ T x → ∀ h : e < m, ∀ a ∈ A ⟨e, h⟩, K ⟨e, h⟩ a ≠ x)
    (hB : ∀ h : e + 1 < m, ∀ a ∈ A ⟨e + 1, h⟩, K ⟨e + 1, h⟩ a < k → Bp (K ⟨e + 1, h⟩ a)) :
    ∀ ts : List (ℕ × ℕ), Small k ts → HoleOK T Bp ts → KeyInj k A K →
      (1 - Bd.ε) ^ ts.length * Z c m k P A K ≤ Z c m k P A (applyEdge e ts K) ∧
        KeyInj k A (applyEdge e ts K) := by
  intro ts
  induction ts with
  | nil => intro _ _ hK; simp [applyEdge, hK]
  | cons p ts ih =>
      intro hs hok hK
      have hp := hs p (by simp)
      obtain ⟨h1, h2⟩ := ih (fun q hq => hs q (by simp [hq])) hok.2 hK
      have e' : applyEdge e (p :: ts) K = moveKey (applyEdge e ts K) e p.1 p.2 := rfl
      rw [e']
      refine ⟨?_, keyInj_moveKey h2 e hp.1 hp.2⟩
      -- the hole of this move
      have hsm : Small k ts := fun q hq => hs q (by simp [hq])
      have hrow : ∀ (u : Fin m) (a : ℕ), applyEdge e ts K u a =
          if e < u.val then comp ts (K u a) else K u a := by
        intro u a; rw [applyEdge_eq]
      have hh : HoleAt A (applyEdge e ts K) e p.1 p.2 := by
        intro hm
        have hbot : ∀ x, x < k → (∀ z, Bp z → comp ts z ≠ x) →
            ∀ a ∈ A ⟨e + 1, hm⟩, applyEdge e ts K ⟨e + 1, hm⟩ a ≠ x := by
          intro x hx hz a ha
          rw [hrow, ite_eq_left (by simp)]
          by_cases hk : K ⟨e + 1, hm⟩ a < k
          · exact hz _ (hB hm a ha hk)
          · rw [comp_of_ge hsm (by omega)]; omega
        have htop : ∀ x, x < k → ¬ T x → ∀ a ∈ A ⟨e, by omega⟩, applyEdge e ts K ⟨e, by omega⟩ a ≠ x := by
          intro x hx hn a ha
          rw [hrow, ite_eq_right (by simp)]
          exact hT x hx hn (by omega) a ha
        rcases hok.1 with (h | h) | h | h
        · exact Or.inl (htop _ hp.1 h)
        · exact Or.inr (Or.inl (htop _ hp.2 h))
        · exact Or.inr (Or.inr (Or.inl (hbot _ hp.1 h)))
        · exact Or.inr (Or.inr (Or.inr (hbot _ hp.2 h)))
      have hm := Bd.move (P := P) hc hA h2 e hp.1 hp.2 hh
      have hε : 0 ≤ 1 - Bd.ε := by
        linarith [Bd.ε_lt_one]
      rw [List.length_cons, pow_succ]
      calc (1 - Bd.ε) ^ ts.length * (1 - Bd.ε) * (Z c m k P A K : ℚ)
          = (1 - Bd.ε) * ((1 - Bd.ε) ^ ts.length * Z c m k P A K) := by ring
        _ ≤ (1 - Bd.ε) * Z c m k P A (applyEdge e ts K) := mul_le_mul_of_nonneg_left h1 hε
        _ ≤ _ := hm

/-- The old column's labelling has its mismatches at new colours. -/
theorem newMis_tilde {A B : Fin m → Finset ℕ} {β : ℕ → ℕ → ℕ}
    (hvc : ∀ v, ∀ c ∈ extR A v ∩ extR A (v + 1), β (v + 1) c = β v c) :
    NewMis (extR A) (extR B) (tilde (extR A) (extR B) β) := by
  intro v c _ hne
  by_contra h
  push Not at h
  apply hne
  unfold tilde
  rw [ite_eq_left h.1, ite_eq_left h.2]
  exact hvc v c (mem_inter.mpr h)

/-- **All the moves, through holes.** -/
theorem applyAllH_step8 (Bd : Bounds8 k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k)
    {B : Fin m → Finset ℕ}
    (hB : ∀ v, (B v).card = k) (β : ℕ → ℕ → ℕ)
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < k)
    (hvc : ∀ v, ∀ c ∈ extR A v ∩ extR A (v + 1), β (v + 1) c = β v c) :
    ∀ e, (1 - Bd.ε) ^ (∑ i ∈ range e, (rhoH k (extR A) (extR B) (tilde (extR A) (extR B) β) i
        (piLH k (extR A) (extR B) (tilde (extR A) (extR B) β) i)).length) *
          Z c m k P A (starKeys k β (stars A B)) ≤
        Z c m k P A (applyAllH (k := k) (Ax := extR A) (Bx := extR B)
          (βx := tilde (extR A) (extR B) β) e (starKeys k β (stars A B))) ∧
      KeyInj k A (applyAllH (k := k) (Ax := extR A) (Bx := extR B)
          (βx := tilde (extR A) (extR B) β) e (starKeys k β (stars A B))) := by
  set Ax := extR A
  set Bx := extR B
  set βx := tilde Ax Bx β
  set M0 := starKeys k β (stars A B)
  have hcard : ∀ v, (Ax v).card = (Bx v).card := by
    intro v; simp only [Ax, Bx, extR]; split_ifs with h
    · rw [hA, hB]
    · rfl
  have hβx : ∀ v, Set.InjOn (β v) (Ax v) ∧ ∀ a ∈ Ax v, β v a < k := by
    intro v; simp only [Ax, extR]; split_ifs with h
    · exact hβ ⟨v, h⟩
    · simp
  have hR : RowLab k Bx βx := rowLab_tilde hcard hβx
  have hN : NewMis Ax Bx βx := newMis_tilde hvc
  have hK0 : KeyInj k A M0 := by
    intro v a a' ha ha' e hlt
    simp only [M0, starKeys] at e hlt
    split_ifs at e hlt with h1 h2 h2 <;> try omega
    exact (hβ v).1 ha ha' e
  -- the keys of a row, after the conjugation of the rows above
  have hkey : ∀ (u : Fin m) (a : ℕ), a ∈ A u → ∀ pl : List (ℕ × ℕ), Small k pl →
      (comp pl (M0 u a) < k → a ∈ Bx u.val ∩ Ax u.val ∧ comp pl (M0 u a) = comp pl (βx u.val a)) ∧
        (¬ a ∈ B u → comp pl (M0 u a) = k) := by
    intro u a ha pl hpl
    have hAx : a ∈ Ax u.val := by simp only [Ax]; rw [extR_val]; exact ha
    by_cases hb : a ∈ B u
    · have hst : (u, a) ∉ stars A B := by rw [mem_stars]; exact fun h => h.2 hb
      refine ⟨fun _ => ⟨mem_inter.mpr ⟨by simp only [Bx]; rw [extR_val]; exact hb, hAx⟩, ?_⟩,
        fun h => absurd hb h⟩
      simp only [M0, starKeys, βx, tilde]
      rw [ite_eq_right hst, ite_eq_left hAx]
    · have hst : (u, a) ∈ stars A B := by rw [mem_stars]; exact ⟨ha, hb⟩
      have e8 : comp pl (M0 u a) = k := by
        simp only [M0, starKeys]; rw [ite_eq_left hst]; exact comp_of_ge hpl le_rfl
      exact ⟨fun h => by omega, fun _ => e8⟩
  intro e
  induction e with
  | zero => simp [applyAllH, hK0]
  | succ e ih =>
      obtain ⟨h1, h2⟩ := ih
      set pl := piLH k Ax Bx βx e
      have hpl : Small k pl := small_piLH hR hN e
      obtain ⟨-, hsm, -, hok⟩ := rhoH_spec hR hN hpl e
      have hcur : ∀ (u : Fin m) (a : ℕ), (u.val = e ∨ u.val = e + 1) →
          applyAllH (k := k) (Ax := Ax) (Bx := Bx) (βx := βx) e M0 u a = comp pl (M0 u a) := by
        intro u a hu
        rw [applyAllH_eq, show min u.val e = e by omega]
      have hT : ∀ x, x < k → ¬ imgT Ax Bx βx e pl x → ∀ h : e < m, ∀ a ∈ A ⟨e, h⟩,
          applyAllH (k := k) (Ax := Ax) (Bx := Bx) (βx := βx) e M0 ⟨e, h⟩ a ≠ x := by
        intro x hx hn h a ha he
        rw [hcur _ _ (Or.inl rfl)] at he
        obtain ⟨hk1, -⟩ := hkey ⟨e, h⟩ a ha pl hpl
        obtain ⟨hab, he'⟩ := hk1 (by omega)
        exact hn ⟨a, hab, by rw [← he', he]⟩
      have hBp : ∀ h : e + 1 < m, ∀ a ∈ A ⟨e + 1, h⟩,
          applyAllH (k := k) (Ax := Ax) (Bx := Bx) (βx := βx) e M0 ⟨e + 1, h⟩ a < k →
            imgT Ax Bx βx (e + 1) pl
              (applyAllH (k := k) (Ax := Ax) (Bx := Bx) (βx := βx) e M0 ⟨e + 1, h⟩ a) := by
        intro h a ha hlt
        rw [hcur _ _ (Or.inr rfl)] at hlt ⊢
        obtain ⟨hk1, -⟩ := hkey ⟨e + 1, h⟩ a ha pl hpl
        obtain ⟨hab, he'⟩ := hk1 hlt
        exact ⟨a, hab, he'.symm⟩
      obtain ⟨h3, h4⟩ := applyEdgeH_step Bd (P := P) hc hA e hT hBp _ hsm hok h2
      refine ⟨?_, h4⟩
      have hε : 0 ≤ 1 - Bd.ε := by
        linarith [Bd.ε_lt_one]
      rw [sum_range_succ, pow_add]
      calc (1 - Bd.ε) ^ (∑ i ∈ range e, (rhoH k Ax Bx βx i (piLH k Ax Bx βx i)).length) *
            (1 - Bd.ε) ^ (rhoH k Ax Bx βx e pl).length * (Z c m k P A M0 : ℚ)
          = (1 - Bd.ε) ^ (rhoH k Ax Bx βx e pl).length *
              ((1 - Bd.ε) ^ (∑ i ∈ range e, (rhoH k Ax Bx βx i (piLH k Ax Bx βx i)).length) *
                Z c m k P A M0) := by ring
        _ ≤ (1 - Bd.ε) ^ (rhoH k Ax Bx βx e pl).length *
              Z c m k P A (applyAllH (k := k) (Ax := Ax) (Bx := Bx) (βx := βx) e M0) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg hε _)
        _ ≤ _ := h3

/-! ### The new gauge and the relaxed pairs -/

/-- The vertical difference of a column. -/
def Dcol (X : Fin m → Finset ℕ) : ℕ := ∑ v ∈ range m, (extR X (v + 1) \ extR X v).card

/-- The new column's gauge. -/
noncomputable def gaugeNew (k : ℕ) (A B : Fin m → Finset ℕ) (β : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ :=
  glueLabH k (extR A) (extR B) (tilde (extR A) (extR B) β)

/-- The new keys: the new gauge on staying colours, unpaired on leaving ones. -/
noncomputable def newKeys8 (k : ℕ) (A B : Fin m → Finset ℕ) (β : ℕ → ℕ → ℕ) : Fin m → ℕ → ℕ :=
  fun v a => if a ∈ B v then gaugeNew k A B β v.val a else k

/-- The relaxed pairs: the labels of row `v` that no shared colour of rows `v, v + 1` carries. -/
noncomputable def Trel (k : ℕ) (B : Fin m → Finset ℕ) (β' : ℕ → ℕ → ℕ) : Finset (Fin m × ℕ) :=
  (univ ×ˢ range k).filter (fun p => p.1.val + 1 < m ∧
    ∀ c ∈ extR B p.1.val ∩ extR B (p.1.val + 1), β' p.1.val c ≠ p.2)

theorem mem_Trel {B : Fin m → Finset ℕ} {β' : ℕ → ℕ → ℕ} {p : Fin m × ℕ} :
    p ∈ Trel k B β' ↔ p.2 < k ∧ p.1.val + 1 < m ∧
      ∀ c ∈ extR B p.1.val ∩ extR B (p.1.val + 1), β' p.1.val c ≠ p.2 := by
  unfold Trel; simp [mem_product]

/-- **Each vertical edge relaxes its new-column difference.** -/
theorem Dcol_le_card_Trel {B : Fin m → Finset ℕ} (hB : ∀ v, (B v).card = k) {β' : ℕ → ℕ → ℕ}
    (hR : RowLab k (extR B) β') : Dcol B ≤ (Trel k B β').card := by
  unfold Dcol
  rw [card_eq_sum_card_fiberwise (f := fun p : Fin m × ℕ => p.1) (t := univ)
    (fun _ _ => mem_univ _), ← Fin.sum_univ_eq_sum_range (fun v => (extR B (v + 1) \ extR B v).card)]
  refine sum_le_sum fun v _ => ?_
  by_cases hv : v.val + 1 < m
  · -- the labels of row `v` outside the image of the shared colours
    set S := extR B v.val ∩ extR B (v.val + 1)
    have himg : (S.image (β' v.val)).card = S.card :=
      card_image_of_injOn fun a ha a' ha' e => (hR v.val).1 (mem_inter.mp ha).1 (mem_inter.mp ha').1 e
    have hsub : S.image (β' v.val) ⊆ range k := fun z hz => by
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
      exact mem_range.mpr ((hR v.val).2 a (mem_inter.mp ha).1)
    have hfib : ((Trel k B β').filter (fun p => p.1 = v)) =
        ((range k \ S.image (β' v.val)).image fun ℓ => (v, ℓ)) := by
      ext ⟨u, ℓ⟩
      simp only [mem_filter, mem_Trel, mem_image, mem_sdiff, mem_range, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hℓ, -, hall⟩, rfl⟩
        exact ⟨ℓ, ⟨hℓ, fun ⟨a, ha, e⟩ => hall a ha e⟩, rfl, rfl⟩
      · rintro ⟨ℓ', ⟨hℓ, hn⟩, rfl, rfl⟩
        exact ⟨⟨hℓ, hv, fun a ha e => hn ⟨a, ha, e⟩⟩, rfl⟩
    rw [hfib, card_image_of_injective _ (fun a b h => by simpa using h), card_sdiff_of_subset hsub,
      card_range, himg]
    have e1 : extR B (v.val + 1) = B ⟨v.val + 1, hv⟩ := by simp [extR, hv]
    have e0 : extR B v.val = B v := extR_val B v
    have hS : S.card = (B v ∩ B ⟨v.val + 1, hv⟩).card := by
      show (extR B v.val ∩ extR B (v.val + 1)).card = _; rw [e0, e1]
    have h1 := card_sdiff_add_card_inter (B ⟨v.val + 1, hv⟩) (B v)
    rw [hB, inter_comm] at h1
    rw [e1, e0]
    omega
  · have : extR B (v.val + 1) = ∅ := extR_ge B (by omega)
    rw [this]; simp

/-! ### The slab inequality -/

/-- **The slab inequality at `k ≥ 8`.** -/
theorem slab_core8 (Bd : Bounds8 k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k)
    {B : Fin m → Finset ℕ}
    (hB : ∀ v, (B v).card = k) (β : ℕ → ℕ → ℕ)
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < k)
    (hvc : ∀ v, ∀ c ∈ extR A v ∩ extR A (v + 1), β (v + 1) c = β v c)
    (hP : ∀ v a, a ∈ A v → k - 1 ≤ (P v).card ∨ a ∉ P v) :
    (1 - Bd.ε) ^ Dcol A * (Z c m k P A (fun v a => β v.val a) : ℚ) ≤
      (1 - Bd.γV) ^ Dcol B *
        (slabR c m k P A (newKeys8 k A B β) (RT (Trel k B (gaugeNew k A B β)))).Ω.card := by
  set Ax := extR A
  set Bx := extR B
  set βx := tilde Ax Bx β
  set M0 := starKeys k β (stars A B)
  have hcard : ∀ v, (Ax v).card = (Bx v).card := by
    intro v; simp only [Ax, Bx, extR]; split_ifs with h
    · rw [hA, hB]
    · rfl
  have hβx : ∀ v, Set.InjOn (β v) (Ax v) ∧ ∀ a ∈ Ax v, β v a < k := by
    intro v; simp only [Ax, extR]; split_ifs with h
    · exact hβ ⟨v, h⟩
    · simp
  have hR : RowLab k Bx βx := rowLab_tilde hcard hβx
  have hN : NewMis Ax Bx βx := newMis_tilde hvc
  have hR' : RowLab k Bx (gaugeNew k A B β) := fun v =>
    ⟨glueLabH_injOn hR v, fun a ha => glueLabH_lt hR hN v ha⟩
  -- the star phase and the moves
  have h1 := star_phase8 Bd (P := P) hc hA (B := B) β hβ hP (stars A B) (Subset.refl _)
  obtain ⟨h2, -⟩ := applyAllH_step8 Bd (P := P) hc hA hB β hβ hvc m
  have hfin : Z c m k P A (applyAllH (k := k) (Ax := Ax) (Bx := Bx) (βx := βx) m M0) =
      Z c m k P A (newKeys8 k A B β) := by
    refine Z_congr fun v a ha => ?_
    rw [applyAllH_eq, show min v.val m = v.val by have := v.isLt; omega]
    simp only [M0, starKeys, mem_stars, newKeys8, gaugeNew]
    by_cases hb : a ∈ B v
    · rw [ite_eq_right (by simp [hb]), ite_eq_left hb]
      unfold glueLabH tilde
      rw [ite_eq_left (by rw [extR_val]; exact ha)]
      rfl
    · rw [ite_eq_left ⟨ha, hb⟩, ite_eq_right hb]
      exact comp_of_ge (small_piLH hR hN _) le_rfl
  rw [hfin] at h2
  -- counting the moves
  set H := (stars A B).card
  set T := ∑ i ∈ range m, (rhoH k Ax Bx βx i (piLH k Ax Bx βx i)).length
  have hT : T ≤ H + Dcol A := by
    have hsd : ∀ v : Fin m, (B v \ A v).card = (A v \ B v).card := by
      intro v
      have e1 := card_sdiff_add_card_inter (B v) (A v)
      have e2 := card_sdiff_add_card_inter (A v) (B v)
      rw [inter_comm, hA] at e2
      rw [hB] at e1
      omega
    have hsumB : ∑ i ∈ range m, (Bx i \ Ax i).card = H := by
      simp only [H]
      rw [card_stars, ← Fin.sum_univ_eq_sum_range (fun i => (Bx i \ Ax i).card)]
      refine sum_congr rfl fun v _ => ?_
      rw [show Bx v.val = B v from extR_val B v, show Ax v.val = A v from extR_val A v, hsd]
    have hshift : ∑ i ∈ range m, (Bx (i + 1) \ Ax (i + 1)).card ≤
        ∑ i ∈ range m, (Bx i \ Ax i).card := by
      have e1 := sum_range_succ' (fun i => (Bx i \ Ax i).card) m
      have e2 := sum_range_succ (fun i => (Bx i \ Ax i).card) m
      have hm : (Bx m \ Ax m).card = 0 := by simp [Bx, extR_ge B (le_refl m)]
      omega
    calc T ≤ ∑ i ∈ range m, ((Bx (i + 1) \ Ax (i + 1)).card + (Ax (i + 1) \ Ax i).card) :=
          sum_le_sum fun i _ => length_rhoH_le hR hN i
      _ = ∑ i ∈ range m, (Bx (i + 1) \ Ax (i + 1)).card + Dcol A := by
          rw [sum_add_distrib]; rfl
      _ ≤ H + Dcol A := by omega
  -- the relaxation
  have hKn : KeyInj k A (newKeys8 k A B β) := by
    intro v a a' ha ha' e hlt
    simp only [newKeys8] at e hlt
    split_ifs at e hlt with h1 h2 h2 <;> try omega
    have hb1 : a ∈ Bx v.val := by simp only [Bx]; rw [extR_val]; exact h1
    have hb2 : a' ∈ Bx v.val := by simp only [Bx]; rw [extR_val]; exact h2
    exact glueLabH_injOn hR v.val hb1 hb2 e
  have hrel := relax_all Bd (P := P) hc hA hKn (Trel k B (gaugeNew k A B β))
    (fun p hp => ⟨(mem_Trel.mp hp).2.1, (mem_Trel.mp hp).1⟩)
  rw [slabR_empty] at hrel
  have hDB := Dcol_le_card_Trel hB hR'
  have hγV : 0 ≤ 1 - Bd.γV ∧ 1 - Bd.γV ≤ 1 := ⟨by linarith [Bd.hV1], by linarith [Bd.γV_nonneg]⟩
  have hpowV : (1 - Bd.γV) ^ (Trel k B (gaugeNew k A B β)).card ≤ (1 - Bd.γV) ^ Dcol B :=
    pow_le_pow_of_le_one hγV.1 hγV.2 hDB
  -- the arithmetic
  have hεγ := Bd.hεγ
  have hε0 := Bd.hε0
  have hγ1 : Bd.γ < 1 := Bd.hγ1
  have hε1 : 0 < 1 - Bd.ε := by linarith
  have hZ0 : (0 : ℚ) ≤ Z c m k P A M0 := by positivity
  have hZo : (0 : ℚ) ≤ Z c m k P A (fun v a => β v.val a) := by positivity
  have hZR : (0 : ℚ) ≤ (slabR c m k P A (newKeys8 k A B β) (RT (Trel k B (gaugeNew k A B β)))).Ω.card := by
    positivity
  have hpowT : (1 - Bd.ε) ^ (H + Dcol A) ≤ (1 - Bd.ε) ^ T :=
    pow_le_pow_of_le_one hε1.le (by linarith) hT
  have hpowH : (1 - Bd.γ) ^ H ≤ (1 - Bd.ε) ^ H :=
    pow_le_pow_left₀ (by linarith) (by linarith) H
  have hHpos : 0 < (1 - Bd.ε) ^ H := pow_pos hε1 H
  have hmain : (1 - Bd.ε) ^ H * ((1 - Bd.ε) ^ Dcol A * Z c m k P A (fun v a => β v.val a)) ≤
      (1 - Bd.ε) ^ H * Z c m k P A (newKeys8 k A B β) := by
    calc (1 - Bd.ε) ^ H * ((1 - Bd.ε) ^ Dcol A * Z c m k P A (fun v a => β v.val a))
        = (1 - Bd.ε) ^ (H + Dcol A) * Z c m k P A (fun v a => β v.val a) := by ring
      _ ≤ (1 - Bd.ε) ^ T * Z c m k P A (fun v a => β v.val a) :=
          mul_le_mul_of_nonneg_right hpowT hZo
      _ ≤ (1 - Bd.ε) ^ T * ((1 - Bd.γ) ^ H * Z c m k P A M0) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg hε1.le _)
      _ = (1 - Bd.γ) ^ H * ((1 - Bd.ε) ^ T * Z c m k P A M0) := by ring
      _ ≤ (1 - Bd.γ) ^ H * Z c m k P A (newKeys8 k A B β) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _)
      _ ≤ (1 - Bd.ε) ^ H * Z c m k P A (newKeys8 k A B β) :=
          mul_le_mul_of_nonneg_right hpowH (by positivity)
  have hstep := le_of_mul_le_mul_left hmain hHpos
  calc (1 - Bd.ε) ^ Dcol A * (Z c m k P A (fun v a => β v.val a) : ℚ)
      ≤ Z c m k P A (newKeys8 k A B β) := hstep
    _ = (slab c m k P A (newKeys8 k A B β)).Ω.card := rfl
    _ ≤ (1 - Bd.γV) ^ (Trel k B (gaugeNew k A B β)).card *
          (slabR c m k P A (newKeys8 k A B β) (RT (Trel k B (gaugeNew k A B β)))).Ω.card := hrel
    _ ≤ _ := mul_le_mul_of_nonneg_right hpowV hZR

end GridGen.Gauge
