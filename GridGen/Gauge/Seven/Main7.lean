/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Gauge7
import GridGen.Gauge.Eight.Main8

/-!
# Every grid is `7`-ECC, given the seam bounds

The gauge telescope of `Eight/Main8.lean` at `k = 7`. Two things change:

* the new gauges are built by the lookahead process (`gaugeNew7`, `Order7.lean`);
* the potential is `Pot7 j = (1 - γ_V)^{D_j} W_j` with `γ_V = 27/5075`, the relaxation gain itself.
  At each seam a D-move (one per unit of the old column's vertical difference) may lose that
  factor, H-moves are paid by their stars, and a star serving two moves is pooled with the unit of
  its second move (`Seam7.lean`).

The seam inequality (`slab_core7`) needs the bounds `Bounds7` on every slab: the star gain, the
loss of a move through a hole (absorbed into the star's hit event, plus residual chains), and the
drift of a hit event (`K7Bounds`). Given them, `uniform ≤ (1 - γ_V)^{D_0} W_0 ≤ … ≤ W_n ≤ total`
(`ecc_rowG_boxProd_seven`).
-/

open Finset SimpleGraph ListColoring
open scoped Classical SimpleGraph

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {m : ℕ}

/-- **The seam bounds at `k = 7`**, for every slab, with the relaxation constant as the move
budget of a vertical-difference unit. -/
def K7Bounds : Prop :=
  ∀ (c m : ℕ) (P A : Fin m → Finset ℕ) (hc : 1 ≤ c), (∀ v, (A v).card = 7) →
    (∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) → ∃ Bnd : Bounds7 c m P A hc, Bnd.γV = gammaV7

/-! ### The gauges through holes -/

/-- The gauge of column `j`, the later columns glued through holes. -/
noncomputable def gaugeH7 (L : Cols (Fin m)) : ℕ → ℕ → ℕ → ℕ
  | 0 => gauge 7 L 0
  | j + 1 => gaugeNew7 (L j) (L (j + 1)) (gaugeH7 L j)

/-- **The gauges are row labellings and vertically consistent.** -/
theorem gaugeH7_props {L : Cols (Fin m)} (hL : IsKCols 7 L) : ∀ j,
    RowLab 7 (extR (L j)) (gaugeH7 L j) ∧
      ∀ v, ∀ c ∈ extR (L j) v ∩ extR (L j) (v + 1), gaugeH7 L j (v + 1) c = gaugeH7 L j v c := by
  intro j
  induction j with
  | zero => exact gauge_props hL 0
  | succ j ih =>
      have hβ : ∀ v : Fin m, Set.InjOn (gaugeH7 L j v.val) (L j v) ∧
          ∀ a ∈ L j v, gaugeH7 L j v.val a < 7 :=
        fun v => by have := ih.1 v.val; rw [extR_val] at this; exact this
      exact gaugeNew7_props (hL j) (hL (j + 1)) hβ

/-- The keys of column `j`'s gauge. -/
noncomputable def keysH7 (L : Cols (Fin m)) (j : ℕ) : Fin m → ℕ → ℕ :=
  fun v a => gaugeH7 L j v.val a

/-- The relaxed labels of column `j + 1`. -/
noncomputable def relH7 (L : Cols (Fin m)) (j : ℕ) : Fin m → Finset ℕ :=
  RT (Trel7 (L (j + 1)) (gaugeH7 L (j + 1)))

/-! ### Pulling relaxed states back -/

/-- **Pulling back relaxed states.** Under a VC labelling, every relaxed label state is the key
image of a list state. -/
theorem pullbackR7 {X : Fin m → Finset ℕ} (hX : ∀ v, (X v).card = 7) {g : ℕ → ℕ → ℕ}
    (hR : RowLab 7 (extR X) g)
    (hvc : ∀ v, ∀ c ∈ extR X v ∩ extR X (v + 1), g (v + 1) c = g v c)
    {u : State (Fin m)} (hu : u ∈ statesR 7 (RT (Trel7 X g))) :
    ∃ t ∈ states (rowG m) X, keyed (fun v a => g v.val a) t = u := by
  rw [mem_statesR] at hu
  choose t ht hgt using fun v => surj_of_rowLab hX hR v (hu.1 v)
  refine ⟨t, ?_, funext hgt⟩
  rw [mem_states]
  refine ⟨ht, fun v v' hvv' e => ?_⟩
  -- a shared colour of adjacent rows has equal labels, which a relaxed label never is
  have key : ∀ a b : Fin m, a.val + 1 = b.val → t a = t b → False := by
    intro a b hab hte
    have hc : t a ∈ extR X a.val ∩ extR X (a.val + 1) := by
      rw [mem_inter, extR_val, hab, extR_val]; exact ⟨ht a, hte ▸ ht b⟩
    have hlab : g (a.val + 1) (t a) = g a.val (t a) := hvc a.val (t a) hc
    have hu_eq : u a = u b := by
      rw [← hgt a, ← hgt b, ← hte, ← hab, hlab]
    have hrel := hu.2 a b hab hu_eq
    rw [mem_RT, mem_Trel7] at hrel
    exact hrel.2.2 (t a) hc (hgt a)
  rcases hvv' with h | h
  · exact key v v' h e
  · exact key v' v h e.symm

/-! ### One seam -/

section Seam

variable {L : Cols (Fin m)}

/-- The keys of column `j + 1`'s gauge, seen from column `j`. -/
noncomputable def newKeysH7 (L : Cols (Fin m)) (j : ℕ) : Fin m → ℕ → ℕ :=
  newKeys7 (L j) (L (j + 1)) (gaugeH7 L j)

/-- **Stage (a), relaxed.** -/
theorem stage_aR7 (hL : IsKCols 7 L) (j i : ℕ) {s : State (Fin m)} :
    ∑ u ∈ (statesR 7 (relH7 L j)).filter (Compat (keyed (newKeysH7 L j) s)), F (rowG m) 7 i u ≤
      ∑ t ∈ (cols (rowG m) L (j + 1)).filter (Compat s), F (rowG m) 7 i (keyed (keysH7 L (j + 1)) t) := by
  obtain ⟨hR, hvc⟩ := gaugeH7_props hL (j + 1)
  refine sum_le_of_preimage _ _ fun u hu => ?_
  rw [mem_filter] at hu
  obtain ⟨t, ht, htu⟩ := pullbackR7 (hL (j + 1)) hR hvc hu.1
  refine ⟨t, mem_filter.mpr ⟨ht, fun v e => ?_⟩, htu⟩
  have htv := ((mem_states (rowG m)).mp ht).1 v
  have hc := hu.2 v
  simp only [keyed, newKeysH7, newKeys7] at hc
  rw [e] at hc
  rw [ite_eq_left htv] at hc
  apply hc
  rw [← htu]; rfl

/-- The relaxed slab sums. -/
theorem slabR_sum7 (P A : Fin m → Finset ℕ) (M : Fin m → ℕ → ℕ) (R : Fin m → Finset ℕ) (c : ℕ) :
    ∑ p ∈ states (rowG m) P, ∑ s ∈ (states (rowG m) A).filter (Compat p),
      ∑ u ∈ (statesR 7 R).filter (Compat (keyed M s)), F (rowG m) 7 c u =
        (slabR (c + 1) m 7 P A M R).Ω.card := card_Ω_R.symm

/-- The core comparison on one past column. -/
theorem core7 (H : K7Bounds) (hL : IsKCols 7 L) (j c : ℕ) (P : Fin m → Finset ℕ)
    (hP : ∀ v a, a ∈ L j v → 7 - 1 ≤ (P v).card ∨ a ∉ P v) :
    (1 - gammaV7) ^ Dcol (L j) * (Z (c + 1) m 7 P (L j) (fun v a => gaugeH7 L j v.val a) : ℚ) ≤
      (1 - gammaV7) ^ Dcol (L (j + 1)) * (slabR (c + 1) m 7 P (L j) (newKeysH7 L j) (relH7 L j)).Ω.card := by
  obtain ⟨hR, hvc⟩ := gaugeH7_props hL j
  have hβ : ∀ v : Fin m, Set.InjOn (gaugeH7 L j v.val) (L j v) ∧ ∀ a ∈ L j v, gaugeH7 L j v.val a < 7 :=
    fun v => by have := hR v.val; rw [extR_val] at this; exact this
  obtain ⟨Bnd, hB⟩ := H (c + 1) m P (L j) (by omega) (hL j) hP
  have := slab_core7 Bnd hB.le (hL j) (hL (j + 1)) hβ hvc hP
  rw [hB] at this
  exact this

/-- The relaxed quantity of a seam. -/
noncomputable def FR7 (L : Cols (Fin m)) (j i : ℕ) (s : State (Fin m)) : ℕ :=
  ∑ u ∈ (statesR 7 (relH7 L j)).filter (Compat (keyed (newKeysH7 L j) s)), F (rowG m) 7 i u

/-- **Stage (b), at `k = 7`.** -/
theorem stage_b7 (H : K7Bounds) (hL : IsKCols 7 L) (j i : ℕ) :
    (1 - gammaV7) ^ Dcol (L j) * ((∑ s ∈ cols (rowG m) L j,
        vec (rowG m) L j s * F (rowG m) 7 (i + 1) (keyed (keysH7 L j) s) : ℕ) : ℚ) ≤
      (1 - gammaV7) ^ Dcol (L (j + 1)) *
        ((∑ s ∈ cols (rowG m) L j, vec (rowG m) L j s * FR7 L j i s : ℕ) : ℚ) := by
  have hcore := fun P hP => core7 (L := L) H hL j i P hP
  have hγ : (0 : ℚ) ≤ (1 - gammaV7) ^ Dcol (L (j + 1)) := pow_nonneg (by unfold gammaV7; norm_num) _
  have hε : (0 : ℚ) ≤ (1 - gammaV7) ^ Dcol (L j) := by
    refine pow_nonneg ?_ _
    unfold gammaV7; norm_num
  match j with
  | 0 =>
      have hsum : ∀ M : Fin m → ℕ → ℕ, ∑ s ∈ cols (rowG m) L 0, vec (rowG m) L 0 s *
          F (rowG m) 7 (i + 1) (keyed M s) = Z (i + 1) m 7 (freshP L) (L 0) M := by
        intro M
        rw [← slab_sum, states_freshP, sum_singleton]
        simp only [vec_zero, one_mul, cols]
        refine sum_congr ?_ fun _ _ => rfl
        ext s
        rw [mem_filter]
        refine ⟨fun hs => ⟨hs, fun v e => ?_⟩, fun h => h.1⟩
        have := lt_fresh (L := L) (((mem_states (rowG m)).mp hs).1 v)
        have e' : ((univ : Finset (Fin m)).biUnion (L 0)).sup id + 1 + v.val % 2 = s v := e
        omega
      have hsumR : ∑ s ∈ cols (rowG m) L 0, vec (rowG m) L 0 s * FR7 L 0 i s =
          (slabR (i + 1) m 7 (freshP L) (L 0) (newKeysH7 L 0) (relH7 L 0)).Ω.card := by
        rw [← slabR_sum7, states_freshP, sum_singleton]
        simp only [vec_zero, one_mul, cols, FR7]
        refine sum_congr ?_ fun _ _ => rfl
        ext s
        rw [mem_filter]
        refine ⟨fun hs => ⟨hs, fun v e => ?_⟩, fun h => h.1⟩
        have := lt_fresh (L := L) (((mem_states (rowG m)).mp hs).1 v)
        have e' : ((univ : Finset (Fin m)).biUnion (L 0)).sup id + 1 + v.val % 2 = s v := e
        omega
      rw [hsum, hsumR]
      exact hcore _ fun v a ha => Or.inr fun h => by
        simp only [freshP, mem_singleton] at h
        have := lt_fresh (L := L) ha
        omega
  | 1 =>
      have hsum : ∀ M : Fin m → ℕ → ℕ, ∑ s ∈ cols (rowG m) L 1, vec (rowG m) L 1 s *
          F (rowG m) 7 (i + 1) (keyed M s) = Z (i + 1) m 7 (L 0) (L 1) M := by
        intro M
        rw [← slab_sum, vec_succ]
        unfold cols
        rw [sum_step_mul]
        simp only [vec_zero, one_mul]
      have hsumR : ∑ s ∈ cols (rowG m) L 1, vec (rowG m) L 1 s * FR7 L 1 i s =
          (slabR (i + 1) m 7 (L 0) (L 1) (newKeysH7 L 1) (relH7 L 1)).Ω.card := by
        rw [← slabR_sum7, vec_succ]
        unfold cols
        rw [sum_step_mul]
        simp only [vec_zero, one_mul, FR7]
      rw [hsum, hsumR]
      exact hcore _ fun v a _ => Or.inl (by rw [hL 0 v]; omega)
  | j + 2 =>
      have hsum : ∀ M : Fin m → ℕ → ℕ, ∑ s ∈ cols (rowG m) L (j + 2), vec (rowG m) L (j + 2) s *
          F (rowG m) 7 (i + 1) (keyed M s) = ∑ r ∈ cols (rowG m) L j, vec (rowG m) L j r *
            Z (i + 1) m 7 (fun v => (L (j + 1) v).erase (r v)) (L (j + 2)) M := by
        intro M
        rw [vec_succ]
        unfold cols
        rw [sum_step_mul, vec_succ, sum_step_mul]
        refine sum_congr rfl fun r _ => ?_
        rw [← slab_sum, filter_compat_states]
      have hsumR : ∑ s ∈ cols (rowG m) L (j + 2), vec (rowG m) L (j + 2) s * FR7 L (j + 2) i s =
          ∑ r ∈ cols (rowG m) L j, vec (rowG m) L j r *
            (slabR (i + 1) m 7 (fun v => (L (j + 1) v).erase (r v)) (L (j + 2)) (newKeysH7 L (j + 2))
              (relH7 L (j + 2))).Ω.card := by
        rw [vec_succ]
        unfold cols
        rw [sum_step_mul, vec_succ, sum_step_mul]
        refine sum_congr rfl fun r _ => ?_
        rw [← slabR_sum7, filter_compat_states]
        rfl
      rw [hsum, hsumR]
      push_cast
      rw [mul_sum, mul_sum]
      refine sum_le_sum fun r _ => ?_
      have h := hcore (fun v => (L (j + 1) v).erase (r v)) fun v a _ => Or.inl (by
        have h1 : (L (j + 1) v).card - 1 ≤ ((L (j + 1) v).erase (r v)).card := pred_card_le_card_erase
        rw [hL (j + 1) v] at h1
        exact h1)
      have hv : (0 : ℚ) ≤ vec (rowG m) L j r := by positivity
      calc (1 - gammaV7) ^ Dcol (L (j + 2)) * ((vec (rowG m) L j r : ℚ) *
            (Z (i + 1) m 7 (fun v => (L (j + 1) v).erase (r v)) (L (j + 2)) (keysH7 L (j + 2)) : ℚ))
          = (vec (rowG m) L j r : ℚ) * ((1 - gammaV7) ^ Dcol (L (j + 2)) *
              Z (i + 1) m 7 (fun v => (L (j + 1) v).erase (r v)) (L (j + 2)) (keysH7 L (j + 2))) := by
            ring
        _ ≤ (vec (rowG m) L j r : ℚ) * ((1 - gammaV7) ^ Dcol (L (j + 3)) *
              (slabR (i + 1) m 7 (fun v => (L (j + 1) v).erase (r v)) (L (j + 2)) (newKeysH7 L (j + 2))
                (relH7 L (j + 2))).Ω.card) := mul_le_mul_of_nonneg_left h hv
        _ = _ := by ring

end Seam

/-! ### The telescope with a potential -/

section Telescope

variable {L : Cols (Fin m)}

/-- The telescoped quantity at column `j`, through the hole gauges. -/
noncomputable def Wt7 (L : Cols (Fin m)) (n j : ℕ) : ℕ :=
  ∑ s ∈ cols (rowG m) L j, vec (rowG m) L j s * F (rowG m) 7 (n - j) (keyed (keysH7 L j) s)

/-- The potential. -/
noncomputable def Pot7 (L : Cols (Fin m)) (n j : ℕ) : ℚ := (1 - gammaV7) ^ Dcol (L j) * Wt7 L n j

theorem one_sub_gV7_pos : 0 < 1 - gammaV7 := by
  unfold gammaV7; norm_num

/-- **One seam.** -/
theorem Pot7_le_succ (H : K7Bounds) (hL : IsKCols 7 L) {n j : ℕ} (hj : j < n) : Pot7 L n j ≤ Pot7 L n (j + 1) := by
  unfold Pot7 Wt7
  have hb := stage_b7 H hL j (n - (j + 1))
  rw [show n - (j + 1) + 1 = n - j by omega] at hb
  -- the relaxed sum is at most the next column's quantity
  have ha : ∑ s ∈ cols (rowG m) L j, vec (rowG m) L j s * FR7 L j (n - (j + 1)) s ≤
      ∑ s ∈ cols (rowG m) L (j + 1), vec (rowG m) L (j + 1) s *
        F (rowG m) 7 (n - (j + 1)) (keyed (keysH7 L (j + 1)) s) := by
    rw [vec_succ]
    unfold cols
    rw [sum_step_mul]
    exact sum_le_sum fun s _ => Nat.mul_le_mul_left _ (stage_aR7 hL j _)
  have haq := (Nat.cast_le (α := ℚ)).mpr ha
  have hγε : (1 - gammaV7) ^ Dcol (L (j + 1)) ≤ (1 - gammaV7) ^ Dcol (L (j + 1)) := by
    refine pow_le_pow_left₀ (by unfold gammaV7; norm_num) ?_ _
    exact le_rfl
  have hγ0 : (0 : ℚ) ≤ (1 - gammaV7) ^ Dcol (L (j + 1)) := pow_nonneg (by unfold gammaV7; norm_num) _
  have hW : (0 : ℚ) ≤ ((∑ s ∈ cols (rowG m) L (j + 1), vec (rowG m) L (j + 1) s *
      F (rowG m) 7 (n - (j + 1)) (keyed (keysH7 L (j + 1)) s) : ℕ) : ℚ) := by positivity
  calc (1 - gammaV7) ^ Dcol (L j) * ((∑ s ∈ cols (rowG m) L j, vec (rowG m) L j s *
          F (rowG m) 7 (n - j) (keyed (keysH7 L j) s) : ℕ) : ℚ)
      ≤ (1 - gammaV7) ^ Dcol (L (j + 1)) *
          ((∑ s ∈ cols (rowG m) L j, vec (rowG m) L j s * FR7 L j (n - (j + 1)) s : ℕ) : ℚ) := hb
    _ ≤ (1 - gammaV7) ^ Dcol (L (j + 1)) * ((∑ s ∈ cols (rowG m) L (j + 1), vec (rowG m) L (j + 1) s *
          F (rowG m) 7 (n - (j + 1)) (keyed (keysH7 L (j + 1)) s) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left haq hγ0
    _ ≤ _ := mul_le_mul_of_nonneg_right hγε hW

theorem Pot7_mono (H : K7Bounds) (hL : IsKCols 7 L) (n : ℕ) : ∀ j, j ≤ n → Pot7 L n 0 ≤ Pot7 L n j := by
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih => intro hj; exact le_trans (ih (by omega)) (Pot7_le_succ H hL (by omega))

/-- **The end.** -/
theorem Pot7_end (L : Cols (Fin m)) (n : ℕ) :
    Pot7 L n n ≤ total (cols (rowG m) L n) (vec (rowG m) L n) := by
  unfold Pot7 Wt7 total
  simp only [Nat.sub_self, F_zero, mul_one]
  have h1 : (1 - gammaV7) ^ Dcol (L n) ≤ 1 :=
    pow_le_one₀ one_sub_gV7_pos.le (by unfold gammaV7; norm_num)
  have h0 : (0 : ℚ) ≤ ((∑ s ∈ cols (rowG m) L n, vec (rowG m) L n s : ℕ) : ℚ) := by positivity
  push_cast at h0 ⊢
  nlinarith

/-! ### The start -/

/-- The relaxed states with nothing relaxed are the uniform states. -/
theorem statesR_empty7 : statesR 7 (fun _ : Fin m => ∅) = states (rowG m) (unif 7) := by
  ext u
  rw [mem_statesR, mem_states]
  simp only [unif, mem_range, notMem_empty, imp_false]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v v' hvv' e => ?_⟩
    rcases hvv' with h | h
    · exact h2 v v' h e
    · exact h2 v' v h e.symm
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun v v' h e => h2 (Or.inl h) e⟩

/-- **Relaxing the first column.** A slab with a dummy past and an unpaired seam column counts the
relaxed first future column, so the relaxation gains apply to it. -/
theorem init_relax7 (n : ℕ) (T : Finset (Fin m × ℕ)) (hT : ∀ p ∈ T, p.1.val + 1 < m ∧ p.2 < 7) :
    ((∑ u ∈ states (rowG m) (unif 7), F (rowG m) 7 n u : ℕ) : ℚ) ≤
      (1 - gammaV7) ^ T.card * ((∑ u ∈ statesR 7 (RT T), F (rowG m) 7 n u : ℕ) : ℚ) := by
  set Pd : Fin m → Finset ℕ := fun v => {100 + v.val % 2}
  set Ad : Fin m → Finset ℕ := fun _ => range 7
  set Md : Fin m → ℕ → ℕ := fun _ _ => 7
  have hAd : ∀ v, (Ad v).card = 7 := fun v => card_range 7
  have hKd : KeyInj 7 Ad Md := fun v a a' _ _ _ h => absurd h (by simp [Md])
  -- the count of the dummy slab
  have hcount : ∀ R : Fin m → Finset ℕ, (slabR (n + 1) m 7 Pd Ad Md R).Ω.card =
      (∑ p ∈ states (rowG m) Pd, ∑ s ∈ (states (rowG m) Ad).filter (Compat p), 1) *
        ∑ u ∈ statesR 7 R, F (rowG m) 7 n u := by
    intro R
    rw [← slabR_sum7, sum_mul]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [one_mul, filter_true_of_mem]
    intro u hu v e
    have := (mem_statesR.mp hu).1 v
    simp only [keyed, Md] at e
    omega
  set N := ∑ p ∈ states (rowG m) Pd, ∑ s ∈ (states (rowG m) Ad).filter (Compat p), 1
  have hN : 0 < N := by
    have hp : (fun v : Fin m => 100 + v.val % 2) ∈ states (rowG m) Pd := by
      rw [mem_states]
      refine ⟨fun v => by simp [Pd], fun v v' hvv' e => ?_⟩
      rcases hvv' with h | h <;> simp only at e <;> omega
    have hs : (fun v : Fin m => v.val % 2) ∈ (states (rowG m) Ad).filter
        (Compat fun v : Fin m => 100 + v.val % 2) := by
      rw [mem_filter, mem_states]
      refine ⟨⟨fun v => by simp [Ad]; omega, fun v v' hvv' e => ?_⟩, fun v e => by simp at e⟩
      rcases hvv' with h | h <;> simp only at e <;> omega
    have h1 : 1 ≤ ∑ s ∈ (states (rowG m) Ad).filter (Compat fun v : Fin m => 100 + v.val % 2), 1 := by
      rw [sum_const, smul_eq_mul, mul_one]; exact card_pos.mpr ⟨_, hs⟩
    have h2 := single_le_sum (f := fun p => ∑ s ∈ (states (rowG m) Ad).filter (Compat p), 1)
      (fun _ _ => Nat.zero_le _) hp
    show 0 < ∑ p ∈ states (rowG m) Pd, ∑ s ∈ (states (rowG m) Ad).filter (Compat p), 1
    omega
  have hrel := relax_all7 (P := Pd) (c := n + 1) (by omega) hAd hKd T hT
  rw [hcount, hcount, statesR_empty7] at hrel
  push_cast at hrel
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have : (N : ℚ) * ((∑ u ∈ states (rowG m) (unif 7), F (rowG m) 7 n u : ℕ) : ℚ) ≤
      (N : ℚ) * ((1 - gammaV7) ^ T.card * ((∑ u ∈ statesR 7 (RT T), F (rowG m) 7 n u : ℕ) : ℚ)) := by
    push_cast; linarith
  exact le_of_mul_le_mul_left this hNq

/-- **The start.** -/
theorem init_le7 (hL : IsKCols 7 L) (n : ℕ) :
    ((∑ u ∈ states (rowG m) (unif 7), F (rowG m) 7 n u : ℕ) : ℚ) ≤ Pot7 L n 0 := by
  obtain ⟨hR, hvc⟩ := gaugeH7_props hL 0
  have h1 := init_relax7 n (Trel7 (L 0) (gaugeH7 L 0))
    (fun p hp => ⟨(mem_Trel7.mp hp).2.1, (mem_Trel7.mp hp).1⟩)
  have h2 : ∑ u ∈ statesR 7 (RT (Trel7 (L 0) (gaugeH7 L 0))), F (rowG m) 7 n u ≤ Wt7 L n 0 := by
    unfold Wt7
    simp only [vec_zero, one_mul, Nat.sub_zero]
    exact sum_le_of_preimage _ _ fun u hu => pullbackR7 (hL 0) hR hvc hu
  have hD := Dcol_le_card_Trel7 (hL 0) hR
  have hγ : (1 - gammaV7) ^ (Trel7 (L 0) (gaugeH7 L 0)).card ≤ (1 - gammaV7) ^ Dcol (L 0) :=
    pow_le_pow_of_le_one (by unfold gammaV7; norm_num) (by unfold gammaV7; norm_num) hD
  have hγε : (1 - gammaV7) ^ Dcol (L 0) ≤ (1 - gammaV7) ^ Dcol (L 0) := by
    refine pow_le_pow_left₀ (by unfold gammaV7; norm_num) ?_ _
    exact le_rfl
  have h2q := (Nat.cast_le (α := ℚ)).mpr h2
  have hnn : (0 : ℚ) ≤ ((∑ u ∈ statesR 7 (RT (Trel7 (L 0) (gaugeH7 L 0))), F (rowG m) 7 n u : ℕ) : ℚ) := by
    positivity
  unfold Pot7
  calc ((∑ u ∈ states (rowG m) (unif 7), F (rowG m) 7 n u : ℕ) : ℚ)
      ≤ (1 - gammaV7) ^ (Trel7 (L 0) (gaugeH7 L 0)).card *
          ((∑ u ∈ statesR 7 (RT (Trel7 (L 0) (gaugeH7 L 0))), F (rowG m) 7 n u : ℕ) : ℚ) := h1
    _ ≤ (1 - gammaV7) ^ Dcol (L 0) *
          ((∑ u ∈ statesR 7 (RT (Trel7 (L 0) (gaugeH7 L 0))), F (rowG m) 7 n u : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_right (le_trans hγ hγε) hnn
    _ ≤ _ := mul_le_mul_of_nonneg_left h2q (pow_nonneg one_sub_gV7_pos.le _)

/-- **The uniform count is a lower bound for every chain of `7`-lists.** -/
theorem uniform_le_total7 (H : K7Bounds) (hL : IsKCols 7 L) (n : ℕ) :
    ∑ u ∈ states (rowG m) (unif 7), F (rowG m) 7 n u ≤
      total (cols (rowG m) L n) (vec (rowG m) L n) := by
  have := le_trans (init_le7 hL n) (le_trans (Pot7_mono H hL n n le_rfl) (Pot7_end L n))
  exact_mod_cast this

end Telescope

/-- **`rowG m □ P_{n+1}` is `7`-ECC.** -/
theorem ecc_rowG_boxProd_seven (H : K7Bounds) (m n : ℕ) : (rowG m □ pathG n).ECCAt 7 := by
  intro M hM
  rw [colConst_eq, col_eq_total_vec]
  exact uniform_le_total7 H (Lof_isKCols hM) n

end GridGen.Gauge

