/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seam
import GridGen.Main

/-!
# Every grid is `k`-ECC for `k ≥ 10`

The gauge telescope runs along a chain of columns of `k`-lists. Column `j` carries a vertically
consistent labelling `gauge j`, built from `gauge (j-1)` by `tilde` and `glueLab`. The telescoped
quantity is

  `W j = ∑_{s ∈ column j} vec j s · F_{n-j}(gauge j ∘ s)`,

where `F` counts uniform futures (`GridGen.Uniform`). Three facts make the argument:

* `W 0` is at least the uniform count: a VC labelling pulls every uniform state back to a list
  state (`init_le`).
* `W n` is the list count.
* `W j ≤ W (j + 1)` (`W_le_succ`). This has two stages. Stage (a): the new column's states map
  onto the uniform ones by the new gauge (`stage_a`). Stage (b): the slab inequality `slab_core`,
  after expanding the chain one or two columns back into slabs (`stage_b`).
-/

open Finset SimpleGraph ListColoring
open scoped Classical SimpleGraph

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {m k : ℕ}

/-! ### Pulling uniform states back along a labelling -/

/-- If every state of `U` is the key image of a state of `T`, the `T`-sum dominates. -/
theorem sum_le_of_preimage {U T : Finset (State (Fin m))} (G : State (Fin m) → ℕ)
    (key : State (Fin m) → State (Fin m)) (h : ∀ u ∈ U, ∃ t ∈ T, key t = u) :
    ∑ u ∈ U, G u ≤ ∑ t ∈ T, G (key t) := by
  choose! φ hφT hφ using h
  have hinj : Set.InjOn φ U := fun u hu u' hu' e => by rw [← hφ u hu, ← hφ u' hu', e]
  calc ∑ u ∈ U, G u = ∑ u ∈ U, G (key (φ u)) := sum_congr rfl fun u hu => by rw [hφ u hu]
    _ = ∑ t ∈ U.image φ, G (key t) := (sum_image (f := fun t => G (key t)) hinj).symm
    _ ≤ ∑ t ∈ T, G (key t) :=
        sum_le_sum_of_subset_of_nonneg (fun t ht => by
          obtain ⟨u, hu, rfl⟩ := mem_image.mp ht; exact hφT u hu) fun _ _ _ => Nat.zero_le _

/-- A labelling that is injective with labels below `k` on `k`-lists is onto `{0, …, k-1}`. -/
theorem surj_of_rowLab {X : Fin m → Finset ℕ} (hX : ∀ v, (X v).card = k) {g : ℕ → ℕ → ℕ}
    (hR : RowLab k (extR X) g) (v : Fin m) {ℓ : ℕ} (hℓ : ℓ < k) : ∃ a ∈ X v, g v.val a = ℓ := by
  have hR' := hR v.val
  rw [extR_val] at hR'
  have hsub : (X v).image (g v.val) ⊆ range k := fun z hz => by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz; exact mem_range.mpr (hR'.2 a ha)
  have hc : ((X v).image (g v.val)).card = k := by rw [card_image_of_injOn hR'.1, hX]
  have heq := eq_of_subset_of_card_le hsub (by rw [hc, card_range])
  have : ℓ ∈ (X v).image (g v.val) := by rw [heq]; exact mem_range.mpr hℓ
  obtain ⟨a, ha, e⟩ := mem_image.mp this
  exact ⟨a, ha, e⟩

/-- **Pulling back.** Under a VC labelling of a column of `k`-lists, every uniform state is the key
image of a list state, compatible with any `s` whose keys the uniform state avoids. -/
theorem pullback {X : Fin m → Finset ℕ} (hX : ∀ v, (X v).card = k) {g : ℕ → ℕ → ℕ}
    (hR : RowLab k (extR X) g)
    (hvc : ∀ v, ∀ c ∈ extR X v ∩ extR X (v + 1), g (v + 1) c = g v c)
    {u : State (Fin m)} (hu : u ∈ states (rowG m) (unif k)) :
    ∃ t ∈ states (rowG m) X, keyed (fun v a => g v.val a) t = u := by
  rw [mem_states] at hu
  have hlt : ∀ v, u v < k := fun v => by simpa [unif] using hu.1 v
  choose t ht hgt using fun v => surj_of_rowLab hX hR v (hlt v)
  refine ⟨t, ?_, funext hgt⟩
  rw [mem_states]
  refine ⟨ht, fun v v' hvv' e => ?_⟩
  apply hu.2 hvv'
  rw [← hgt v, ← hgt v', e]
  rcases hvv' with h | h
  · have := hvc v.val (t v') (mem_inter.mpr ⟨by rw [extR_val]; rw [← e]; exact ht v,
      by rw [show v.val + 1 = v'.val from h, extR_val]; exact ht v'⟩)
    rw [show v.val + 1 = v'.val from h] at this
    exact this.symm
  · have := hvc v'.val (t v') (mem_inter.mpr ⟨by rw [extR_val]; exact ht v',
      by rw [show v'.val + 1 = v.val from h, extR_val]; rw [← e]; exact ht v⟩)
    rw [show v'.val + 1 = v.val from h] at this
    exact this

/-! ### The gauges of a chain of columns -/

/-- A first row labelling: the position of a colour in its list. -/
noncomputable def initLab (Bx : ℕ → Finset ℕ) (v a : ℕ) : ℕ :=
  if h : a ∈ Bx v then (((Bx v).equivFin ⟨a, h⟩ : Fin (Bx v).card) : ℕ) else 0

theorem rowLab_initLab {Bx : ℕ → Finset ℕ} (hB : ∀ v, (Bx v).card ≤ k) :
    RowLab k Bx (initLab Bx) := by
  intro v
  refine ⟨fun a ha a' ha' e => ?_, fun a ha => ?_⟩
  · rw [Finset.mem_coe] at ha ha'
    unfold initLab at e
    rw [dite_eq_left ha, dite_eq_left ha'] at e
    have := (Bx v).equivFin.injective (Fin.ext e)
    exact congrArg Subtype.val this
  · unfold initLab; rw [dite_eq_left ha]
    exact lt_of_lt_of_le (Fin.isLt _) (hB v)

/-- The gauge of column `j`. -/
noncomputable def gauge (k : ℕ) (L : Cols (Fin m)) : ℕ → ℕ → ℕ → ℕ
  | 0 => glueLab k (extR (L 0)) (initLab (extR (L 0)))
  | j + 1 => glueLab k (extR (L (j + 1))) (tilde (extR (L j)) (extR (L (j + 1))) (gauge k L j))

theorem extR_card_le {X : Fin m → Finset ℕ} (hX : ∀ v, (X v).card = k) (v : ℕ) :
    (extR X v).card ≤ k := by
  unfold extR; split_ifs with h
  · rw [hX]
  · simp

theorem extR_card_eq {X Y : Fin m → Finset ℕ} (hX : ∀ v, (X v).card = k)
    (hY : ∀ v, (Y v).card = k) (v : ℕ) : (extR X v).card = (extR Y v).card := by
  unfold extR; split_ifs with h
  · rw [hX, hY]
  · rfl

/-- **The gauges are row labellings and vertically consistent.** -/
theorem gauge_props {L : Cols (Fin m)} (hL : IsKCols k L) : ∀ j,
    RowLab k (extR (L j)) (gauge k L j) ∧
      ∀ v, ∀ c ∈ extR (L j) v ∩ extR (L j) (v + 1), gauge k L j (v + 1) c = gauge k L j v c := by
  intro j
  have glue_props : ∀ {Bx : ℕ → Finset ℕ} {βx : ℕ → ℕ → ℕ}, RowLab k Bx βx →
      RowLab k Bx (glueLab k Bx βx) ∧
        ∀ v, ∀ c ∈ Bx v ∩ Bx (v + 1), glueLab k Bx βx (v + 1) c = glueLab k Bx βx v c :=
    fun hR => ⟨fun v => ⟨glueLab_injOn hR v, fun a ha => glueLab_lt hR v ha⟩,
      fun v c hc => glueLab_vc hR v hc⟩
  induction j with
  | zero => exact glue_props (rowLab_initLab (extR_card_le (hL 0)))
  | succ j ih =>
      refine glue_props (rowLab_tilde (extR_card_eq (hL j) (hL (j + 1))) fun v => ?_)
      exact ⟨(ih.1 v).1, (ih.1 v).2⟩

/-! ### One seam -/

section Seam

variable {L : Cols (Fin m)}

/-- The keys of column `j`'s gauge. -/
noncomputable def keysOf (k : ℕ) (L : Cols (Fin m)) (j : ℕ) : Fin m → ℕ → ℕ :=
  fun v a => gauge k L j v.val a

/-- The keys of column `j + 1`'s gauge, seen from column `j`: leaving colours are unpaired. -/
noncomputable def newKeys (k : ℕ) (L : Cols (Fin m)) (j : ℕ) : Fin m → ℕ → ℕ :=
  fun v a => if a ∈ L (j + 1) v then gauge k L (j + 1) v.val a else k

/-- **Stage (a).** -/
theorem stage_a (hL : IsKCols k L) (j i : ℕ) {s : State (Fin m)} :
    F (rowG m) k (i + 1) (keyed (newKeys k L j) s) ≤
      ∑ t ∈ (cols (rowG m) L (j + 1)).filter (Compat s), F (rowG m) k i (keyed (keysOf k L (j + 1)) t) := by
  rw [F_succ]
  obtain ⟨hR, hvc⟩ := gauge_props hL (j + 1)
  refine sum_le_of_preimage _ _ fun u hu => ?_
  rw [mem_filter] at hu
  obtain ⟨t, ht, htu⟩ := pullback (hL (j + 1)) hR hvc hu.1
  refine ⟨t, mem_filter.mpr ⟨ht, fun v e => ?_⟩, htu⟩
  have htv := ((mem_states (rowG m)).mp ht).1 v
  have hc := hu.2 v
  simp only [keyed, newKeys] at hc
  rw [e] at hc
  rw [ite_eq_left htv] at hc
  apply hc
  rw [← htu]; rfl

/-- The states of a column compatible with `r`: the lists with `r`'s colours removed. -/
theorem filter_compat_states (X : Fin m → Finset ℕ) (r : State (Fin m)) :
    (states (rowG m) X).filter (Compat r) = states (rowG m) (fun v => (X v).erase (r v)) := by
  ext p
  simp only [mem_filter, mem_states, mem_erase, Compat]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨fun v => ⟨fun e => h3 v e.symm, h1 v⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨fun v => (h1 v).2, h2⟩, fun v e => (h1 v).1 e.symm⟩

/-- The slab sums. -/
theorem slab_sum (P A : Fin m → Finset ℕ) (M : Fin m → ℕ → ℕ) (c : ℕ) :
    ∑ p ∈ states (rowG m) P, ∑ s ∈ (states (rowG m) A).filter (Compat p),
      F (rowG m) k c (keyed M s) = Z c m k P A M := (card_Ω_eq).symm

/-- Seam bounds on every slab with `k`-lists in the seam column. -/
def GaugeBounds (k : ℕ) : Prop :=
  ∀ (c m : ℕ) (P A : Fin m → Finset ℕ), 1 ≤ c → (∀ v, (A v).card = k) →
    Nonempty (SlabBounds c m k P A)

theorem gaugeBounds_ten (hk : 10 ≤ k) : GaugeBounds k :=
  fun _ _ _ _ hc hA => ⟨slabBounds_ten hk hc hA⟩

/-- The core comparison on every admissible past column. -/
theorem core (hG : GaugeBounds k) (hL : IsKCols k L) (j c : ℕ) (hc : 1 ≤ c) (P : Fin m → Finset ℕ)
    (hP : ∀ v a, a ∈ L j v → k - 1 ≤ (P v).card ∨ a ∉ P v) :
    Z c m k P (L j) (keysOf k L j) ≤ Z c m k P (L j) (newKeys k L j) := by
  obtain ⟨hR, hvc⟩ := gauge_props hL j
  have hβ : ∀ v : Fin m, Set.InjOn (gauge k L j v.val) (L j v) ∧ ∀ a ∈ L j v, gauge k L j v.val a < k :=
    fun v => by have := hR v.val; rw [extR_val] at this; exact this
  exact slab_core_gen (Classical.choice (hG c m P (L j) hc (hL j))) (hL j) (hL (j + 1))
    (gauge k L j) hβ hvc hP

/-- The fresh past column of the first seam: one colour per row, above every list colour. -/
noncomputable def freshP (L : Cols (Fin m)) : Fin m → Finset ℕ :=
  fun v => {((univ : Finset (Fin m)).biUnion (L 0)).sup id + 1 + v.val % 2}

theorem lt_fresh {L : Cols (Fin m)} {v : Fin m} {a : ℕ} (ha : a ∈ L 0 v) :
    a < ((univ : Finset (Fin m)).biUnion (L 0)).sup id + 1 := by
  have : a ≤ ((univ : Finset (Fin m)).biUnion (L 0)).sup id :=
    le_sup (f := id) (mem_biUnion.mpr ⟨v, mem_univ _, ha⟩)
  omega

theorem states_freshP (L : Cols (Fin m)) :
    states (rowG m) (freshP L) =
      {fun v => ((univ : Finset (Fin m)).biUnion (L 0)).sup id + 1 + v.val % 2} := by
  ext p
  rw [mem_states, mem_singleton]
  simp only [freshP, mem_singleton]
  constructor
  · rintro ⟨h, _⟩; funext v; exact h v
  · rintro rfl
    refine ⟨fun v => rfl, fun v v' hvv' e => ?_⟩
    rcases hvv' with h | h <;> simp only at e <;> omega

/-- **Stage (b).** -/
theorem stage_b (hG : GaugeBounds k) (hL : IsKCols k L) (j i : ℕ) :
    ∑ s ∈ cols (rowG m) L j, vec (rowG m) L j s * F (rowG m) k (i + 1) (keyed (keysOf k L j) s) ≤
      ∑ s ∈ cols (rowG m) L j, vec (rowG m) L j s * F (rowG m) k (i + 1) (keyed (newKeys k L j) s) := by
  have hcore := fun P hP => core (L := L) hG hL j (i + 1) (by omega) P hP
  match j with
  | 0 =>
      -- the fresh past column
      have hsum : ∀ M : Fin m → ℕ → ℕ, ∑ s ∈ cols (rowG m) L 0, vec (rowG m) L 0 s *
          F (rowG m) k (i + 1) (keyed M s) = Z (i + 1) m k (freshP L) (L 0) M := by
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
      rw [hsum, hsum]
      exact hcore _ fun v a ha => Or.inr fun h => by
        simp only [freshP, mem_singleton] at h
        have := lt_fresh (L := L) ha
        omega
  | 1 =>
      have hsum : ∀ M : Fin m → ℕ → ℕ, ∑ s ∈ cols (rowG m) L 1, vec (rowG m) L 1 s *
          F (rowG m) k (i + 1) (keyed M s) = Z (i + 1) m k (L 0) (L 1) M := by
        intro M
        rw [← slab_sum, vec_succ]
        unfold cols
        rw [sum_step_mul]
        simp only [vec_zero, one_mul]
      rw [hsum, hsum]
      exact hcore _ fun v a _ => Or.inl (by rw [hL 0 v]; omega)
  | j + 2 =>
      have hsum : ∀ M : Fin m → ℕ → ℕ, ∑ s ∈ cols (rowG m) L (j + 2), vec (rowG m) L (j + 2) s *
          F (rowG m) k (i + 1) (keyed M s) = ∑ r ∈ cols (rowG m) L j, vec (rowG m) L j r *
            Z (i + 1) m k (fun v => (L (j + 1) v).erase (r v)) (L (j + 2)) M := by
        intro M
        rw [vec_succ]
        unfold cols
        rw [sum_step_mul, vec_succ, sum_step_mul]
        refine sum_congr rfl fun r _ => ?_
        rw [← slab_sum, filter_compat_states]
      rw [hsum, hsum]
      refine sum_le_sum fun r _ => Nat.mul_le_mul_left _ (hcore _ fun v a _ => Or.inl ?_)
      have h1 : (L (j + 1) v).card - 1 ≤ ((L (j + 1) v).erase (r v)).card := pred_card_le_card_erase
      rw [hL (j + 1) v] at h1
      exact h1

end Seam

/-! ### The telescope -/

section Telescope

variable {L : Cols (Fin m)}

/-- The telescoped quantity at column `j` of a chain of `n + 1` columns. -/
noncomputable def W (k : ℕ) (L : Cols (Fin m)) (n j : ℕ) : ℕ :=
  ∑ s ∈ cols (rowG m) L j, vec (rowG m) L j s * F (rowG m) k (n - j) (keyed (keysOf k L j) s)

/-- **One seam.** -/
theorem W_le_succ (hG : GaugeBounds k) (hL : IsKCols k L) {n j : ℕ} (hj : j < n) :
    W k L n j ≤ W k L n (j + 1) := by
  unfold W
  rw [show n - j = (n - (j + 1)) + 1 by omega]
  refine le_trans (stage_b hG hL j _) ?_
  rw [vec_succ]
  unfold cols
  rw [sum_step_mul]
  exact sum_le_sum fun s _ => Nat.mul_le_mul_left _ (stage_a hL j _)

theorem W_mono (hG : GaugeBounds k) (hL : IsKCols k L) (n : ℕ) : ∀ j, j ≤ n → W k L n 0 ≤ W k L n j := by
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih => intro hj; exact le_trans (ih (by omega)) (W_le_succ hG hL (by omega))

/-- **The initial condition.** -/
theorem init_le (hL : IsKCols k L) (n : ℕ) :
    ∑ u ∈ states (rowG m) (unif k), F (rowG m) k n u ≤ W k L n 0 := by
  unfold W
  simp only [vec_zero, one_mul, Nat.sub_zero]
  obtain ⟨hR, hvc⟩ := gauge_props hL 0
  exact sum_le_of_preimage _ _ fun u hu => pullback (hL 0) hR hvc hu

/-- **The end.** -/
theorem W_end (L : Cols (Fin m)) (n : ℕ) :
    W k L n n = total (cols (rowG m) L n) (vec (rowG m) L n) := by
  unfold W total
  simp

/-- **The uniform count is a lower bound for every chain of `k`-lists**, `k ≥ 10`. -/
theorem uniform_le_total (hG : GaugeBounds k) (hL : IsKCols k L) (n : ℕ) :
    ∑ u ∈ states (rowG m) (unif k), F (rowG m) k n u ≤
      total (cols (rowG m) L n) (vec (rowG m) L n) := by
  rw [← W_end (k := k)]
  exact le_trans (init_le hL n) (W_mono hG hL n n le_rfl)

end Telescope

/-- **`rowG m □ P_{n+1}` is `k`-ECC whenever the seam bounds hold at `k`.** -/
theorem ecc_rowG_boxProd_of {k : ℕ} (hG : GaugeBounds k) (m n : ℕ) :
    (rowG m □ pathG n).ECCAt k := by
  intro M hM
  rw [colConst_eq, col_eq_total_vec]
  exact uniform_le_total hG (Lof_isKCols hM) n

/-- **`rowG m □ P_{n+1}` is `k`-ECC for every `k ≥ 10`.** -/
theorem ecc_rowG_boxProd {k : ℕ} (hk : 10 ≤ k) (m n : ℕ) : (rowG m □ pathG n).ECCAt k :=
  ecc_rowG_boxProd_of (gaugeBounds_ten hk) m n

end GridGen.Gauge
