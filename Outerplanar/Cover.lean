/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Analytic

/-!
# Partial covers of a cycle: peeling and the one-thread theorem

* `Cover.CapGE.le_Z` — a capacity bound, for weights that are not normalised;
* `Cover.Z_peel` — removing the last vertex of an arc;
* `Cover.arc_le_Z` — the capacity of a cover on a proper subset of the cycle (a union of arcs);
* `Cover.capGE_of_witness` — the one-thread theorem (Step 3 of the proof draft).
-/

namespace Outerplanar

open Finset

namespace Cover

variable {n : ℕ} [NeZero n] (P : Cover n)

theorem mem_cols {A : Finset (Fin n)} {b f : Fin n → ℕ} :
    f ∈ P.cols A b ↔ (∀ i, (i ∈ A → f i ∈ P.F i) ∧ (i ∉ A → f i = b i)) ∧
      ∀ i, i ∈ A → i + 1 ∈ A → ¬ P.M i (f i) (f (i + 1)) := by
  classical
  simp only [cols, Finset.mem_filter, Fintype.mem_piFinset]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  by_cases h : i ∈ A <;> simp [h]

theorem Z_nonneg {A : Finset (Fin n)} {b : Fin n → ℕ} {w : Fin n → ℕ → ℝ}
    (hw : ∀ i ∈ A, ∀ c ∈ P.F i, 0 < w i c) : 0 ≤ P.Z A b w :=
  Finset.sum_nonneg fun _ hf => Finset.prod_nonneg fun i hi =>
    (hw i hi _ (((P.mem_cols.mp hf).1 i).1 hi)).le

/-- A capacity bound, for weights that are positive but not normalised. -/
theorem CapGE.le_Z {P : Cover n} {A : Finset (Fin n)} {b : Fin n → ℕ} {C : ℝ}
    (h : P.CapGE A b C) (hne : ∀ i ∈ A, (P.F i).Nonempty) {w : Fin n → ℕ → ℝ}
    (hw : ∀ i ∈ A, ∀ c ∈ P.F i, 0 < w i c) :
    C * ∏ i ∈ A, gmean (P.F i) (w i) ≤ P.Z A b w := by
  have hG : 0 < ∏ i ∈ A, gmean (P.F i) (w i) := Finset.prod_pos fun i _ => gmean_pos _ _
  have h1 := h (fun i c => w i c / gmean (P.F i) (w i)) (fun i hi => by
    refine ⟨fun c hc => div_pos (hw i hi c hc) (gmean_pos _ _), ?_⟩
    rw [Finset.prod_div_distrib, Finset.prod_const, gmean_pow (hne i hi) (hw i hi)]
    exact div_self (Finset.prod_pos (hw i hi)).ne')
  have h2 : P.Z A b (fun i c => w i c / gmean (P.F i) (w i))
      = P.Z A b w / ∏ i ∈ A, gmean (P.F i) (w i) := by
    simp only [Z, Finset.sum_div]
    exact Finset.sum_congr rfl fun f _ => Finset.prod_div_distrib ..
  rw [h2, le_div_iff₀ hG] at h1
  exact h1

/-- The colourings on `A` do not depend on the pinning when `A` is everything. -/
theorem cols_univ (b b' : Fin n → ℕ) : P.cols univ b = P.cols univ b' := by
  ext f
  simp [mem_cols]

open Classical in
/-- **Peeling the last vertex of an arc.** -/
theorem Z_peel {A : Finset (Fin n)} (b : Fin n → ℕ) (w : Fin n → ℕ → ℝ) {i : Fin n}
    (hi : i ∈ A) (hi1 : i + 1 ∉ A) :
    P.Z A b w = ∑ f ∈ P.cols (A.erase i) b, (∏ t ∈ A.erase i, w t (f t)) *
      ∑ c ∈ P.F i with (i - 1 ∈ A → ¬ P.M (i - 1) (f (i - 1)) c), w i c := by
  have hne : i - 1 ≠ i := by
    intro h
    have h1 : i + 1 = i := by
      calc i + 1 = (i - 1) + 1 := by rw [h]
        _ = i := sub_add_cancel i 1
    exact hi1 (h1.symm ▸ hi)
  have hmaps : ∀ f ∈ P.cols A b, Function.update f i (b i) ∈ P.cols (A.erase i) b := by
    intro f hf
    rw [mem_cols] at hf ⊢
    refine ⟨fun t => ⟨fun ht => ?_, fun ht => ?_⟩, fun t ht ht1 => ?_⟩
    · rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
      exact (hf.1 t).1 (Finset.mem_of_mem_erase ht)
    · by_cases hti : t = i
      · subst hti; simp
      · rw [Function.update_of_ne hti]
        exact (hf.1 t).2 fun h => ht (Finset.mem_erase.mpr ⟨hti, h⟩)
    · rw [Function.update_of_ne (Finset.ne_of_mem_erase ht),
        Function.update_of_ne (Finset.ne_of_mem_erase ht1)]
      exact hf.2 t (Finset.mem_of_mem_erase ht) (Finset.mem_of_mem_erase ht1)
  rw [Z, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun f' hf' => ?_
  have hf'' := P.mem_cols.mp hf'
  have hfi : f' i = b i := (hf''.1 i).2 (Finset.notMem_erase i A)
  -- the fibre over `f'`
  have hfib : (P.cols A b).filter (fun f => Function.update f i (b i) = f')
      = ((P.F i).filter fun c => (i - 1 ∈ A → ¬ P.M (i - 1) (f' (i - 1)) c)).image
        (Function.update f' i) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hf, hup⟩
      have hf2 := P.mem_cols.mp hf
      refine ⟨f i, ⟨(hf2.1 i).1 hi, fun h0 => ?_⟩, ?_⟩
      · have := hf2.2 (i - 1) h0 (by rwa [sub_add_cancel])
        rw [sub_add_cancel] at this
        rwa [← hup, Function.update_of_ne hne]
      · rw [← hup]; simp
    · rintro ⟨c, ⟨hc, hok⟩, rfl⟩
      refine ⟨P.mem_cols.mpr ⟨fun t => ⟨fun ht => ?_, fun ht => ?_⟩, fun t ht ht1 => ?_⟩, ?_⟩
      · by_cases hti : t = i
        · subst hti; simpa using hc
        · rw [Function.update_of_ne hti]
          exact (hf''.1 t).1 (Finset.mem_erase.mpr ⟨hti, ht⟩)
      · have hti : t ≠ i := fun h => ht (h ▸ hi)
        rw [Function.update_of_ne hti]
        exact (hf''.1 t).2 fun h => ht (Finset.mem_of_mem_erase h)
      · have hti : t ≠ i := fun h => hi1 (h ▸ ht1)
        rw [Function.update_of_ne hti]
        by_cases ht1i : t + 1 = i
        · have ht' : t = i - 1 := by rw [← ht1i]; simp
          rw [ht1i, Function.update_self]
          subst ht'
          exact hok ht
        · rw [Function.update_of_ne ht1i]
          exact hf''.2 t (Finset.mem_erase.mpr ⟨hti, ht⟩) (Finset.mem_erase.mpr ⟨ht1i, ht1⟩)
      · rw [Function.update_idem, ← hfi, Function.update_eq_self]
  rw [hfib, Finset.sum_image (fun c _ c' _ h => by
    have := congrFun h i
    simpa using this), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.mul_prod_erase A _ hi, Function.update_self, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun t ht => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]

open Fin.NatCast in
/-- A nonempty proper subset of the cycle has a last vertex of an arc. -/
theorem exists_last {A : Finset (Fin n)} (hne : A.Nonempty) (hA : A ≠ univ) :
    ∃ i ∈ A, i + 1 ∉ A := by
  by_contra h
  have h' : ∀ i ∈ A, i + 1 ∈ A := fun i hi => by
    by_contra h1
    exact h ⟨i, hi, h1⟩
  obtain ⟨a, ha⟩ := hne
  have hall : ∀ t : ℕ, a + (t : Fin n) ∈ A := by
    intro t
    induction t with
    | zero => simpa using ha
    | succ t ih =>
      have := h' _ ih
      rwa [add_assoc, ← Nat.cast_succ] at this
  apply hA
  ext x
  simp only [mem_univ, iff_true]
  have := hall (x - a).val
  rwa [Fin.cast_val_eq_self, add_sub_cancel] at this

theorem cols_empty (b : Fin n → ℕ) : P.cols ∅ b = {b} := by
  ext f
  simp [mem_cols, funext_iff]

open Classical in
/-- **The capacity of a union of arcs.** On a proper subset `A` of the cycle, an `m`-fold
partial cover has capacity at least the product over `A` of `m - 1` (the predecessor is in `A`)
or `m` (it is not). -/
theorem arc_le_Z {m : ℕ} (hm : 2 ≤ m) (hcard : ∀ i, (P.F i).card = m) (hM : P.IsMatching)
    (b : Fin n → ℕ) : ∀ (N : ℕ) (A : Finset (Fin n)), A.card = N → A ≠ univ →
      ∀ w : Fin n → ℕ → ℝ, (∀ i ∈ A, ∀ c ∈ P.F i, 0 < w i c) →
      (∏ i ∈ A, if i - 1 ∈ A then (m : ℝ) - 1 else m) * ∏ i ∈ A, gmean (P.F i) (w i)
        ≤ P.Z A b w := by
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  intro N
  induction N with
  | zero =>
    intro A hA _ w _
    rw [Finset.card_eq_zero] at hA
    subst hA
    simp [Z, cols_empty]
  | succ N ih =>
    intro A hA hAu w hw
    have hne : A.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨i, hi, hi1⟩ := exists_last hne hAu
    have hA' : (A.erase i).card = N := by rw [Finset.card_erase_of_mem hi]; omega
    have hA'u : A.erase i ≠ univ := fun h => Finset.notMem_erase i A (h ▸ mem_univ i)
    have hne1 : i - 1 ≠ i := by
      intro h
      have h1 : i + 1 = i := by
        calc i + 1 = (i - 1) + 1 := by rw [h]
          _ = i := sub_add_cancel i 1
      exact hi1 (h1.symm ▸ hi)
    have hmem : ∀ t ∈ A.erase i, (t - 1 ∈ A.erase i ↔ t - 1 ∈ A) := by
      intro t ht
      rw [Finset.mem_erase]
      refine ⟨fun h => h.2, fun h => ⟨fun h' => ?_, h⟩⟩
      have : t = i + 1 := by rw [← h']; simp
      exact hi1 (this ▸ Finset.mem_of_mem_erase ht)
    have hc : ∏ t ∈ A, (if t - 1 ∈ A then (m : ℝ) - 1 else m)
        = (if i - 1 ∈ A then (m : ℝ) - 1 else m)
          * ∏ t ∈ A.erase i, (if t - 1 ∈ A.erase i then (m : ℝ) - 1 else m) := by
      rw [← Finset.mul_prod_erase A _ hi]
      congr 1
      exact Finset.prod_congr rfl fun t ht => by rw [if_congr (hmem t ht) rfl rfl]
    have hg : ∏ t ∈ A, gmean (P.F t) (w t)
        = gmean (P.F i) (w i) * ∏ t ∈ A.erase i, gmean (P.F t) (w t) :=
      (Finset.mul_prod_erase A _ hi).symm
    have hPi : 0 ≤ ∏ t ∈ A.erase i, (if t - 1 ∈ A.erase i then (m : ℝ) - 1 else m) :=
      Finset.prod_nonneg fun t _ => by split_ifs <;> [exact hm1; positivity]
    have hFne : ∀ t, (P.F t).Nonempty := fun t => by rw [← Finset.card_pos, hcard]; omega
    rw [P.Z_peel b w hi hi1, hc, hg]
    by_cases h0 : i - 1 ∈ A
    · -- a pendant vertex
      set s : ℕ → ℝ := fun x => ∑ c ∈ P.F i with ¬ P.M (i - 1) x c, w i c with hs
      set w' := Function.update w (i - 1) (fun x => w (i - 1) x * s x) with hw'
      have h0' : i - 1 ∈ A.erase i := Finset.mem_erase.mpr ⟨hne1, h0⟩
      have hMi := hM (i - 1)
      rw [sub_add_cancel] at hMi
      have hspos : ∀ x ∈ P.F (i - 1), 0 < s x := fun x hx =>
        pendant_pos hm (P.F i) (hcard i) (P.M (i - 1) x)
          (fun c hc c' hc' h h' => hMi.1 x hx c hc c' hc' h h') (w i) (hw i hi)
      have hw'pos : ∀ t ∈ A.erase i, ∀ c ∈ P.F t, 0 < w' t c := by
        intro t ht c hc
        by_cases hti : t = i - 1
        · subst hti
          rw [hw', Function.update_self]
          exact mul_pos (hw _ h0 c hc) (hspos c hc)
        · rw [hw', Function.update_of_ne hti]
          exact hw t (Finset.mem_of_mem_erase ht) c hc
      have hZ : ∑ f ∈ P.cols (A.erase i) b, (∏ t ∈ A.erase i, w t (f t)) *
            ∑ c ∈ P.F i with (i - 1 ∈ A → ¬ P.M (i - 1) (f (i - 1)) c), w i c
          = P.Z (A.erase i) b w' := by
        refine Finset.sum_congr rfl fun f _ => ?_
        have hfil : (∑ c ∈ P.F i with (i - 1 ∈ A → ¬ P.M (i - 1) (f (i - 1)) c), w i c)
            = s (f (i - 1)) :=
          Finset.sum_congr (Finset.filter_congr fun c _ => by simp [h0]) fun _ _ => rfl
        rw [hfil, ← Finset.mul_prod_erase (A.erase i) (fun t => w t (f t)) h0',
          ← Finset.mul_prod_erase (A.erase i) (fun t => w' t (f t)) h0', hw',
          Function.update_self]
        have : ∏ t ∈ (A.erase i).erase (i - 1),
              Function.update w (i - 1) (fun x => w (i - 1) x * s x) t (f t)
            = ∏ t ∈ (A.erase i).erase (i - 1), w t (f t) :=
          Finset.prod_congr rfl fun t ht => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
        rw [this]
        ring
      rw [hZ]
      refine le_trans ?_ (ih (A.erase i) hA' hA'u w' hw'pos)
      have hg' : ∏ t ∈ A.erase i, gmean (P.F t) (w' t)
          = gmean (P.F (i - 1)) (w (i - 1)) * gmean (P.F (i - 1)) s
            * ∏ t ∈ (A.erase i).erase (i - 1), gmean (P.F t) (w t) := by
        rw [← Finset.mul_prod_erase (A.erase i) _ h0', hw', Function.update_self,
          gmean_mul (hw _ h0) hspos]
        congr 1
        exact Finset.prod_congr rfl fun t ht => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
      have hg'' : ∏ t ∈ A.erase i, gmean (P.F t) (w t)
          = gmean (P.F (i - 1)) (w (i - 1))
            * ∏ t ∈ (A.erase i).erase (i - 1), gmean (P.F t) (w t) :=
        (Finset.mul_prod_erase (A.erase i) _ h0').symm
      have hpend := pendant_gmean hm (P.F (i - 1)) (P.F i) (hcard _) (hcard _) (P.M (i - 1))
        hMi.1 hMi.2 (w i) (hw i hi)
      rw [hg', hg'', ite_eq_left h0]
      set R := ∏ t ∈ (A.erase i).erase (i - 1), gmean (P.F t) (w t) with hR
      have hRpos : 0 ≤ R := Finset.prod_nonneg fun t _ => (gmean_pos _ _).le
      set Pc := ∏ t ∈ A.erase i, (if t - 1 ∈ A.erase i then (m : ℝ) - 1 else m)
      have hg0 := (gmean_pos (P.F (i - 1)) (w (i - 1))).le
      calc ((m : ℝ) - 1) * Pc * (gmean (P.F i) (w i) * (gmean (P.F (i - 1)) (w (i - 1)) * R))
          = (Pc * gmean (P.F (i - 1)) (w (i - 1)) * R) * (((m : ℝ) - 1) * gmean (P.F i) (w i)) := by
            ring
        _ ≤ (Pc * gmean (P.F (i - 1)) (w (i - 1)) * R) * gmean (P.F (i - 1)) s :=
            mul_le_mul_of_nonneg_left hpend (by positivity)
        _ = Pc * (gmean (P.F (i - 1)) (w (i - 1)) * gmean (P.F (i - 1)) s * R) := by ring
    · -- an isolated vertex
      have hZ : ∑ f ∈ P.cols (A.erase i) b, (∏ t ∈ A.erase i, w t (f t)) *
            ∑ c ∈ P.F i with (i - 1 ∈ A → ¬ P.M (i - 1) (f (i - 1)) c), w i c
          = P.Z (A.erase i) b w * ∑ c ∈ P.F i, w i c := by
        rw [Z, Finset.sum_mul]
        refine Finset.sum_congr rfl fun f _ => ?_
        congr 1
        exact Finset.sum_congr (Finset.filter_true_of_mem fun c _ => by simp [h0]) fun _ _ => rfl
      rw [hZ, ite_eq_right h0]
      have hIH := ih (A.erase i) hA' hA'u w fun t ht => hw t (Finset.mem_of_mem_erase ht)
      have hS := card_mul_gmean_le_sum (hFne i) (hw i hi)
      rw [hcard] at hS
      set Pc := ∏ t ∈ A.erase i, (if t - 1 ∈ A.erase i then (m : ℝ) - 1 else m)
      set G := ∏ t ∈ A.erase i, gmean (P.F t) (w t)
      have hG : 0 ≤ Pc * G := mul_nonneg hPi (Finset.prod_nonneg fun t _ => (gmean_pos _ _).le)
      calc (m : ℝ) * Pc * (gmean (P.F i) (w i) * G)
          = (Pc * G) * ((m : ℝ) * gmean (P.F i) (w i)) := by ring
        _ ≤ P.Z (A.erase i) b w * ∑ c ∈ P.F i, w i c :=
            mul_le_mul hIH hS (mul_nonneg (Nat.cast_nonneg m) (gmean_pos _ _).le) (P.Z_nonneg fun t ht =>
              hw t (Finset.mem_of_mem_erase ht))

end Cover

open Classical in
theorem sum_mul_sum_mem {n : ℕ} (p : Finset (Fin n) → ℝ) (L : Fin n → ℝ) :
    ∑ J, p J * ∑ i ∈ J, L i = ∑ i, (∑ J with i ∈ J, p J) * L i := by
  have h1 : ∀ J : Finset (Fin n), p J * ∑ i ∈ J, L i = ∑ i, if i ∈ J then p J * L i else 0 := by
    intro J
    rw [Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl fun J _ => h1 J, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_filter]

open Classical in
theorem sum_mul_sum_compl {n : ℕ} (p : Finset (Fin n) → ℝ) (L : Fin n → ℝ) :
    ∑ J, p J * ∑ i ∈ Jᶜ, L i = ∑ i, (∑ J, p J - ∑ J with i ∈ J, p J) * L i := by
  have h1 : ∀ J : Finset (Fin n), p J * ∑ i ∈ Jᶜ, L i = p J * ∑ i, L i - p J * ∑ i ∈ J, L i := by
    intro J
    rw [← Finset.sum_add_sum_compl J L]
    ring
  rw [Finset.sum_congr rfl fun J _ => h1 J, Finset.sum_sub_distrib, sum_mul_sum_mem,
    ← Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

namespace Cover

variable {n : ℕ} [NeZero n] (P : Cover n)

open Classical in
/-- **The one-thread theorem** (Step 3 of the proof draft). If a `k`-fold partial cover has a
cut section `b`, the cover without `b` has capacity at least `g0`, and there is a witness law,
then the capacity is at least `C`. -/
theorem capGE_of_witness {k : ℕ} (hk : 3 ≤ k) (hcard : ∀ i, (P.F i).card = k)
    (hM : P.IsMatching) {b : Fin n → ℕ} {e : Fin n} (hb : P.IsCutSection b e) {g0 C : ℝ}
    (hC : 0 < C) (h0 : (P.erase b).CapGE univ b g0) (hW : Witness k e g0 C)
    (b' : Fin n → ℕ) : P.CapGE univ b' C := by
  obtain ⟨p, hp0, hpgood, hpsum, hpmarg, hpent⟩ := hW
  intro w hw
  have hZb : P.Z univ b' w = P.Z univ b w := by rw [Z, Z, P.cols_univ b' b]
  rw [hZb]
  have hwpos : ∀ i, ∀ c ∈ P.F i, 0 < w i c := fun i => (hw i (mem_univ i)).1
  set u : Fin n → ℝ := fun i => w i (b i) with hu_def
  have hu : ∀ i, 0 < u i := fun i => hwpos i _ (hb.1 i)
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hkpos : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  -- the cover without `b`
  have hFE : ∀ i, (P.erase b).F i = (P.F i).erase (b i) := fun _ => rfl
  have hcardE : ∀ i, ((P.erase b).F i).card = k - 1 := fun i => by
    rw [hFE, Finset.card_erase_of_mem (hb.1 i), hcard]
  have hME : (P.erase b).IsMatching := fun i =>
    ⟨fun x hx y hy y' hy' => (hM i).1 x (Finset.mem_of_mem_erase hx) y
        (Finset.mem_of_mem_erase hy) y' (Finset.mem_of_mem_erase hy'),
      fun x hx x' hx' y hy => (hM i).2 x (Finset.mem_of_mem_erase hx) x'
        (Finset.mem_of_mem_erase hx') y (Finset.mem_of_mem_erase hy)⟩
  have hwE : ∀ i, ∀ c ∈ (P.erase b).F i, 0 < w i c := fun i c hc =>
    hwpos i c (Finset.mem_of_mem_erase hc)
  have hneE : ∀ i, ((P.erase b).F i).Nonempty := fun i => by
    rw [← Finset.card_pos, hcardE]; omega
  have hgm : ∀ i, Real.log (gmean ((P.erase b).F i) (w i))
      = -(((k : ℝ) - 1)⁻¹ * Real.log (u i)) := by
    intro i
    rw [log_gmean, hcardE, hk1, hFE]
    have h1 : ∑ c ∈ P.F i, Real.log (w i c) = 0 := by
      rw [← Real.log_prod (fun c hc => (hwpos i c hc).ne'), (hw i (mem_univ i)).2, Real.log_one]
    rw [← Finset.add_sum_erase _ _ (hb.1 i)] at h1
    have h2 : ∑ c ∈ (P.F i).erase (b i), Real.log (w i c) = -Real.log (u i) := by
      rw [hu_def]; linarith
    rw [h2]; ring
  -- the colourings, sorted by the set of vertices coloured `b`
  let Jset : (Fin n → ℕ) → Finset (Fin n) := fun f => univ.filter fun i => f i = b i
  let T : Finset (Fin n) → ℝ := fun J =>
    ∑ f ∈ (P.cols univ b).filter (fun f => Jset f = J), ∏ i, w i (f i)
  have hZT : P.Z univ b w = ∑ J, T J := (Finset.sum_fiberwise _ Jset _).symm
  have hterm : ∀ f ∈ P.cols univ b, 0 ≤ ∏ i, w i (f i) := fun f hf =>
    Finset.prod_nonneg fun i _ => (hwpos i _ (((P.mem_cols.mp hf).1 i).1 (mem_univ i))).le
  have hT0 : ∀ J, 0 ≤ T J := fun J =>
    Finset.sum_nonneg fun f hf => hterm f (Finset.mem_filter.mp hf).1
  let G : Finset (Fin n) → ℝ := fun J => ∏ i ∈ Jᶜ, gmean ((P.erase b).F i) (w i)
  have hGpos : ∀ J, 0 < G J := fun J => Finset.prod_pos fun i _ => gmean_pos _ _
  let τ : Finset (Fin n) → ℝ := fun J => (∏ i ∈ J, u i) * (gW (k - 1) g0 J * G J)
  have hUpos : ∀ J : Finset (Fin n), 0 < ∏ i ∈ J, u i := fun J => Finset.prod_pos fun i _ => hu i
  have hτ : ∀ J, 0 < p J → τ J ≤ T J := by
    intro J hpJ
    obtain ⟨hgood, -⟩ := hpgood J hpJ
    have hsub : (P.erase b).cols Jᶜ b ⊆ (P.cols univ b).filter (fun f => Jset f = J) := by
      intro f hf
      have hf' := (P.erase b).mem_cols.mp hf
      have hin : ∀ t, t ∈ J → f t = b t := fun t ht => (hf'.1 t).2 (by simpa using ht)
      have hout : ∀ t, t ∉ J → f t ∈ P.F t ∧ f t ≠ b t := fun t ht => by
        have := (hf'.1 t).1 (by simpa using ht)
        rw [hFE] at this
        exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
      rw [Finset.mem_filter, mem_cols]
      refine ⟨⟨fun t => ⟨fun _ => ?_, fun h => absurd (mem_univ t) h⟩, fun t _ _ => ?_⟩, ?_⟩
      · by_cases ht : t ∈ J
        · rw [hin t ht]; exact hb.1 t
        · exact (hout t ht).1
      · by_cases ht : t ∈ J <;> by_cases ht1 : t + 1 ∈ J
        · have hte : t = e := by
            by_contra hte
            exact hgood t hte ht ht1
          subst hte
          rw [hin t ht, hin _ ht1]
          exact hb.2.2.1 _ (hb.1 _)
        · rw [hin t ht]
          by_cases hte : t = e
          · subst hte
            exact hb.2.2.1 _ (hout _ ht1).1
          · intro hMx
            exact (hout _ ht1).2 ((hM t).1 (b t) (hb.1 t) _ (hout _ ht1).1 _ (hb.1 _) hMx
              (hb.2.1 t hte))
        · rw [hin _ ht1]
          by_cases hte : t = e
          · subst hte
            exact hb.2.2.2 _ (hout _ ht).1
          · intro hMx
            exact (hout _ ht).2 ((hM t).2 _ (hout _ ht).1 (b t) (hb.1 t) _ (hb.1 _) hMx
              (hb.2.1 t hte))
        · exact hf'.2 t (by simpa using ht) (by simpa using ht1)
      · ext t
        simp only [Jset, Finset.mem_filter, mem_univ, true_and]
        exact ⟨fun h => by_contra fun ht => (hout t ht).2 h, hin t⟩
    have hZ : (∏ i ∈ J, u i) * (P.erase b).Z Jᶜ b w ≤ T J := by
      rw [Z, Finset.mul_sum]
      calc ∑ f ∈ (P.erase b).cols Jᶜ b, (∏ i ∈ J, u i) * ∏ i ∈ Jᶜ, w i (f i)
          = ∑ f ∈ (P.erase b).cols Jᶜ b, ∏ i, w i (f i) := by
            refine Finset.sum_congr rfl fun f hf => ?_
            rw [← Finset.prod_mul_prod_compl J fun i => w i (f i)]
            congr 1
            refine Finset.prod_congr rfl fun i hi => ?_
            rw [((((P.erase b).mem_cols.mp hf).1 i).2 (by simpa using hi))]
        _ ≤ T J := Finset.sum_le_sum_of_subset_of_nonneg hsub fun f hf _ =>
            hterm f (Finset.mem_filter.mp hf).1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (hUpos J).le) hZ
    by_cases hJ : J = ∅
    · subst hJ
      have := h0.le_Z (fun i _ => hneE i) (fun i _ => hwE i)
      simpa [gW, G] using this
    · have hne : Jᶜ ≠ univ := by
        intro h
        exact hJ (by simpa using h)
      have := (P.erase b).arc_le_Z (m := k - 1) (by omega) hcardE hME b _ Jᶜ rfl hne w
        (fun i _ => hwE i)
      have hprod : (∏ i ∈ Jᶜ, if i - 1 ∈ Jᶜ then ((k - 1 : ℕ) : ℝ) - 1 else ((k - 1 : ℕ) : ℝ))
          = gW (k - 1) g0 J := by
        rw [gW, ite_eq_right hJ, arcW]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : i - 1 ∈ J <;> simp [h]
      rw [hprod] at this
      exact this
  have hτpos : ∀ J, 0 < p J → 0 < τ J := fun J hpJ =>
    mul_pos (hUpos J) (mul_pos (hpgood J hpJ).2 (hGpos J))
  -- Gibbs
  have hg := gibbs univ p T (fun J _ => hp0 J) hpsum
    (fun J _ hpJ => lt_of_lt_of_le (hτpos J hpJ) (hτ J hpJ)) (fun J _ => hT0 J)
  rw [← hZT] at hg
  have hZpos : 0 < P.Z univ b w := by
    obtain ⟨J, -, hpJ⟩ : ∃ J ∈ (univ : Finset (Finset (Fin n))), 0 < p J := by
      by_contra h
      have : ∑ J, p J = 0 := Finset.sum_eq_zero fun J hJ =>
        le_antisymm (not_lt.mp fun hlt => h ⟨J, hJ, hlt⟩) (hp0 J)
      linarith
    rw [hZT]
    exact lt_of_lt_of_le (lt_of_lt_of_le (hτpos J hpJ) (hτ J hpJ))
      (Finset.single_le_sum (fun J _ => hT0 J) (mem_univ J))
  have h1 : ∑ J, p J * Real.log (τ J / p J) ≤ ∑ J, p J * Real.log (T J / p J) :=
    Finset.sum_le_sum fun J _ => by
      rcases (hp0 J).eq_or_lt with h | h
      · rw [← h]; simp
      · exact mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (hτpos J h) h)
          (div_le_div_of_nonneg_right (hτ J h) h.le)) h.le
  have h2 : ∀ J, p J * Real.log (τ J / p J) = p J * Real.log (gW (k - 1) g0 J / p J)
      + (p J * ∑ i ∈ J, Real.log (u i)
        - ((k : ℝ) - 1)⁻¹ * (p J * ∑ i ∈ Jᶜ, Real.log (u i))) := by
    intro J
    rcases (hp0 J).eq_or_lt with h | h
    · rw [← h]; simp
    · have hgpos := (hpgood J h).2
      have e1 : τ J / p J = (∏ i ∈ J, u i) * ((gW (k - 1) g0 J / p J) * G J) := by
        simp only [τ]; field_simp
      rw [e1, Real.log_mul (hUpos J).ne' (mul_pos (div_pos hgpos h) (hGpos J)).ne',
        Real.log_mul (div_pos hgpos h).ne' (hGpos J).ne',
        Real.log_prod (fun i _ => (hu i).ne'), Real.log_prod (fun i _ => (gmean_pos _ _).ne'),
        Finset.sum_congr rfl fun i _ => hgm i, Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring
  have h3 : ∑ J, p J * Real.log (τ J / p J)
      = ∑ J, p J * Real.log (gW (k - 1) g0 J / p J) := by
    rw [Finset.sum_congr rfl fun J _ => h2 J, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_mul_sum_mem, sum_mul_sum_compl, hpsum]
    have hz : ∑ i, (∑ J with i ∈ J, p J) * Real.log (u i)
        - ((k : ℝ) - 1)⁻¹ * ∑ i, (1 - ∑ J with i ∈ J, p J) * Real.log (u i) = 0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hpmarg i]
      have hk0 : (k : ℝ) ≠ 0 := by
        have : (3 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      field_simp
      ring
    rw [hz, add_zero]
  have : Real.log C ≤ Real.log (P.Z univ b w) := by linarith
  exact (Real.log_le_log_iff hC hZpos).mp this

end Cover

end Outerplanar
