/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Seam7
import GridGen.Gauge.Seven.BoxV7

/-!
# The new gauge at `k = 7`, and the slab inequality

The lookahead process of `Order7.lean` glues the new column's row labellings into a vertically
consistent labelling (`proc_spec`): every move swaps two labels below `k`, and every edge processed
is matched, later moves on other colours keeping every match (`matched_snoc`). With the star and move
phase of `Seam7.lean` and the relaxation of `BoxV7.lean` this gives the slab inequality at `k = 7`
(`slab_core7`), for any seam bounds `Bounds7` with `γ_V ≤ 27/5075`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {m : ℕ}

section Proc

variable {Ax Bx : ℕ → Finset ℕ} {βx : ℕ → ℕ → ℕ}

/-- A colour step keeps small moves and every match. -/
theorem stepC_keep (hR : RowLab 7 Bx βx) (e : ℕ) (O : List GOp) {cc : ℕ}
    (hcc : cc ∈ Bx e ∩ Bx (e + 1)) (hO : OpsSmall 7 O) :
    OpsSmall 7 (stepC Ax Bx βx e O cc) ∧
      ∀ e' c, c ∈ Bx e' ∩ Bx (e' + 1) → Matched (βx := βx) O e' c →
        Matched (βx := βx) (stepC Ax Bx βx e O cc) e' c := by
  have hlab : ∀ {O : List GOp} {u d : ℕ}, OpsSmall 7 O → d ∈ Bx u → curL O u (βx u d) < 7 :=
    fun hO hd => curL_lt hO _ ((hR _).2 _ hd)
  have hop : ∀ {O : List GOp} {e' d : ℕ} {o : GOp}, OpsSmall 7 O →
      OnColour (Bx := Bx) (βx := βx) O e' d o → OpsSmall 7 (O ++ [o]) := by
    intro O e' d o hO ho
    obtain ⟨h1, h2, rfl, -⟩ := ho
    exact opsSmall_append hO fun o' ho' => by
      rw [List.mem_singleton] at ho'; subst ho'; exact ⟨hlab hO h2, hlab hO h1⟩
  rcases stepC_cases (Ax := Ax) (Bx := Bx) (βx := βx) e O hcc with
    ⟨-, he⟩ | ⟨-, -, o, ho, he⟩ | ⟨-, -, -, o₂, o₁, ho₂, ho₁, he⟩
  · rw [he]; exact ⟨hO, fun _ _ _ h => h⟩
  · rw [he]
    refine ⟨hop hO ho, fun e' c hc hm => ?_⟩
    rw [mem_inter] at hc
    exact matched_snoc hR ho hc hm
  · rw [he]
    refine ⟨hop (hop hO ho₂) ho₁, fun e' c hc hm => ?_⟩
    rw [mem_inter] at hc
    exact matched_snoc hR ho₁ hc (matched_snoc hR ho₂ hc hm)

/-- A run of colour steps keeps small moves and every match. -/
theorem fold_keep (hR : RowLab 7 Bx βx) (e : ℕ) :
    ∀ (L : List ℕ) (O : List GOp), (∀ cc ∈ L, cc ∈ Bx e ∩ Bx (e + 1)) → OpsSmall 7 O →
      OpsSmall 7 (L.foldl (stepC Ax Bx βx e) O) ∧
        ∀ e' c, c ∈ Bx e' ∩ Bx (e' + 1) → Matched (βx := βx) O e' c →
          Matched (βx := βx) (L.foldl (stepC Ax Bx βx e) O) e' c := by
  intro L
  induction L with
  | nil => intro O _ hO; exact ⟨hO, fun _ _ _ h => h⟩
  | cons cc L ih =>
      intro O hL hO
      obtain ⟨h1, h2⟩ := stepC_keep (Ax := Ax) hR e O (hL cc (by simp)) hO
      obtain ⟨h3, h4⟩ := ih _ (fun c hc => hL c (by simp [hc])) h1
      exact ⟨h3, fun e' c hc hm => h4 e' c hc (h2 e' c hc hm)⟩

/-- **The process**: small moves, and every processed edge matched. -/
theorem proc_spec (hR : RowLab 7 Bx βx) : ∀ n, OpsSmall 7 (proc Ax Bx βx n) ∧
    ∀ e < n, ∀ c ∈ Bx e ∩ Bx (e + 1), Matched (βx := βx) (proc Ax Bx βx n) e c := by
  intro n
  induction n with
  | zero => exact ⟨fun o ho => by simp [proc] at ho, fun e he => by omega⟩
  | succ n ih =>
      obtain ⟨hs, hm⟩ := ih
      obtain ⟨h1, h2⟩ := fold_keep (Ax := Ax) hR n (ordE Bx n) (proc Ax Bx βx n)
        (fun cc hc => (mem_sort _).mp hc) hs
      obtain ⟨N, -, -, h3, -⟩ := runEdge_spec (Ax := Ax) hR n (proc Ax Bx βx n)
        (small_actOn hs _) (small_actOn hs _)
      refine ⟨h1, fun e he c hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with h | rfl
      · exact h2 e c hc (hm e h c hc)
      · exact h3 c hc

end Proc

/-! ### The new gauge and the slab inequality -/

/-- **The new column's gauge at `k = 7`**: the lookahead process applied to `tilde`. -/
noncomputable def gaugeNew7 (A B : Fin m → Finset ℕ) (β : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ :=
  fun v a => curL (proc (extR A) (extR B) (tilde (extR A) (extR B) β) m) v
    (tilde (extR A) (extR B) β v a)

/-- The new keys: the new gauge on staying colours, unpaired on leaving ones. -/
noncomputable def newKeys7 (A B : Fin m → Finset ℕ) (β : ℕ → ℕ → ℕ) : Fin m → ℕ → ℕ :=
  fun v a => if a ∈ B v then gaugeNew7 A B β v.val a else 7

/-- The relaxed pairs at `k = 7`. -/
noncomputable def Trel7 (B : Fin m → Finset ℕ) (β' : ℕ → ℕ → ℕ) : Finset (Fin m × ℕ) :=
  (univ ×ˢ range 7).filter (fun p => p.1.val + 1 < m ∧
    ∀ c ∈ extR B p.1.val ∩ extR B (p.1.val + 1), β' p.1.val c ≠ p.2)

theorem mem_Trel7 {B : Fin m → Finset ℕ} {β' : ℕ → ℕ → ℕ} {p : Fin m × ℕ} :
    p ∈ Trel7 B β' ↔ p.2 < 7 ∧ p.1.val + 1 < m ∧
      ∀ c ∈ extR B p.1.val ∩ extR B (p.1.val + 1), β' p.1.val c ≠ p.2 := by
  unfold Trel7; simp [mem_product]

/-- **Each vertical edge relaxes its new-column difference** (`k = 7`). -/
theorem Dcol_le_card_Trel7 {B : Fin m → Finset ℕ} (hB : ∀ v, (B v).card = 7) {β' : ℕ → ℕ → ℕ}
    (hR : RowLab 7 (extR B) β') : Dcol B ≤ (Trel7 B β').card := by
  unfold Dcol
  rw [card_eq_sum_card_fiberwise (f := fun p : Fin m × ℕ => p.1) (t := univ)
    (fun _ _ => mem_univ _), ← Fin.sum_univ_eq_sum_range (fun v => (extR B (v + 1) \ extR B v).card)]
  refine sum_le_sum fun v _ => ?_
  by_cases hv : v.val + 1 < m
  · set S := extR B v.val ∩ extR B (v.val + 1)
    have himg : (S.image (β' v.val)).card = S.card :=
      card_image_of_injOn fun a ha a' ha' e => (hR v.val).1 (mem_inter.mp ha).1 (mem_inter.mp ha').1 e
    have hsub : S.image (β' v.val) ⊆ range 7 := fun z hz => by
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
      exact mem_range.mpr ((hR v.val).2 a (mem_inter.mp ha).1)
    have hfib : ((Trel7 B β').filter (fun p => p.1 = v)) =
        ((range 7 \ S.image (β' v.val)).image fun ℓ => (v, ℓ)) := by
      ext ⟨u, ℓ⟩
      simp only [mem_filter, mem_Trel7, mem_image, mem_sdiff, mem_range, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hℓ, -, hall⟩, rfl⟩
        exact ⟨ℓ, ⟨hℓ, fun ⟨a, ha, e⟩ => hall a ha e⟩, rfl, rfl⟩
      · rintro ⟨ℓ', ⟨hℓ, hn⟩, rfl, rfl⟩
        exact ⟨⟨hℓ, hv, fun a ha e => hn ⟨a, ha, e⟩⟩, rfl⟩
    rw [hfib, card_image_of_injective _ (fun a b h => by simpa using h), card_sdiff_of_subset hsub,
      card_range, himg]
    have e1 : extR B (v.val + 1) = B ⟨v.val + 1, hv⟩ := by simp [extR, hv]
    have e0 : extR B v.val = B v := extR_val B v
    have h1 := card_sdiff_add_card_inter (B ⟨v.val + 1, hv⟩) (B v)
    rw [hB, inter_comm] at h1
    show (extR B (v.val + 1) \ extR B v.val).card ≤ 7 - (extR B v.val ∩ extR B (v.val + 1)).card
    rw [e1, e0]
    omega
  · have : extR B (v.val + 1) = ∅ := extR_ge B (by omega)
    rw [this]; simp

variable {c : ℕ} {P A B : Fin m → Finset ℕ} {β : ℕ → ℕ → ℕ}

/-- **The new gauge is a vertically consistent row labelling.** -/
theorem gaugeNew7_props (hA : ∀ v, (A v).card = 7) (hB : ∀ v, (B v).card = 7)
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < 7) :
    RowLab 7 (extR B) (gaugeNew7 A B β) ∧
      ∀ v, ∀ c ∈ extR B v ∩ extR B (v + 1), gaugeNew7 A B β (v + 1) c = gaugeNew7 A B β v c := by
  have hcard : ∀ v, (extR A v).card = (extR B v).card := by
    intro v; simp only [extR]; split_ifs with h
    · rw [hA, hB]
    · rfl
  have hβx : ∀ v, Set.InjOn (β v) (extR A v) ∧ ∀ a ∈ extR A v, β v a < 7 := by
    intro v; simp only [extR]; split_ifs with h
    · exact hβ ⟨v, h⟩
    · simp
  have hR : RowLab 7 (extR B) (tilde (extR A) (extR B) β) := rowLab_tilde hcard hβx
  obtain ⟨hs, hm⟩ := proc_spec (Ax := extR A) hR m
  refine ⟨fun v => ⟨fun a ha a' ha' e => (hR v).1 ha ha' (compA_injective _ e),
    fun a ha => curL_lt hs _ ((hR v).2 a ha)⟩, fun v cc hcc => ?_⟩
  have hv : v < m := lt_of_mem_extR (mem_inter.mp hcc).2 |> fun h => by omega
  exact hm v hv cc hcc

/-- The final cover of the star and move phase is the new keys. -/
theorem cov_final_eq (v : Fin m) (a : ℕ) (ha : a ∈ A v) :
    cov 7 β (proc (extR A) (extR B) (tilde (extR A) (extR B) β) m) (stars A B) v a =
      newKeys7 A B β v a := by
  unfold cov newKeys7 gaugeNew7
  by_cases hb : a ∈ B v
  · rw [ite_eq_right (by rw [mem_stars]; exact fun h => h.2 hb), ite_eq_left hb]
    congr 1
    unfold tilde; rw [ite_eq_left (by rw [extR_val]; exact ha)]
  · rw [ite_eq_left (by rw [mem_stars]; exact ⟨ha, hb⟩), ite_eq_right hb]

/-- **The slab inequality at `k = 7`.** -/
theorem slab_core7 {hc : 1 ≤ c} (Bnd : Bounds7 c m P A hc) (hγV : Bnd.γV ≤ gammaV7)
    (hA : ∀ v, (A v).card = 7) (hB : ∀ v, (B v).card = 7)
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < 7)
    (hvc : ∀ v, ∀ c ∈ extR A v ∩ extR A (v + 1), β (v + 1) c = β v c)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) :
    (1 - Bnd.γV) ^ Dcol A * (Z c m 7 P A (fun v a => β v.val a) : ℚ) ≤
      (1 - Bnd.γV) ^ Dcol B *
        (slabR c m 7 P A (newKeys7 A B β) (RT (Trel7 B (gaugeNew7 A B β)))).Ω.card := by
  have h1 := seam_moves7 (B := B) hA hB hβ hP Bnd hvc
  have hfin : Z c m 7 P A (cov 7 β (proc (extR A) (extR B) (tilde (extR A) (extR B) β) m)
      (stars A B)) = Z c m 7 P A (newKeys7 A B β) := Z_congr fun v a ha => cov_final_eq v a ha
  rw [hfin] at h1
  obtain ⟨hR', -⟩ := gaugeNew7_props hA hB hβ
  have hKn : KeyInj 7 A (newKeys7 A B β) := by
    intro v a a' ha ha' e hlt
    simp only [newKeys7] at e hlt
    split_ifs at e hlt with h1 h2 h2 <;> try omega
    have hb1 : a ∈ extR B v.val := by rw [extR_val]; exact h1
    have hb2 : a' ∈ extR B v.val := by rw [extR_val]; exact h2
    exact (hR' v.val).1 hb1 hb2 e
  have hrel := relax_all7 (P := P) hc hA hKn (Trel7 B (gaugeNew7 A B β))
    (fun p hp => ⟨(mem_Trel7.mp hp).2.1, (mem_Trel7.mp hp).1⟩)
  rw [slabR_empty] at hrel
  have hDB := Dcol_le_card_Trel7 hB hR'
  have hγ0 : 0 ≤ Bnd.γV := le_trans Bnd.hε0 Bnd.hD
  have hV : 0 ≤ 1 - gammaV7 ∧ 1 - gammaV7 ≤ 1 - Bnd.γV := by unfold gammaV7 at hγV ⊢; constructor <;> linarith
  have hpow : (1 - gammaV7) ^ (Trel7 B (gaugeNew7 A B β)).card ≤ (1 - Bnd.γV) ^ Dcol B :=
    calc (1 - gammaV7) ^ (Trel7 B (gaugeNew7 A B β)).card ≤ (1 - gammaV7) ^ Dcol B :=
          pow_le_pow_of_le_one hV.1 (by unfold gammaV7; norm_num) hDB
      _ ≤ (1 - Bnd.γV) ^ Dcol B := pow_le_pow_left₀ hV.1 hV.2 _
  have hZR : (0 : ℚ) ≤ (slabR c m 7 P A (newKeys7 A B β) (RT (Trel7 B (gaugeNew7 A B β)))).Ω.card := by
    positivity
  calc (1 - Bnd.γV) ^ Dcol A * (Z c m 7 P A (fun v a => β v.val a) : ℚ)
      ≤ Z c m 7 P A (newKeys7 A B β) := h1
    _ = (slab c m 7 P A (newKeys7 A B β)).Ω.card := rfl
    _ ≤ (1 - gammaV7) ^ (Trel7 B (gaugeNew7 A B β)).card *
          (slabR c m 7 P A (newKeys7 A B β) (RT (Trel7 B (gaugeNew7 A B β)))).Ω.card := hrel
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow hZR

end GridGen.Gauge
