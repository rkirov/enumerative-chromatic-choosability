/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SqMultiSound
import Outerplanar.SqHullBase
import Outerplanar.HexWalks
import Outerplanar.SqData.Table
import Outerplanar.Gain

/-!
# Squares with three loaded edges: from patterns to lists

The three-loaded analogue of `genF_le_faceSum` and `ballFaceBare_two_of_cover`
(`Outerplanar/Square.lean`).

* `faceP Q w a b` — the face of a square with pattern `Q` (`Pat`, `Outerplanar/Square.lean`) in
  index form, all three path edges loaded with the index tables `w 0`, `w 1`, `w 2`;
* `GoodH md tn td Q` — every choice of tables in the classes `md` gives the hexagon bound
  `(N₀ N₁ N₂ tn / td) ^ 6` at the root; `GoodC md tn td Q` — the closing count
  `≥ N₀ N₁ N₂ tn / td`. Both are monotone under `PatLE` (`GoodH.mono`, `GoodC.mono`), and they
  follow from the records of `Outerplanar/SqMultiCheck.lean` (`goodH_of_check`,
  `goodC_of_check`);
* `sqClass m` — the class of a path edge of a run: `0` the ball class `InBall`, `1` the
  matching class `BijGe … 1`, `2` the hexagon class `Hex`, read in index form by
  `edgeOK_of_sqClass`;
* `sq_hex_of_good`, `sq_close_of_good` — given the property for the 52 patterns of the cover
  `SqData.qs`, every square with three loaded path edges in the classes of the run has the
  hexagon bound at its root edge (resp. the closing count).

Part of milestone M0 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`.
-/

namespace Outerplanar.SqMulti

open Finset

/-! ### Patterns -/

/-- The equal colours of the path edge `j` of a pattern. -/
def patE (Q : Pat) (j : ℕ) : BMat := if j = 0 then Q.e01 else if j = 1 then Q.e12 else Q.e23

/-- The face of a square with pattern `Q` and loaded tables `w 0`, `w 1`, `w 2`, in index
form. -/
def faceP (Q : Pat) (w : ℕ → Fin 3 → Fin 3 → ℝ) (a b : Fin 3) : ℝ :=
  ∑ s, ∑ t, if (!Q.e01 a s && !Q.e12 s t && !Q.e23 t b) = true then w 0 a s * w 1 s t * w 2 t b
    else 0

/-- The hexagon bound at the root of a pattern, for tables in the classes `md`. -/
def GoodH (md : ℕ → Mode) (tn td : ℕ) (Q : Pat) : Prop :=
  ∀ (w : ℕ → Fin 3 → Fin 3 → ℝ) (N : ℕ → ℝ), (∀ j < 3, 0 < N j) →
    (∀ j < 3, EdgeOK (md j) (patE Q j) (w j) (N j)) →
    (N 0 * N 1 * N 2 * tn / td) ^ 6 ≤ ∏ k, faceP Q w (offPair k).1 (offPair k).2

/-- The closing count of a pattern, for tables in the classes `md`. -/
def GoodC (md : ℕ → Mode) (tn td : ℕ) (Q : Pat) : Prop :=
  ∀ (w : ℕ → Fin 3 → Fin 3 → ℝ) (N : ℕ → ℝ), (∀ j < 3, 0 < N j) →
    (∀ j < 3, EdgeOK (md j) (patE Q j) (w j) (N j)) →
    N 0 * N 1 * N 2 * tn / td ≤ ∑ a, ∑ b, if Q.e03 a b = true then 0 else faceP Q w a b

/-- More equal colours make the class hypothesis weaker. -/
theorem EdgeOK.mono_E {md : Mode} {E E' : BMat} {w : Fin 3 → Fin 3 → ℝ} {N : ℝ}
    (h : EdgeOK md E w N) (hle : ∀ x y, E x y = true → E' x y = true) : EdgeOK md E' w N := by
  have hf : ∀ x y, E' x y = false → E x y = false := fun x y h' => by
    cases hE : E x y
    · rfl
    · rw [hle x y hE] at h'; exact absurd h' (by decide)
  refine ⟨h.nonneg, fun h1 x y hxy => h.fl h1 x y (hf x y hxy),
    fun h1 σ hσ hp => h.bij h1 σ hσ fun x => hf _ _ (hp x),
    fun h1 σ hσ => h.hx h1 σ ⟨hσ.1, fun c d hcd => hσ.2 c d (hle c d hcd)⟩,
    fun h1 σ hσ j c d hcd => h.ball h1 σ ⟨hσ.1, fun c d hcd => hσ.2 c d (hle c d hcd)⟩ j c d
      (hf c d hcd)⟩

theorem patE_le {P Q : Pat} (h : PatLE P Q) {j : ℕ} (x y : Fin 3) :
    patE P j x y = true → patE Q j x y = true := by
  unfold patE
  split_ifs
  · exact h.h01 x y
  · exact h.h12 x y
  · exact h.h23 x y

theorem faceP_mono {P Q : Pat} (h : PatLE P Q) {w : ℕ → Fin 3 → Fin 3 → ℝ}
    (hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y) (a b : Fin 3) : faceP Q w a b ≤ faceP P w a b := by
  unfold faceP
  refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => ?_
  have hnn : 0 ≤ w 0 a s * w 1 s t * w 2 t b :=
    mul_nonneg (mul_nonneg (hw 0 (by norm_num) _ _) (hw 1 (by norm_num) _ _))
      (hw 2 (by norm_num) _ _)
  by_cases hQ : (!Q.e01 a s && !Q.e12 s t && !Q.e23 t b) = true
  · have hP : (!P.e01 a s && !P.e12 s t && !P.e23 t b) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hQ ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hQ
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · cases e : P.e01 a s
        · rfl
        · rw [h.h01 a s e] at h1; exact h1
      · cases e : P.e12 s t
        · rfl
        · rw [h.h12 s t e] at h2; exact h2
      · cases e : P.e23 t b
        · rfl
        · rw [h.h23 t b e] at h3; exact h3
    rw [ite_eq_left hQ, ite_eq_left hP]
  · rw [ite_eq_right hQ]
    split_ifs
    · exact hnn
    · exact le_rfl

theorem faceP_nonneg {Q : Pat} {w : ℕ → Fin 3 → Fin 3 → ℝ} (hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y)
    (a b : Fin 3) : 0 ≤ faceP Q w a b :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => by
    split_ifs
    · exact mul_nonneg (mul_nonneg (hw 0 (by norm_num) _ _) (hw 1 (by norm_num) _ _))
        (hw 2 (by norm_num) _ _)
    · exact le_rfl

theorem GoodH.mono {md : ℕ → Mode} {tn td : ℕ} {P Q : Pat} (h : PatLE P Q)
    (hQ : GoodH md tn td Q) : GoodH md tn td P := by
  intro w N hN hE
  have hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y := fun j hj => (hE j hj).nonneg
  refine (hQ w N hN fun j hj => (hE j hj).mono_E (patE_le h)).trans ?_
  exact Finset.prod_le_prod₀ (fun k _ => faceP_nonneg hw _ _) fun k _ => faceP_mono h hw _ _

theorem GoodC.mono {md : ℕ → Mode} {tn td : ℕ} {P Q : Pat} (h : PatLE P Q)
    (hQ : GoodC md tn td Q) : GoodC md tn td P := by
  intro w N hN hE
  have hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y := fun j hj => (hE j hj).nonneg
  refine (hQ w N hN fun j hj => (hE j hj).mono_E (patE_le h)).trans ?_
  rw [h.h03]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  split_ifs
  · exact le_rfl
  · exact faceP_mono h hw _ _

/-! ### From records to patterns -/

theorem bit_eq : bit = bitAt := rfl

theorem edgeE_patE {pat j : ℕ} (hj : j < 3) : edgeE pat j = patE (patOfCode pat) j := by
  funext x y
  unfold edgeE patE eqc patOfCode
  rw [bit_eq]
  interval_cases j <;> simp only [ite_true] <;> congr 1 <;> omega

theorem faceN_faceP (pat : ℕ) (w : ℕ → Fin 3 → Fin 3 → ℝ) (a b : Fin 3) :
    faceN pat w a.val b.val = faceP (patOfCode pat) w a b := by
  unfold faceN faceP
  rw [sum_range9]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  have h1 : legal pat a.val ((3 * s.val + t.val) / 3) ((3 * s.val + t.val) % 3) b.val
      = (!(patOfCode pat).e01 a s && !(patOfCode pat).e12 s t && !(patOfCode pat).e23 t b) := by
    rw [cell_div, cell_mod]
    unfold legal eqc patOfCode
    rw [bit_eq, show 9 * 0 + (3 * a.val + s.val) = 3 * a.val + s.val by omega,
      show 9 * 1 + (3 * s.val + t.val) = 9 + 3 * s.val + t.val by omega,
      show 9 * 2 + (3 * t.val + b.val) = 18 + 3 * t.val + b.val by omega]
  have h2 : tW w a.val (3 * s.val + t.val) b.val = w 0 a s * w 1 s t * w 2 t b := by
    unfold tW cellOf
    simp only [ite_true, ite_false, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
      cell_div, cell_mod, wc_cell]
  rw [h1, h2]

/-- **A hexagon record gives the property of its pattern.** -/
theorem goodH_of_check {md : ℕ → Mode} {pat D k : ℕ} {ps : List (ℕ × ℕ × ℕ × ℕ)} {tn td : ℕ}
    (h : checkH md pat D k ps tn td = true) : GoodH md tn td (patOfCode pat) := by
  intro w N hN hE
  have key := checkR_sound h hN fun j hj => by rw [edgeE_patE hj]; exact hE j hj
  have hl : hexRows.length = 6 := rfl
  have ht : rTot hexRows = 6 := rfl
  rw [ht, hl] at key
  refine key.trans (le_of_eq ?_)
  rw [Finset.prod_range, ← (Equiv.refl (Fin 6)).prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  fin_cases i <;> simp [rA, rB, rN, hexRows, ← faceN_faceP, offPair]

/-- **A closing record gives the property of its pattern.** -/
theorem goodC_of_check {md : ℕ → Mode} {pat D k : ℕ} {ps : List (ℕ × ℕ × ℕ × ℕ)} {tn td : ℕ}
    (h : checkC md pat D k ps tn td = true) : GoodC md tn td (patOfCode pat) := by
  intro w N hN hE
  have key := checkC_sound h hN fun j hj => by rw [edgeE_patE hj]; exact hE j hj
  refine key.trans (le_of_eq ?_)
  rw [sum_range9]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cell_div, cell_mod, faceN_faceP]
  have : eqc pat 3 (3 * a.val + b.val) = (patOfCode pat).e03 a b := by
    unfold eqc patOfCode
    rw [bit_eq]
    congr 1
    omega
  rw [this]

/-! ### The classes of the runs, on lists -/

/-- The mode of a digit: `0` the ball class, `1` the matching class, `2` the hexagon class. -/
def modeOf (m : ℕ) : Mode := if m = 0 then modeB else if m = 1 then modeM else modeH

theorem modesOf_eq (c j : ℕ) : modesOf c j = modeOf (dig 2 c j) := rfl

/-- The class of a path edge with digit `m`, on lists. -/
def sqClass (m : ℕ) (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  if m = 0 then InBall S T W N else if m = 1 then BijGe S T W N 1 else Hex S T W N

/-- The class of a path edge read through enumerations of its two lists. -/
theorem edgeOK_of_sqClass {m : ℕ} {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N : ℝ}
    (hW : ∀ c d, 0 ≤ W c d) (h : sqClass m S T W N) {ζ ξ : Fin 3 → ℕ}
    (hζ : Function.Injective ζ) (hξ : Function.Injective ξ) (hζm : ∀ a, ζ a ∈ S)
    (hξm : ∀ b, ξ b ∈ T) :
    EdgeOK (modeOf m) (fun x y => decide (ζ x = ξ y)) (fun x y => W (ζ x) (ξ y)) N := by
  unfold sqClass at h
  unfold modeOf
  have h11 : ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
  split_ifs at h ⊢ with h0 h1
  · refine ⟨fun x y => hW _ _, fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun _ => ?_⟩
    simp only [modeB, h11, one_mul]
    exact h.idx hζ hξ hζm hξm
  · refine ⟨fun x y => hW _ _, fun h => absurd h (by decide), fun _ σ hσ hp => ?_,
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    simp only [modeM, h11, one_mul]
    have := h ζ (ξ ∘ σ) hζ (hξ.comp hσ.1) hζm (fun b => hξm _)
      (fun a e => by have := hp a; simp [e] at this)
    simpa using this
  · refine ⟨fun x y => hW _ _, fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun _ σ ⟨hσ, hc⟩ => ?_, fun h => absurd h (by decide)⟩
    simp only [modeH, h11, one_mul]
    have hm : Matched S T (fun k => ζ (offPair k).1) (fun k => ξ (σ (offPair k).2)) :=
      ⟨ζ, ξ ∘ σ, hζ, hξ.comp hσ, hζm, fun b => hξm _, fun a b hab => by
        obtain ⟨i, hi⟩ := offPair_surj a b hab
        exact ⟨i, by show ζ (offPair i).1 = ζ a; rw [hi],
          by show ξ (σ (offPair i).2) = ξ (σ b); rw [hi]⟩⟩
    have hne : ∀ i, ζ (offPair i).1 ≠ ξ (σ (offPair i).2) := fun i e =>
      offPair_ne i (hσ (hc _ _ (decide_eq_true e)))
    exact h _ _ hm hne

/-! ### The hexagon class from its index form, up to a renumbering -/

theorem prod_offPair_perm {π : Fin 3 → Fin 3} (hπ : Function.Bijective π) (G : Fin 3 → Fin 3 → ℝ) :
    ∏ k, G (π (offPair k).1) (π (offPair k).2) = ∏ k, G (offPair k).1 (offPair k).2 := by
  have hcell : ∀ r : Fin 6, ∃ r', offPair r' = (π (offPair r).1, π (offPair r).2) := fun r =>
    offPair_surj _ _ fun e => offPair_ne r (hπ.1 e)
  choose κ hκ using hcell
  have hκinj : Function.Injective κ := fun r r' e => by
    apply offPair_injective
    have h1 := hκ r
    have h2 := hκ r'
    rw [e, h2] at h1
    exact Prod.ext (hπ.1 (congrArg Prod.fst h1).symm) (hπ.1 (congrArg Prod.snd h1).symm)
  have hκb : Function.Bijective κ := ⟨hκinj, Finite.injective_iff_surjective.mp hκinj⟩
  rw [← hκb.prod_comp fun k => G (offPair k).1 (offPair k).2]
  exact Finset.prod_congr rfl fun r _ => by rw [hκ r]

theorem hex_of_idx_perm {Lu Lv : Finset ℕ} {F : ℕ → ℕ → ℝ} {A : ℝ}
    (h : ∀ α β : Fin 3 → ℕ, Function.Injective α → Function.Injective β → (∀ a, α a ∈ Lu) →
      (∀ b, β b ∈ Lv) → (∀ a b, α a = β b → a = b) →
      ∃ π : Fin 3 → Fin 3, Function.Bijective π ∧
        A ^ 6 ≤ ∏ k, F (α (π (offPair k).1)) (β (π (offPair k).2))) :
    Hex Lu Lv F A := by
  refine hex_of_idx fun α β hα hβ hαm hβm hal => ?_
  obtain ⟨π, hπ, hb⟩ := h α β hα hβ hαm hβm hal
  rwa [prod_offPair_perm hπ fun a b => F (α a) (β b)] at hb

/-! ### Normal form and the cover -/

/-- **The frame of a square**: for aligned enumerations of the root lists, a renumbering `π`
of both and enumerations of the two interior lists whose pattern has the property `Good`, for
any property that holds on the 52 patterns and is monotone. -/
theorem sq_frame {Good : Pat → Prop} (hmono : ∀ P Q, PatLE P Q → Good Q → Good P)
    (hgood : ∀ q, q < SqData.qs.length → Good (patOfCode (SqData.qs.getD q 0)))
    {Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    {α β : Fin 3 → ℕ} (hα : Function.Injective α) (hβ : Function.Injective β)
    (hβm : ∀ b, β b ∈ Lv) (hal : ∀ a b, α a = β b → a = b) :
    ∃ π : Fin 3 → Fin 3, Function.Bijective π ∧ ∃ γ₀ γ₁ : Fin 3 → ℕ, Function.Injective γ₀ ∧
      Function.Injective γ₁ ∧ (∀ s, γ₀ s ∈ Li 0) ∧ (∀ t, γ₁ t ∈ Li 1) ∧
      Good (patOf (fun a => α (π a)) γ₀ γ₁ (fun b => β (π b))) := by
  obtain ⟨g₀, hg₀, hg₀m, hg₀a⟩ := exists_aligned (hLi 0) hα
  obtain ⟨g₁, hg₁, hg₁m, hg₁a⟩ := exists_aligned (hLi 1) hg₀
  obtain ⟨δ, hδ, hδm, hδa⟩ := exists_aligned hLv hg₁
  have hρex : ∀ b, ∃ t, δ t = β b := fun b => by
    have h := hβm b
    rw [← image_enum hLv hδ hδm] at h
    obtain ⟨t, -, ht⟩ := mem_image.mp h
    exact ⟨t, ht⟩
  choose ρ hρ using hρex
  have hρinj : Function.Injective ρ := fun b b' e => hβ (by rw [← hρ b, ← hρ b', e])
  have hρb : Function.Bijective ρ := ⟨hρinj, Finite.injective_iff_surjective.mp hρinj⟩
  have e01 : ∀ a s, α a = g₀ s ↔ a = s ∧ decide (α a = g₀ a) = true := fun a s =>
    ⟨fun e => by
      obtain rfl := hg₀a s a e.symm
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have e12 : ∀ s t, g₀ s = g₁ t ↔ s = t ∧ decide (g₀ s = g₁ s) = true := fun s t =>
    ⟨fun e => by
      obtain rfl := hg₁a t s e.symm
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have e23 : ∀ t b, g₁ t = β b ↔ t = ρ b ∧ decide (g₁ t = δ t) = true := fun t b =>
    ⟨fun e => by
      have e' : δ (ρ b) = g₁ t := by rw [hρ b, e]
      obtain rfl := hδa (ρ b) t e'
      exact ⟨rfl, decide_eq_true e'.symm⟩, fun ⟨e, h⟩ => by
      rw [← hρ b, ← e]; exact of_decide_eq_true h⟩
  have e03 : ∀ a b, α a = β b ↔ a = b ∧ decide (α a = β a) = true := fun a b =>
    ⟨fun e => by
      obtain rfl := hal a b e
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have hcons : NormCons (fun a => decide (α a = g₀ a)) (fun s => decide (g₀ s = g₁ s))
      (fun t => decide (g₁ t = δ t)) (fun a => decide (α a = β a)) ρ := by
    refine ⟨fun b h0 h1 h2 => ?_, fun a h0 h1 hr => ?_, fun a h0 h2 hr => ?_,
      fun a h1 h2 hr => ?_⟩
    · have e : α (ρ b) = β b := by
        rw [of_decide_eq_true h0, of_decide_eq_true h1, of_decide_eq_true h2, hρ b]
      obtain h := hal _ _ e
      exact ⟨h, by rw [h] at e; exact decide_eq_true e⟩
    · have e : g₁ a = β a := by
        rw [← of_decide_eq_true h1, ← of_decide_eq_true h0, of_decide_eq_true hr]
      have h := ((e23 a a).mp e).1
      exact ⟨h.symm, ((e23 a a).mp e).2⟩
    · have e : g₀ a = g₁ (ρ a) := by
        rw [← of_decide_eq_true h0, of_decide_eq_true hr, of_decide_eq_true h2, hρ a]
      have h := ((e12 a (ρ a)).mp e).1
      exact ⟨h.symm, ((e12 a (ρ a)).mp e).2⟩
    · have e : α a = g₀ (ρ a) := by
        rw [of_decide_eq_true h1, of_decide_eq_true h2, hρ a, of_decide_eq_true hr]
      have h := ((e01 a (ρ a)).mp e).1
      exact ⟨h.symm, ((e01 a (ρ a)).mp e).2⟩
  obtain ⟨π, π₀, π₁, hπ, hπ₀, hπ₁, Q, hQ, hle⟩ :=
    pcover_of_table hgood SqData.chunk_all _ _ _ _ ρ hρb hcons
  refine ⟨π, hπ, fun s => g₀ (π₀ s), fun t => g₁ (π₁ t), hg₀.comp hπ₀.1, hg₁.comp hπ₁.1,
    fun s => hg₀m _, fun t => hg₁m _, ?_⟩
  have hP : patOf (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t))
        (fun b => β (π b))
      = normPat (fun a => decide (α a = g₀ a)) (fun s => decide (g₀ s = g₁ s))
        (fun t => decide (g₁ t = δ t)) (fun a => decide (α a = β a)) ρ π π₀ π₁ := by
    unfold patOf normPat
    congr 1
    · funext a s
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e01 _ _
    · funext s t
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e12 _ _
    · funext t b
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e23 _ _
    · funext a b
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact (e03 _ _).trans ⟨fun ⟨e, h⟩ => ⟨hπ.1 e, h⟩, fun ⟨e, h⟩ => ⟨by rw [e], h⟩⟩
  rw [hP]
  exact hmono _ _ hle hQ

/-! ### The face sum against the index form -/

/-- The index tables of a square, read through enumerations of its four lists. -/
def wOf (W : Fin 3 → ℕ → ℕ → ℝ) (α γ₀ γ₁ β : Fin 3 → ℕ) : ℕ → Fin 3 → Fin 3 → ℝ := fun j =>
  if j = 0 then fun x y => W 0 (α x) (γ₀ y) else if j = 1 then fun x y => W 1 (γ₀ x) (γ₁ y)
  else fun x y => W 2 (γ₁ x) (β y)

/-- The scales of the three path edges, on numbers. -/
def nOf (N : Fin 3 → ℝ) (j : ℕ) : ℝ := if j = 0 then N 0 else if j = 1 then N 1 else N 2

theorem wOf_nonneg {W : Fin 3 → ℕ → ℕ → ℝ} (hW : ∀ j c d, 0 ≤ W j c d) (α γ₀ γ₁ β : Fin 3 → ℕ) :
    ∀ j < 3, ∀ x y, 0 ≤ wOf W α γ₀ γ₁ β j x y := fun j _ x y => by
  unfold wOf
  split_ifs <;> exact hW _ _ _

/-- **The face sum of a square with three loaded edges against the index form.** -/
theorem faceP_le_faceSum {Li : Fin 2 → Finset ℕ} (hLi : ∀ j, (Li j).card = 3)
    {α γ₀ γ₁ β : Fin 3 → ℕ} (hγ₀ : Function.Injective γ₀) (hγ₁ : Function.Injective γ₁)
    (hγ₀m : ∀ s, γ₀ s ∈ Li 0) (hγ₁m : ∀ t, γ₁ t ∈ Li 1) {W : Fin 3 → ℕ → ℕ → ℝ}
    (hW : ∀ j c d, 0 ≤ W j c d) (a b : Fin 3) :
    faceP (patOf α γ₀ γ₁ β) (wOf W α γ₀ γ₁ β) a b ≤ faceSum Li (fun _ _ => 1) W (α a) (β b) := by
  rw [faceSum_two, sum_enum (hLi 0) hγ₀ hγ₀m]
  simp only [sum_enum (hLi 1) hγ₁ hγ₁m]
  unfold faceP
  refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => ?_
  simp only [wOf, ite_true, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_false]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (hW _ _ _) (hW _ _ _)) (hW _ _ _)

theorem edgeOK_wOf {c : ℕ} {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} {W : Fin 3 → ℕ → ℕ → ℝ}
    (hW : ∀ j c d, 0 ≤ W j c d) {N : Fin 3 → ℝ}
    (h0 : sqClass (dig 2 c 0) Lu (Li 0) (W 0) (N 0))
    (h1 : sqClass (dig 2 c 1) (Li 0) (Li 1) (W 1) (N 1))
    (h2 : sqClass (dig 2 c 2) (Li 1) Lv (W 2) (N 2)) {α γ₀ γ₁ β : Fin 3 → ℕ}
    (hα : Function.Injective α) (hγ₀ : Function.Injective γ₀) (hγ₁ : Function.Injective γ₁)
    (hβ : Function.Injective β) (hαm : ∀ a, α a ∈ Lu) (hγ₀m : ∀ s, γ₀ s ∈ Li 0)
    (hγ₁m : ∀ t, γ₁ t ∈ Li 1) (hβm : ∀ b, β b ∈ Lv) :
    ∀ j < 3, EdgeOK (modesOf c j) (patE (patOf α γ₀ γ₁ β) j) (wOf W α γ₀ γ₁ β j) (nOf N j) := by
  intro j hj
  rw [modesOf_eq]
  interval_cases j
  · exact edgeOK_of_sqClass (hW 0) h0 hα hγ₀ hαm hγ₀m
  · exact edgeOK_of_sqClass (hW 1) h1 hγ₀ hγ₁ hγ₀m hγ₁m
  · exact edgeOK_of_sqClass (hW 2) h2 hγ₁ hβ hγ₁m hβm

theorem nOf_pos {N : Fin 3 → ℝ} (hN : ∀ j, 0 < N j) : ∀ j < 3, 0 < nOf N j := fun j _ => by
  unfold nOf
  split_ifs <;> exact hN _

/-! ### The list-level theorems -/

/-- **A square with three loaded path edges in the classes of a run has the hexagon bound at
its root edge**, given the hexagon property for the 52 patterns. -/
theorem sq_hex_of_good {c tn td : ℕ}
    (hgood : ∀ q, q < SqData.qs.length → GoodH (modesOf c) tn td (patOfCode (SqData.qs.getD q 0)))
    {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    {W : Fin 3 → ℕ → ℕ → ℝ} (hW : ∀ j c d, 0 ≤ W j c d) {N : Fin 3 → ℝ} (hN : ∀ j, 0 < N j)
    (h0 : sqClass (dig 2 c 0) Lu (Li 0) (W 0) (N 0))
    (h1 : sqClass (dig 2 c 1) (Li 0) (Li 1) (W 1) (N 1))
    (h2 : sqClass (dig 2 c 2) (Li 1) Lv (W 2) (N 2)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) W) (N 0 * N 1 * N 2 * tn / td) := by
  refine hex_of_idx_perm fun α β hα hβ hαm hβm hal => ?_
  obtain ⟨π, hπ, γ₀, γ₁, hγ₀, hγ₁, hγ₀m, hγ₁m, hG⟩ :=
    sq_frame (fun P Q h hq => GoodH.mono h hq) hgood hLv hLi hα hβ hβm hal
  refine ⟨π, hπ, ?_⟩
  have key := hG _ _ (nOf_pos hN) (edgeOK_wOf hW h0 h1 h2 (hα.comp hπ.1) hγ₀ hγ₁ (hβ.comp hπ.1)
    (fun a => hαm _) hγ₀m hγ₁m fun b => hβm _)
  simp only [nOf, ite_true, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    ite_false] at key
  refine key.trans (Finset.prod_le_prod₀ (fun k _ => faceP_nonneg (wOf_nonneg hW _ _ _ _) _ _)
    fun k _ => ?_)
  exact faceP_le_faceSum hLi hγ₀ hγ₁ hγ₀m hγ₁m hW _ _

/-- **A square with three loaded path edges in the classes of a run, closed by its root edge,
has the closing count**, given the closing property for the 52 patterns. -/
theorem sq_close_of_good {c tn td : ℕ}
    (hgood : ∀ q, q < SqData.qs.length → GoodC (modesOf c) tn td (patOfCode (SqData.qs.getD q 0)))
    {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ} (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3)
    {W : Fin 3 → ℕ → ℕ → ℝ} (hW : ∀ j c d, 0 ≤ W j c d) {N : Fin 3 → ℝ} (hN : ∀ j, 0 < N j)
    (h0 : sqClass (dig 2 c 0) Lu (Li 0) (W 0) (N 0))
    (h1 : sqClass (dig 2 c 1) (Li 0) (Li 1) (W 1) (N 1))
    (h2 : sqClass (dig 2 c 2) (Li 1) Lv (W 2) (N 2)) :
    N 0 * N 1 * N 2 * tn / td
      ≤ ∑ x ∈ Lu, ∑ y ∈ Lv, if x = y then 0 else faceSum Li (fun _ _ => 1) W x y := by
  obtain ⟨α, hα, hαm⟩ := exists_enum hLu
  obtain ⟨β, hβ, hβm, hβa⟩ := exists_aligned hLv hα
  have hal : ∀ a b, α a = β b → a = b := fun a b e => hβa b a e.symm
  obtain ⟨π, hπ, γ₀, γ₁, hγ₀, hγ₁, hγ₀m, hγ₁m, hG⟩ :=
    sq_frame (fun P Q h hq => GoodC.mono h hq) hgood hLv hLi hα hβ hβm hal
  have key := hG _ _ (nOf_pos hN) (edgeOK_wOf hW h0 h1 h2 (hα.comp hπ.1) hγ₀ hγ₁ (hβ.comp hπ.1)
    (fun a => hαm _) hγ₀m hγ₁m fun b => hβm _)
  simp only [nOf, ite_true, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    ite_false] at key
  refine key.trans ?_
  calc _ ≤ ∑ a, ∑ b, (if α (π a) = β (π b) then 0
        else faceSum Li (fun _ _ => 1) W (α (π a)) (β (π b))) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        simp only [patOf]
        by_cases h : α (π a) = β (π b)
        · simp [h]
        · simp only [h, decide_false, Bool.false_eq_true, ite_false]
          exact faceP_le_faceSum hLi hγ₀ hγ₁ hγ₀m hγ₁m hW _ _
    _ = _ := by
        rw [sum_enum hLu (hα.comp hπ.1) (fun a => hαm _)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sum_enum hLv (hβ.comp hπ.1) (fun b => hβm _)]
        rfl

end Outerplanar.SqMulti
