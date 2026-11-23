/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.TagBuilt

/-!
# Graphs built by ears and pendant edges under a system of profile classes

The graph induction of `Outerplanar/TagBuilt.lean` with a third step: a **pendant edge** `vw` at a
vertex `v` of the part built so far. This is how a new block starts at a cut vertex. What will
hang on `vw` (the new block and everything beyond it) is summed over the colour of `w`; the
result is a vertex profile at `v`, which is moved onto an edge `vy` at `v` already built. The
demand `t` carried by `vy` is split into a demand `t₀` on `vy` and a demand `t₁` on `vw`.

* `ClassSys.VertexSound t t₀ t₁` — profiles of the classes `t₀` on `vy` and `t₁` on `vw`, and a
  `plain` profile on `wv`, give a profile of class `t` on `vy`, with the constant
  `A₀ · 2 A₁ A₂` (the factor `2` is the ordinary count for the colour of `w`).
* `TagBuiltV R rule glue vrule S tg` — built from an edge by ears and pendant edges.
* **`ecc_three_of_tagBuiltV`** — sound rules give 3-ECC.

Part of the formalization of the seven-even-face theorem with cut vertices (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`, another AI session of this
repository's collaboration); formalized by Claude.
-/

namespace Outerplanar

open Finset

namespace ClassSys

variable (R : ClassSys)

/-- The demand `t` on `vy` is met by the demands `t₀` on `vy` and `t₁` on a new pendant edge
`vw`. -/
def VertexSound (t t₀ t₁ : R.Tag) : Prop :=
  ∀ (Lv Ly Lw : Finset ℕ), Lv.card = 3 → Ly.card = 3 → Lw.card = 3 →
    ∀ (W X X' : ℕ → ℕ → ℝ), (∀ c d, 0 ≤ W c d) → (∀ c d, 0 ≤ X c d) → (∀ c d, 0 ≤ X' c d) →
    ∀ (A A₁ A₂ : ℝ), 0 < A → 0 < A₁ → 0 < A₂ →
    R.cls t₀ Lv Ly W A → R.cls t₁ Lv Lw X A₁ → R.cls R.plain Lw Lv X' A₂ →
    R.cls t Lv Ly (fun c d => W c d * ∑ e ∈ Lw, X c e * X' e c) (A * (2 * A₁ * A₂))

end ClassSys

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The tags after a pendant edge `vw` at `v`, with the demand on `vy` split. -/
def pendTags (R : ClassSys) (tg : V → V → R.Tag) (v y w : V) (t₀ t₁ : R.Tag) :
    V → V → R.Tag := fun a b =>
  if a = v ∧ b = y then t₀ else if a = v ∧ b = w then t₁
  else if a = w ∧ b = v then R.plain else tg a b

/-- Built from an edge by ears and pendant edges, following the rules. -/
inductive TagBuiltV (R : ClassSys) (rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop)
    (glue : R.Tag → R.Tag → Prop) (vrule : R.Tag → R.Tag → R.Tag → Prop) :
    Finset V → (V → V → R.Tag) → Prop
  | edge (u v : V) (huv : G.Adj u v) (t₁ t₂ : R.Tag) (hg : glue t₁ t₂) :
      TagBuiltV R rule glue vrule {u, v} (edgeTags R u v t₁ t₂)
  | face (S : Finset V) (tg : V → V → R.Tag) (m : ℕ) (u v : V) (x : Fin m → V)
      (he : IsEar G S u v x) (τ : Fin (m + 1) → R.Tag) (hr : rule (tg u v) m τ)
      (hS : TagBuiltV R rule glue vrule S tg) :
      TagBuiltV R rule glue vrule (S ∪ univ.image x) (earTags R S tg u v x τ)
  | pendant (S : Finset V) (tg : V → V → R.Tag) (v y w : V) (hv : v ∈ S) (hy : y ∈ S)
      (hvy : G.Adj v y) (hw : w ∉ S) (hwv : G.Adj w v) (huniq : ∀ z ∈ S, G.Adj w z → z = v)
      (t₀ t₁ : R.Tag) (hr : vrule (tg v y) t₀ t₁) (hS : TagBuiltV R rule glue vrule S tg) :
      TagBuiltV R rule glue vrule (insert w S) (pendTags R tg v y w t₀ t₁)

variable {G}

theorem prod_update_one {ι : Type*} [DecidableEq ι] {s : Finset ι} {q : ι} (hq : q ∈ s)
    (g : ι → ℝ) (k : ℝ) :
    ∏ p ∈ s, (if p = q then g q * k else g p) = (∏ p ∈ s, g p) * k := by
  rw [← Finset.mul_prod_erase s _ hq, ← Finset.mul_prod_erase s g hq]
  simp only [↓reduceIte]
  have : ∏ p ∈ s.erase q, (if p = q then g q * k else g p) = ∏ p ∈ s.erase q, g p :=
    Finset.prod_congr rfl fun p hp => by simp only [Finset.ne_of_mem_erase hp, ↓reduceIte]
  rw [this]
  ring

/-- **A pendant edge.** -/
theorem tagBound_pendant {R : ClassSys} {S : Finset V} {tg : V → V → R.Tag} {v y w : V}
    (hv : v ∈ S) (hy : y ∈ S) (hvy : G.Adj v y) (hw : w ∉ S) (hwv : G.Adj w v)
    (huniq : ∀ z ∈ S, G.Adj w z → z = v) {t₀ t₁ : R.Tag} (hr : R.VertexSound (tg v y) t₀ t₁)
    (ih : TagBound G R S tg) : TagBound G R (insert w S) (pendTags R tg v y w t₀ t₁) := by
  intro L Ω A hcard hΩ hA hinv
  have hwm : w ∈ insert w S := mem_insert_self w S
  have hvm : v ∈ insert w S := mem_insert_of_mem hv
  have hym : y ∈ insert w S := mem_insert_of_mem hy
  have hwv' : w ≠ v := fun e => hw (e ▸ hv)
  have hwy : w ≠ y := fun e => hw (e ▸ hy)
  have hcl0 : R.cls t₀ (L v) (L y) (Ω v y) (A v y) := by
    have := hinv v hvm y hym hvy
    simpa [pendTags] using this
  have hcl1 : R.cls t₁ (L v) (L w) (Ω v w) (A v w) := by
    have := hinv v hvm w hwm hwv.symm
    simpa [pendTags, hwy] using this
  have hcl2 : R.cls R.plain (L w) (L v) (Ω w v) (A w v) := by
    have := hinv w hwm v hvm hwv
    simpa [pendTags, hwv'] using this
  set F : ℕ → ℝ := fun c => ∑ e ∈ L w, Ω v w c e * Ω w v e c with hF
  set Ω'' : V → V → ℕ → ℕ → ℝ :=
    fun a b => if a = v ∧ b = y then fun c d => Ω v y c d * F c else Ω a b with hΩ''
  set A'' : V → V → ℝ := fun a b => if a = v ∧ b = y then A v y * (2 * A v w * A w v) else A a b
    with hA''
  have hF0 : ∀ c, 0 ≤ F c := fun c => Finset.sum_nonneg fun e _ =>
    mul_nonneg (hΩ _ _ _ _) (hΩ _ _ _ _)
  have key := ih L Ω'' A'' (fun x hx => hcard x (mem_insert_of_mem hx))
    (fun a b c d => by
      simp only [hΩ'']; split_ifs
      · exact mul_nonneg (hΩ _ _ _ _) (hF0 c)
      · exact hΩ _ _ _ _)
    (fun a b => by
      simp only [hA'']; split_ifs
      · exact mul_pos (hA _ _) (mul_pos (mul_pos two_pos (hA _ _)) (hA _ _))
      · exact hA _ _)
    (fun a ha b hb hab => by
      by_cases hvy' : a = v ∧ b = y
      · obtain ⟨rfl, rfl⟩ := hvy'
        simp only [hΩ'', hA'', and_self, ite_true]
        exact hr (L a) (L b) (L w) (hcard a hvm) (hcard b hym) (hcard w hwm) _ _ _
          (hΩ _ _) (hΩ _ _) (hΩ _ _) _ _ _ (hA _ _) (hA _ _) (hA _ _) hcl0 hcl1 hcl2
      · have haw : a ≠ w := fun e => hw (e ▸ ha)
        have hbw : b ≠ w := fun e => hw (e ▸ hb)
        have := hinv a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
        simp only [pendTags, hvy', ite_false, hbw, and_false, haw, false_and] at this
        simp only [hΩ'', hA'', hvy', ite_false]
        exact this)
  have hvyp : (v, y) ∈ adjPairs G S := (mem_adjPairs G).mpr ⟨hv, hy, hvy⟩
  have hZ : ZG G (insert w S) L (fun _ _ => 1) Ω = ZG G S L (fun _ _ => 1) Ω'' := by
    rw [ZG_insert_pendant G hw hv hwv huniq, hΩ'', ZG_update_pair G hvyp L _ Ω fun c _ => F c]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [mul_one, hF]
  have hconst := ZG_const_insert_pendant G 3 hw hv hwv huniq
  have hprod := prod_adjPairs_insert_pendant G hw hv hwv huniq (fun p => A p.1 p.2)
  have hprod'' : ∏ p ∈ adjPairs G S, A'' p.1 p.2
      = (∏ p ∈ adjPairs G S, A p.1 p.2) * (2 * A v w * A w v) := by
    have := prod_update_one hvyp (fun p => A p.1 p.2) (2 * A v w * A w v)
    rw [← this]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [hA'']
    by_cases h : p.1 = v ∧ p.2 = y
    · have hp : p = (v, y) := Prod.ext h.1 h.2
      simp [hp]
    · have hp : p ≠ (v, y) := fun e => h ⟨by rw [e], by rw [e]⟩
      simp only [h, ite_false, hp]
  rw [hZ, hconst, hprod]
  rw [hprod''] at key
  have e : ZG G S (fun _ => range 3) (fun _ _ => 1) neProfile * (((3 : ℕ) : ℝ) - 1)
        * (A w v * (A v w * ∏ p ∈ adjPairs G S, A p.1 p.2))
      = ZG G S (fun _ => range 3) (fun _ _ => 1) neProfile
        * ((∏ p ∈ adjPairs G S, A p.1 p.2) * (2 * A v w * A w v)) := by
    push_cast; ring
  rw [e]
  exact key

theorem tagBound_of_tagBuiltV {R : ClassSys}
    {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop} {glue : R.Tag → R.Tag → Prop}
    {vrule : R.Tag → R.Tag → R.Tag → Prop}
    (hsound : ∀ t m τ, rule t m τ → R.RuleSound t m τ)
    (hglue : ∀ t₁ t₂, glue t₁ t₂ → R.GlueSound t₁ t₂)
    (hvert : ∀ t t₀ t₁, vrule t t₀ t₁ → R.VertexSound t t₀ t₁) {S : Finset V}
    {tg : V → V → R.Tag} (h : TagBuiltV G R rule glue vrule S tg) : TagBound G R S tg := by
  induction h with
  | edge u v huv t₁ t₂ hg => exact tagBound_edge huv (hglue _ _ hg)
  | face S tg m u v x he τ hr hS ih => exact tagBound_face hsound he hr ih
  | pendant S tg v y w hv hy hvy hw hwv huniq t₀ t₁ hr hS ih =>
    exact tagBound_pendant hv hy hvy hw hwv huniq (hvert _ _ _ hr) ih

variable (G)

/-- **Graphs built by ears and pendant edges with sound rules are 3-ECC.** -/
theorem ecc_three_of_tagBuiltV {R : ClassSys}
    {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop} {glue : R.Tag → R.Tag → Prop}
    {vrule : R.Tag → R.Tag → R.Tag → Prop}
    (hsound : ∀ t m τ, rule t m τ → R.RuleSound t m τ)
    (hglue : ∀ t₁ t₂, glue t₁ t₂ → R.GlueSound t₁ t₂)
    (hvert : ∀ t t₀ t₁, vrule t t₀ t₁ → R.VertexSound t t₀ t₁) {tg : V → V → R.Tag}
    (h : TagBuiltV G R rule glue vrule univ tg) : G.ECCAt 3 := by
  intro L hL
  have key := tagBound_of_tagBuiltV hsound hglue hvert h L neProfile (fun _ _ => 1)
    (fun x _ => hL x) (fun _ _ c d => by unfold neProfile; split_ifs <;> norm_num)
    (fun _ _ => one_pos)
    (fun a _ b _ _ => R.of_dom _ _ _ _ _ zero_le_one (dominant_ne (L a) (L b)))
  rw [Finset.prod_const_one, mul_one, ZG_univ_eq_col, ZG_univ_eq_col] at key
  have key' : (G.colConst 3 : ℝ) ≤ (G.col L : ℝ) := key
  exact_mod_cast key'

end Outerplanar
