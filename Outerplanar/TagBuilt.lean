/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.OneLoad

/-!
# Graphs built by ears under a system of profile classes

A generic form of the graph induction of `Outerplanar/OneLoad.lean`, in which the invariant
carried on an edge is not fixed in advance but chosen from a *class system*. Proving a new
theorem of the form "every graph built by such-and-such ears is 3-ECC" then amounts to giving
the classes and proving single-face lemmas. There is no further graph-level work.

* `ClassSys` — a type of tags, a class `cls t S T W A` for each tag (profile `W` on the lists
  `S`, `T` of the ends, with constant `A`), and a tag `plain` whose class consists of `Dominant`
  profiles. Every class contains the `Dominant` profiles and is closed under multiplication
  by a `Dominant` profile.
* `ClassSys.RuleSound t m τ` — a face with `m` interior vertices whose path edges carry
  profiles of the classes `τ j` gives a profile of class `t` on its root edge.
* `ClassSys.GlueSound t₁ t₂` — two profiles of classes `t₁` and `t₂` on the two sides of an
  edge give at least `6 A₁ A₂` colourings of the edge.
* `TagBuilt R rule glue S tg` — the vertex set `S` with tags `tg` on ordered pairs is built from
  an edge (two tags satisfying `glue`) by ears. An ear on `(u, v)` follows a rule
  `rule (tg u v) m τ`; afterwards `(u, v)` is `plain` (what hangs on it has been built), the
  path edge `j` carries `τ j` in the direction of the path and `plain` in the other.
* **`ecc_three_of_tagBuilt`** — if every rule is sound and the glue is sound, a graph built
  on all its vertices is 3-ECC.

This is part of the formalization of the six-even-face theorem (research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`); its plan is
`ai_research_notes/OUTERPLANAR_SIX_EVEN_LEAN_PLAN.md`.
-/

namespace Outerplanar

open Finset

/-- A system of profile classes for three colours. -/
structure ClassSys where
  /-- The tags. -/
  Tag : Type
  /-- The tag of an edge on which nothing more is built. -/
  plain : Tag
  /-- The class of a tag: a profile on two lists with a constant. -/
  cls : Tag → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  /-- Every class contains the `Dominant` profiles. -/
  of_dom : ∀ t S T W A, 0 ≤ A → Dominant S T W A → cls t S T W A
  /-- The plain class is the `Dominant` class. -/
  dom_of_plain : ∀ S T W A, cls plain S T W A → Dominant S T W A
  /-- Every class is closed under multiplication by a `Dominant` profile. -/
  mul_dom : ∀ t S T W W' A A', 0 ≤ A → 0 ≤ A' → (∀ c d, 0 ≤ W c d) → (∀ c d, 0 ≤ W' c d) →
    Dominant S T W' A' → cls t S T W A → cls t S T (fun c d => W' c d * W c d) (A' * A)

namespace ClassSys

variable (R : ClassSys)

/-- A face with `m` interior vertices, path edges of the classes `τ j`, gives class `t`. -/
def RuleSound (t : R.Tag) (m : ℕ) (τ : Fin (m + 1) → R.Tag) : Prop :=
  ∀ (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ), Lu.card = 3 → Lv.card = 3 →
    (∀ j, (Li j).card = 3) → ∀ (E : Fin (m + 1) → ℕ → ℕ → ℝ), (∀ j c d, 0 ≤ E j c d) →
    ∀ (A : Fin (m + 1) → ℝ), (∀ j, 0 < A j) →
    (∀ j, R.cls (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) →
    R.cls t Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j)

/-- Two sides of an edge of the classes `t₁`, `t₂` give at least `6 A A'` colourings. -/
def GlueSound (t₁ t₂ : R.Tag) : Prop :=
  ∀ (S T : Finset ℕ) (W W' : ℕ → ℕ → ℝ) (A A' : ℝ), S.card = 3 → T.card = 3 →
    (∀ c d, 0 ≤ W c d) → (∀ c d, 0 ≤ W' c d) → 0 < A → 0 < A' →
    R.cls t₁ S T W A → R.cls t₂ T S W' A' → 6 * (A * A') ≤ ∑ d ∈ T, ∑ c ∈ S, W' d c * W c d

end ClassSys

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Tags -/

/-- The tags of a single edge `uv`. -/
def edgeTags (R : ClassSys) (u v : V) (t₁ t₂ : R.Tag) : V → V → R.Tag := fun a b =>
  if a = u ∧ b = v then t₁ else if a = v ∧ b = u then t₂ else R.plain

/-- The tags after an ear on `(u, v)` with path tags `τ`. -/
noncomputable def earTags (R : ClassSys) (S : Finset V) (tg : V → V → R.Tag) {m : ℕ} (u v : V)
    (x : Fin m → V) (τ : Fin (m + 1) → R.Tag) : V → V → R.Tag := fun a b =>
  if a = u ∧ b = v then R.plain
  else if h : ∃ j : Fin (m + 1), earPath u v x j.castSucc = a ∧ earPath u v x j.succ = b then
    τ h.choose
  else if a ∈ S ∧ b ∈ S then tg a b else R.plain

/-- `TagBuilt R rule glue S tg`: the induced subgraph on `S` is built from an edge by ears,
following the rules, with the tags `tg`. -/
inductive TagBuilt (R : ClassSys) (rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop)
    (glue : R.Tag → R.Tag → Prop) : Finset V → (V → V → R.Tag) → Prop
  | edge (u v : V) (huv : G.Adj u v) (t₁ t₂ : R.Tag) (hg : glue t₁ t₂) :
      TagBuilt R rule glue {u, v} (edgeTags R u v t₁ t₂)
  | face (S : Finset V) (tg : V → V → R.Tag) (m : ℕ) (u v : V) (x : Fin m → V)
      (he : IsEar G S u v x) (τ : Fin (m + 1) → R.Tag) (hr : rule (tg u v) m τ)
      (hS : TagBuilt R rule glue S tg) :
      TagBuilt R rule glue (S ∪ univ.image x) (earTags R S tg u v x τ)

/-- The weighted lower bound on `S` with tags `tg`. -/
def TagBound (R : ClassSys) (S : Finset V) (tg : V → V → R.Tag) : Prop :=
  ∀ (L : V → Finset ℕ) (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ),
    (∀ x ∈ S, (L x).card = 3) → (∀ x y c d, 0 ≤ Ω x y c d) → (∀ x y, 0 < A x y) →
    (∀ a ∈ S, ∀ b ∈ S, G.Adj a b → R.cls (tg a b) (L a) (L b) (Ω a b) (A a b)) →
    ZG G S (fun _ => range 3) (fun _ _ => 1) neProfile * ∏ p ∈ adjPairs G S, A p.1 p.2
      ≤ ZG G S L (fun _ _ => 1) Ω

variable {G}

section Tags

variable {R : ClassSys} {S : Finset V} {tg : V → V → R.Tag} {m : ℕ} {u v : V} {x : Fin m → V}
  {τ : Fin (m + 1) → R.Tag}

omit [Fintype V] in
theorem earTags_root : earTags R S tg u v x τ u v = R.plain := by
  simp [earTags]

theorem earTags_fwd (he : IsEar G S u v x) (j : Fin (m + 1)) :
    earTags R S tg u v x τ (earPath u v x j.castSucc) (earPath u v x j.succ) = τ j := by
  have hnot := he.earPath_not_both j
  have h1 : ¬ (earPath u v x j.castSucc = u ∧ earPath u v x j.succ = v) := by
    rintro ⟨e1, e2⟩
    exact hnot ⟨by rw [e1]; exact he.hu, by rw [e2]; exact he.hv⟩
  have hex : ∃ j' : Fin (m + 1), earPath u v x j'.castSucc = earPath u v x j.castSucc ∧
      earPath u v x j'.succ = earPath u v x j.succ := ⟨j, rfl, rfl⟩
  simp only [earTags, h1, ite_false, dite_eq_left hex]
  congr 1
  exact Fin.castSucc_injective _ (he.earPath_injective hex.choose_spec.1)

theorem earTags_bwd (he : IsEar G S u v x) (j : Fin (m + 1)) :
    earTags R S tg u v x τ (earPath u v x j.succ) (earPath u v x j.castSucc) = R.plain := by
  have hnot := he.earPath_not_both j
  have h1 : ¬ (earPath u v x j.succ = u ∧ earPath u v x j.castSucc = v) := by
    rintro ⟨e1, e2⟩
    exact hnot ⟨by rw [e2]; exact he.hv, by rw [e1]; exact he.hu⟩
  have hex : ¬ ∃ j' : Fin (m + 1), earPath u v x j'.castSucc = earPath u v x j.succ ∧
      earPath u v x j'.succ = earPath u v x j.castSucc := by
    rintro ⟨j', e1, e2⟩
    have a1 := congrArg Fin.val (he.earPath_injective e1)
    have a2 := congrArg Fin.val (he.earPath_injective e2)
    simp only [Fin.val_castSucc, Fin.val_succ] at a1 a2
    omega
  have h3 : ¬ (earPath u v x j.succ ∈ S ∧ earPath u v x j.castSucc ∈ S) :=
    fun h => hnot ⟨h.2, h.1⟩
  simp only [earTags, h1, ite_false, dite_eq_right hex, h3]

theorem earTags_old (he : IsEar G S u v x) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (hab : ¬ (a = u ∧ b = v)) : earTags R S tg u v x τ a b = tg a b := by
  have hex : ¬ ∃ j : Fin (m + 1), earPath u v x j.castSucc = a ∧ earPath u v x j.succ = b := by
    rintro ⟨j, rfl, rfl⟩
    exact he.earPath_not_both j ⟨ha, hb⟩
  simp only [earTags, hab, ite_false, dite_eq_right hex, ha, hb, and_self, ite_true]

end Tags

/-! ### The base edge -/

theorem tagBound_edge {R : ClassSys} {u v : V} (huv : G.Adj u v) {t₁ t₂ : R.Tag}
    (hg : R.GlueSound t₁ t₂) : TagBound G R {u, v} (edgeTags R u v t₁ t₂) := by
  intro L Ω A hcard hΩ hA hinv
  have huv' : u ≠ v := huv.ne
  have hu : u ∉ ({v} : Finset V) := by simpa using huv'
  have hv : v ∈ ({v} : Finset V) := mem_singleton_self v
  have huniq : ∀ z ∈ ({v} : Finset V), G.Adj u z → z = v := fun z hz _ => mem_singleton.mp hz
  have hve : ({v} : Finset V) = insert v ∅ := by simp
  have hiso : ∀ z ∈ (∅ : Finset V), ¬ G.Adj v z := by simp
  have hconst : ZG G {u, v} (fun _ => range 3) (fun _ _ => 1) neProfile = 6 := by
    show ZG G (insert u {v}) (fun _ => range 3) (fun _ _ => 1) neProfile = 6
    rw [ZG_const_insert_pendant G 3 hu hv huv huniq, hve,
      ZG_const_insert_isolated G 3 (notMem_empty v) hiso, ZG_empty]
    norm_num
  have hprod : ∏ p ∈ adjPairs G {u, v}, A p.1 p.2 = A u v * A v u := by
    show ∏ p ∈ adjPairs G (insert u {v}), A p.1 p.2 = A u v * A v u
    rw [prod_adjPairs_insert_pendant G hu hv huv huniq (fun p => A p.1 p.2), hve,
      adjPairs_insert_isolated G hiso]
    simp [adjPairs]
  have hZ : ZG G {u, v} L (fun _ _ => 1) Ω
      = ∑ d ∈ L v, ∑ c ∈ L u, Ω v u d c * Ω u v c d := by
    show ZG G (insert u {v}) L (fun _ _ => 1) Ω = _
    rw [ZG_insert_pendant G hu hv huv huniq,
      ← ZG_update_vertex G hv L (fun _ _ => 1) Ω
        (fun d => ∑ c ∈ L u, Ω v u d c * Ω u v c d * 1)]
    simp only [hve]
    rw [ZG_insert_isolated G (notMem_empty v) hiso, ZG_empty]
    simp
  rw [hconst, hprod, hZ]
  have huS : u ∈ ({u, v} : Finset V) := by simp
  have hvS : v ∈ ({u, v} : Finset V) := by simp
  have h1 := hinv u huS v hvS huv
  have h2 := hinv v hvS u huS huv.symm
  have e1 : edgeTags R u v t₁ t₂ u v = t₁ := by simp [edgeTags]
  have e2 : edgeTags R u v t₁ t₂ v u = t₂ := by simp [edgeTags, Ne.symm huv']
  rw [e1] at h1
  rw [e2] at h2
  have := hg (L u) (L v) (Ω u v) (Ω v u) (A u v) (A v u) (hcard u huS) (hcard v hvS)
    (hΩ u v) (hΩ v u) (hA u v) (hA v u) h1 h2
  linarith

/-! ### Adding a face -/

theorem tagBound_face {R : ClassSys} {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop}
    (hsound : ∀ t m τ, rule t m τ → R.RuleSound t m τ) {S : Finset V} {tg : V → V → R.Tag}
    {m : ℕ} {u v : V} {x : Fin m → V} (he : IsEar G S u v x) {τ : Fin (m + 1) → R.Tag}
    (hr : rule (tg u v) m τ) (ih : TagBound G R S tg) :
    TagBound G R (S ∪ univ.image x) (earTags R S tg u v x τ) := by
  intro L Ω A hcard hΩ hA hinv
  have hxm : ∀ j, x j ∈ S ∪ univ.image x := fun j =>
    mem_union_right _ (mem_image_of_mem _ (mem_univ j))
  have hcu := hcard u (mem_union_left _ he.hu)
  have hcv := hcard v (mem_union_left _ he.hv)
  have hci : ∀ j, (L (x j)).card = 3 := fun j => hcard (x j) (hxm j)
  have hE0 : ∀ j c d, 0 ≤ earE Ω u v x j c d := fun j c d =>
    mul_nonneg (hΩ _ _ _ _) (hΩ _ _ _ _)
  have hApos : ∀ j : Fin (m + 1), 0 < A (earPath u v x j.castSucc) (earPath u v x j.succ)
      * A (earPath u v x j.succ) (earPath u v x j.castSucc) := fun j =>
    mul_pos (hA _ _) (hA _ _)
  -- the profiles of the path edges
  have hEj : ∀ j, R.cls (τ j) (pathList (L u) (L v) (fun j => L (x j)) j.castSucc)
      (pathList (L u) (L v) (fun j => L (x j)) j.succ) (earE Ω u v x j)
      (A (earPath u v x j.castSucc) (earPath u v x j.succ)
        * A (earPath u v x j.succ) (earPath u v x j.castSucc)) := by
    intro j
    rw [pathList_eq_earPath, pathList_eq_earPath]
    have hf := hinv _ (he.earPath_mem _) _ (he.earPath_mem _) (he.earPath_adj j)
    have hb := hinv _ (he.earPath_mem _) _ (he.earPath_mem _) (he.earPath_adj j).symm
    rw [earTags_fwd he] at hf
    rw [earTags_bwd he] at hb
    have hbd := (R.dom_of_plain _ _ _ _ hb).swap
    have := R.mul_dom _ _ _ _ _ _ _ (hA _ _).le (hA _ _).le (hΩ _ _) (fun c d => hΩ _ _ _ _)
      hbd hf
    have e : (fun c d => Ω (earPath u v x j.succ) (earPath u v x j.castSucc) d c
        * Ω (earPath u v x j.castSucc) (earPath u v x j.succ) c d) = earE Ω u v x j :=
      funext₂ fun c d => mul_comm _ _
    rw [e, mul_comm] at this
    exact this
  set C := faceConst3 m
      * ∏ j : Fin (m + 1), A (earPath u v x j.castSucc) (earPath u v x j.succ)
        * A (earPath u v x j.succ) (earPath u v x j.castSucc) with hCdef
  have hC : 0 < C :=
    mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hApos j)
  have hF := hsound _ _ _ hr (L u) (L v) (fun j => L (x j)) hcu hcv hci (earE Ω u v x) hE0 _
    hApos hEj
  have hF0 : ∀ c d, 0 ≤ faceSum (fun j => L (x j)) (fun _ _ => 1) (earE Ω u v x) c d :=
    faceSum_nonneg _ _ _ (fun j c _ => zero_le_one) hE0
  have huvm : (u, v) ∈ adjPairs G S := (mem_adjPairs G).mpr ⟨he.hu, he.hv, he.huv⟩
  have ih' := ih L
    (fun a b => if a = u ∧ b = v then fun c d => Ω u v c d
      * faceSum (fun j => L (x j)) (fun _ _ => 1) (earE Ω u v x) c d else Ω a b)
    (fun a b => if a = u ∧ b = v then A u v * C else A a b)
    (fun z hz => hcard z (mem_union_left _ hz))
    (by
      intro a b c d
      by_cases hab : a = u ∧ b = v
      · simp only [hab, and_self, ite_true]
        exact mul_nonneg (hΩ _ _ _ _) (hF0 c d)
      · simp only [hab, ite_false]
        exact hΩ _ _ _ _)
    (by
      intro a b
      by_cases hab : a = u ∧ b = v
      · simp only [hab, and_self, ite_true]
        exact mul_pos (hA _ _) hC
      · simp only [hab, ite_false]
        exact hA _ _)
    (by
      intro a ha b hb hadj
      have hold := hinv a (mem_union_left _ ha) b (mem_union_left _ hb) hadj
      by_cases hab : a = u ∧ b = v
      · obtain ⟨rfl, rfl⟩ := hab
        simp only [and_self, ite_true]
        rw [earTags_root] at hold
        exact R.mul_dom _ _ _ _ _ _ _ hC.le (hA _ _).le hF0 (hΩ _ _)
          (R.dom_of_plain _ _ _ _ hold) hF
      · simp only [hab, ite_false]
        rw [earTags_old he ha hb hab] at hold
        exact hold)
  rw [prod_adjPairs_update G huvm A, ZG_update_pair G huvm L _ Ω, ← he.ZG_eq] at ih'
  rw [he.ZG_const G (by norm_num : 1 ≤ 3), he.prod_adjPairs (fun p => A p.1 p.2)]
  refine le_of_eq_of_le ?_ ih'
  rw [hCdef]
  unfold faceConst3
  ring

/-! ### The theorem -/

theorem tagBound_of_tagBuilt {R : ClassSys}
    {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop} {glue : R.Tag → R.Tag → Prop}
    (hsound : ∀ t m τ, rule t m τ → R.RuleSound t m τ)
    (hglue : ∀ t₁ t₂, glue t₁ t₂ → R.GlueSound t₁ t₂) {S : Finset V} {tg : V → V → R.Tag}
    (h : TagBuilt G R rule glue S tg) : TagBound G R S tg := by
  induction h with
  | edge u v huv t₁ t₂ hg => exact tagBound_edge huv (hglue _ _ hg)
  | face S tg m u v x he τ hr hS ih => exact tagBound_face hsound he hr ih

variable (G)

/-- **Graphs built by sound rules are 3-ECC.** -/
theorem ecc_three_of_tagBuilt {R : ClassSys}
    {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop} {glue : R.Tag → R.Tag → Prop}
    (hsound : ∀ t m τ, rule t m τ → R.RuleSound t m τ)
    (hglue : ∀ t₁ t₂, glue t₁ t₂ → R.GlueSound t₁ t₂) {tg : V → V → R.Tag}
    (h : TagBuilt G R rule glue univ tg) : G.ECCAt 3 := by
  intro L hL
  have key := tagBound_of_tagBuilt hsound hglue h L neProfile (fun _ _ => 1)
    (fun x _ => hL x) (fun _ _ c d => by unfold neProfile; split_ifs <;> norm_num)
    (fun _ _ => one_pos)
    (fun a _ b _ _ => R.of_dom _ _ _ _ _ zero_le_one (dominant_ne (L a) (L b)))
  rw [Finset.prod_const_one, mul_one, ZG_univ_eq_col, ZG_univ_eq_col] at key
  have key' : (G.colConst 3 : ℝ) ≤ (G.col L : ℝ) := key
  exact_mod_cast key'

end Outerplanar
