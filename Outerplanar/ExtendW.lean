/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.TagBuiltW
import Outerplanar.SixEvenBuild

/-!
# Building one side of an edge of a block, with branches hanging at its vertices

The induction `extend` of `Outerplanar/SixEvenBuild.lean` for a block of a larger graph: a polygon
dissection `H` on `Fin N`, embedded by an injective `ψ` (adjacency of `G` between vertices of the
block is that of `H`), with a set `hang z ∋ ψ z` at each vertex `z`: everything of `G` that hangs
at `ψ z` away from the block. The sets `hang z` are pairwise disjoint, and a neighbour of `ψ z`
outside the block lies in `hang z`.

* `sideR ψ hang a b` — the region of the side `[a, b]`: its ends and everything hanging at its
  interior vertices.
* `childR ψ hang r j` — the region of the `j`-th child of the root face `r` of a side: the side
  `[r j, r (j + 1)]`, together with what hangs at `r j` when `r j` is an interior vertex of the
  root face (`j ≠ 0`). This is how the branches at the interior vertices of a face are assigned:
  to the path edge after them.
* `HangBuild R rule glue vrule tagR U x` — the hypothesis on a branch region `U` at `x`: whenever
  `x` is built and `U` is not, and an edge `(x, y)` carries the demand `tagR (X ∪ U)` for some `X`
  meeting `U` only in `x`, then `U` can be built so that `(x, y)` carries `tagR X`, the other
  demands unchanged.
* **`extendW`** — the side `[a, b]` of an edge whose ends are built and whose region is not, with
  demand `tagR (sideR a b)`, is built, provided the face rule holds at the root face of every
  side inside it (with the children's demands `tagR (childR r j)`) and every branch at an
  interior vertex is buildable.

The tags are functions of the region only (`tagR : Finset V → R.Tag`); the face rules, vertex
rules and the regions' contents are the business of the instance.

Part of the formalization of the seven-even-face theorem with cut vertices (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`); formalized by Claude.
-/

namespace Outerplanar

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {N : ℕ} {H : SimpleGraph (Fin N)}

/-! ### Regions -/

/-- The region of the side `[a, b]`: its ends and what hangs at its interior vertices. -/
def sideR (ψ : Fin N → V) (hang : Fin N → Finset V) (a b : Fin N) : Finset V :=
  insert (ψ a) (insert (ψ b) ((Ioo a b).biUnion hang))

/-- The region of the `j`-th child of the root face `r`. -/
def childR (ψ : Fin N → V) (hang : Fin N → Finset V) {m : ℕ} (r : Fin (m + 2) → Fin N)
    (j : Fin (m + 1)) : Finset V :=
  if j.val = 0 then sideR ψ hang (r j.castSucc) (r j.succ)
  else sideR ψ hang (r j.castSucc) (r j.succ) ∪ hang (r j.castSucc)

theorem mem_sideR {ψ : Fin N → V} {hang : Fin N → Finset V} {a b : Fin N} {v : V} :
    v ∈ sideR ψ hang a b ↔ v = ψ a ∨ v = ψ b ∨ ∃ z, a < z ∧ z < b ∧ v ∈ hang z := by
  simp only [sideR, mem_insert, mem_biUnion, mem_Ioo, and_assoc]

/-- The hanging sets of a block: `hang z` contains `ψ z`, they are pairwise disjoint, and a
neighbour of `ψ z` outside the block hangs at `z`. -/
structure HangOK (G : SimpleGraph V) (ψ : Fin N → V) (hang : Fin N → Finset V) : Prop where
  self : ∀ z, ψ z ∈ hang z
  disj : ∀ z z' v, v ∈ hang z → v ∈ hang z' → z = z'
  nbr : ∀ z y, G.Adj (ψ z) y → (∃ i, ψ i = y) ∨ y ∈ hang z

theorem HangOK.idx {ψ : Fin N → V} {hang : Fin N → Finset V} (h : HangOK G ψ hang) {i z : Fin N}
    (hi : ψ i ∈ hang z) : i = z := h.disj i z _ (h.self i) hi

/-- A buildable branch region `U` at `x`. -/
def HangBuild (G : SimpleGraph V) [DecidableRel G.Adj] (R : ClassSys)
    (rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop) (glue : R.Tag → R.Tag → Prop)
    (vrule : R.Tag → R.Tag → R.Tag → Prop) (tagR : Finset V → R.Tag) (U : Finset V) (x : V) :
    Prop :=
  ∀ (T : Finset V) (tg : V → V → R.Tag), TagBuiltW G R rule glue vrule T tg → x ∈ T →
    (∀ v ∈ U, v ∈ T → v = x) → ∀ y ∈ T, G.Adj x y → ∀ X : Finset V, x ∈ X →
    (∀ v ∈ X, v ∈ U → v = x) → tg x y = tagR (X ∪ U) →
    ∃ tg', TagBuiltW G R rule glue vrule (T ∪ U) tg' ∧ tg' x y = tagR X ∧
      ∀ p ∈ T, ∀ q ∈ T, ¬ (p = x ∧ q = y) → tg' p q = tg p q

/-! ### The root face is an ear -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **The root face is an ear** on the edge `(a, b)` of a set meeting `[a, b]` in its ends,
whose interior vertices have no neighbour in the set outside the block. -/
theorem isEar_rootW (hH : IsDissection H) (ψ : Fin N → V) (hψ : Function.Injective ψ)
    (hGH : ∀ i j, G.Adj (ψ i) (ψ j) ↔ H.Adj i j) {a b : Fin N} (hadj : H.Adj a b) (hab : a < b)
    {m : ℕ} {r : Fin (m + 2) → Fin N} (he : RootEnum H a b m r) {T : Finset V} (ha : ψ a ∈ T)
    (hb : ψ b ∈ T) (hT : ∀ i, a < i → i < b → ψ i ∉ T)
    (hnb : ∀ k, a < k → k < b → ∀ y ∈ T, G.Adj (ψ k) y → ∃ i, ψ i = y) :
    IsEar G T (ψ a) (ψ b) (earVerts ψ r) := by
  have hm1 := he.one_le
  have hin : ∀ j : Fin m, a < r ⟨j.val + 1, by omega⟩ ∧ r ⟨j.val + 1, by omega⟩ < b := fun j => by
    constructor
    · rw [← he.first]; exact he.mono (show (0 : ℕ) < j.val + 1 by omega)
    · rw [← he.last]; exact he.mono (show j.val + 1 < m + 1 by omega)
  have hidx : ∀ k l : Fin (m + 2), k < l → (H.Adj (r k) (r l) ↔ l.val = k.val + 1 ∨
      (k = 0 ∧ l = Fin.last (m + 1))) := by
    intro k l hkl
    rw [rootFace_adj hH hab hadj (he.mem k) (he.mem l) (he.mono hkl)]
    constructor
    · rintro (h | h)
      · left
        by_contra hne
        have hk1 : k.val + 1 < m + 2 := by have := l.isLt; have : k.val < l.val := hkl; omega
        exact h _ (he.mem ⟨k.val + 1, hk1⟩) ⟨he.mono (show k.val < k.val + 1 by omega),
          he.mono (show k.val + 1 < l.val by have : k.val < l.val := hkl; omega)⟩
      · right
        have h1 := (h a (left_mem_rootFace hab.le)).1
        have h2 := (h b (right_mem_rootFace hab.le)).2
        rw [← he.first] at h1; rw [← he.last] at h2
        exact ⟨he.mono.injective (le_antisymm h1 (he.mono.monotone (Fin.zero_le _))),
          he.mono.injective (le_antisymm (he.mono.monotone (Fin.le_last _)) h2)⟩
    · rintro (h | ⟨rfl, rfl⟩)
      · left
        intro z hz ⟨h1, h2⟩
        obtain ⟨i, rfl⟩ := he.surj z hz
        have := he.mono.lt_iff_lt.mp h1
        have := he.mono.lt_iff_lt.mp h2
        have : k.val < i.val := by assumption
        have : i.val < l.val := by assumption
        omega
      · right
        intro z hz
        rw [he.first, he.last]
        exact ⟨(mem_rootFace.mp hz).1, (mem_rootFace.mp hz).2.1⟩
  refine ⟨hm1, ha, hb, (hGH a b).mpr hadj, fun j j' e => ?_, fun j => hT _ (hin j).1 (hin j).2,
    fun j y hy => ?_, fun j j' => ?_⟩
  · have := he.mono.injective (hψ e)
    exact Fin.ext (by have := congrArg Fin.val this; simp at this; omega)
  · unfold earVerts
    set k : Fin (m + 2) := ⟨j.val + 1, by omega⟩
    constructor
    · intro hA0
      obtain ⟨i, rfl⟩ := hnb _ (hin j).1 (hin j).2 y hy hA0
      rw [hGH] at hA0
      obtain ⟨h1, h2⟩ := nc_inside hH (hin j).1 (hin j).2 hadj hA0
      have hiab : i = a ∨ i = b := by
        by_contra h
        push Not at h
        exact hT i (lt_of_le_of_ne h1 (Ne.symm h.1)) (lt_of_le_of_ne h2 h.2) hy
      rcases hiab with rfl | rfl
      · have hA' : H.Adj (r 0) (r k) := by rw [he.first]; exact hA0.symm
        rcases (hidx 0 k (show (0 : ℕ) < j.val + 1 by omega)).mp hA' with h | ⟨-, h⟩
        · left; exact ⟨by simp [k] at h; omega, rfl⟩
        · exact absurd (congrArg Fin.val h) (by simp [k]; omega)
      · have hA' : H.Adj (r k) (r (Fin.last (m + 1))) := by rw [he.last]; exact hA0
        rcases (hidx k _ (show j.val + 1 < m + 1 by omega)).mp hA' with h | ⟨h, -⟩
        · right; exact ⟨by simp [k] at h; omega, rfl⟩
        · exact absurd (congrArg Fin.val h) (by simp [k])
    · rintro (⟨hj0, rfl⟩ | ⟨hjm, rfl⟩)
      · rw [hGH, ← he.first]
        exact ((hidx 0 k (show (0 : ℕ) < j.val + 1 by omega)).mpr
          (Or.inl (by simp [k]; omega))).symm
      · rw [hGH, ← he.last]
        exact (hidx k _ (show j.val + 1 < m + 1 by omega)).mpr (Or.inl (by simp [k]; omega))
  · unfold earVerts
    rw [hGH]
    rcases lt_trichotomy j j' with hlt | rfl | hgt
    · rw [hidx _ _ (show j.val + 1 < j'.val + 1 by have : j.val < j'.val := hlt; omega)]
      constructor
      · rintro (h | ⟨h, -⟩)
        · left; simp at h; omega
        · exact absurd (congrArg Fin.val h) (by simp)
      · rintro (h | h)
        · left; simp; omega
        · have : j.val < j'.val := hlt; omega
    · simp
    · rw [H.adj_comm, hidx _ _ (show j'.val + 1 < j.val + 1 by have : j'.val < j.val := hgt; omega)]
      constructor
      · rintro (h | ⟨h, -⟩)
        · right; simp at h; omega
        · exact absurd (congrArg Fin.val h) (by simp)
      · rintro (h | h)
        · have : j'.val < j.val := hgt; omega
        · left; simp; omega

/-! ### The induction -/

section Extend

variable {R : ClassSys} {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop}
  {glue : R.Tag → R.Tag → Prop} {vrule : R.Tag → R.Tag → R.Tag → Prop}

/-- **Building the side `[a, b]` of an edge of a block**, with the branches at its interior
vertices, by induction on the width. -/
theorem extendW (hH : IsDissection H) (ψ : Fin N → V) (hψ : Function.Injective ψ)
    (hGH : ∀ i j, G.Adj (ψ i) (ψ j) ↔ H.Adj i j) (hang : Fin N → Finset V)
    (hok : HangOK G ψ hang) (tagR : Finset V → R.Tag) (a₀ b₀ : Fin N)
    (hrule : ∀ (a b : Fin N) (m : ℕ) (r : Fin (m + 2) → Fin N), a₀ ≤ a → b ≤ b₀ → H.Adj a b →
      a < b → RootEnum H a b m r →
        rule (tagR (sideR ψ hang a b)) m fun i => tagR (childR ψ hang r i))
    (hbr : ∀ z, a₀ < z → z < b₀ → HangBuild G R rule glue vrule tagR (hang z) (ψ z)) :
    ∀ (d : ℕ) (a b : Fin N), b.val - a.val ≤ d → a₀ ≤ a → b ≤ b₀ → a < b → H.Adj a b →
    ∀ (T : Finset V) (tg : V → V → R.Tag), TagBuiltW G R rule glue vrule T tg →
      ψ a ∈ T → ψ b ∈ T → (∀ z, a < z → z < b → ∀ v ∈ hang z, v ∉ T) →
      tg (ψ a) (ψ b) = tagR (sideR ψ hang a b) →
      ∃ tg', TagBuiltW G R rule glue vrule (T ∪ sideR ψ hang a b) tg' ∧
        ∀ p ∈ T, ∀ q ∈ T, ¬ (p = ψ a ∧ q = ψ b) → tg' p q = tg p q := by
  intro d
  induction d with
  | zero =>
    intro a b hd _ _ hab
    exact absurd hd (by have : a.val < b.val := hab; omega)
  | succ d ih =>
  intro a b hd ha₀ hb₀ hab hadj T tg hT ha hb hint hdem
  have hT' : ∀ i, a < i → i < b → ψ i ∉ T := fun i h1 h2 => hint i h1 h2 _ (hok.self i)
  by_cases hedge : b.val ≤ a.val + 1
  · -- a single edge: nothing to build
    have hsub : sideR ψ hang a b ⊆ T := by
      intro v hv
      rcases mem_sideR.mp hv with rfl | rfl | ⟨z, h1, h2, -⟩
      · exact ha
      · exact hb
      · exact absurd hedge (by have : a.val < z.val := h1; have : z.val < b.val := h2; omega)
    exact ⟨tg, by rw [union_eq_left.mpr hsub]; exact hT, fun _ _ _ _ _ => rfl⟩
  have h2 : a.val + 2 ≤ b.val := by omega
  obtain ⟨m, r, he⟩ := exists_rootEnum hH hadj h2
  have hm1 := he.one_le
  set x := earVerts ψ r with hx
  have hnb : ∀ k, a < k → k < b → ∀ y ∈ T, G.Adj (ψ k) y → ∃ i, ψ i = y := by
    intro k h1 h2 y hy hA
    rcases hok.nbr k y hA with h | h
    · exact h
    · exact absurd hy (hint k h1 h2 y h)
  have hear : IsEar G T (ψ a) (ψ b) x := isEar_rootW hH ψ hψ hGH hadj hab he ha hb hT' hnb
  have hpath : ∀ j, earPath (ψ a) (ψ b) x j = ψ (r j) := fun j => by
    rw [hx]; exact earPath_eq ψ he j
  set τ : Fin (m + 1) → R.Tag := fun i => tagR (childR ψ hang r i) with hτ
  have hrl : rule (tg (ψ a) (ψ b)) m τ := by
    rw [hdem]; exact hrule a b m r ha₀ hb₀ hadj hab he
  set T₁ := T ∪ univ.image x with hT₁
  set tg₁ := earTags R T tg (ψ a) (ψ b) x τ with htg₁
  have hT1 : TagBuiltW G R rule glue vrule T₁ tg₁ :=
    TagBuiltW.face T tg m (ψ a) (ψ b) x hear τ hrl hT
  have hRT : ∀ j : Fin (m + 2), ψ (r j) ∈ T₁ := by
    intro j
    rw [← hpath j]
    rcases earPath_cases (ψ a) (ψ b) x j with ⟨-, e⟩ | ⟨-, e⟩ | ⟨j', -, e⟩
    · rw [e]; exact mem_union_left _ ha
    · rw [e]; exact mem_union_left _ hb
    · rw [e]; exact mem_union_right _ (mem_image_of_mem _ (mem_univ _))
  have hT₁mem : ∀ v ∈ T₁, v ∈ T ∨ ∃ j : Fin (m + 2), ψ (r j) = v := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · exact Or.inl h
    · obtain ⟨j, -, rfl⟩ := mem_image.mp h
      exact Or.inr ⟨⟨j.val + 1, by omega⟩, rfl⟩
  -- the interior vertices of the root face are interior
  have hrin : ∀ j : Fin (m + 2), 0 < j.val → j.val < m + 1 → a < r j ∧ r j < b := by
    intro j h0 h1
    constructor
    · rw [← he.first]; exact he.mono (show (0 : ℕ) < j.val by omega)
    · rw [← he.last]; exact he.mono (show j.val < m + 1 by simp; omega)
  -- membership in a child region
  have hchild : ∀ (i : Fin (m + 1)) (v : V), v ∈ childR ψ hang r i →
      v = ψ (r i.castSucc) ∨ v = ψ (r i.succ) ∨
        (∃ z, r i.castSucc < z ∧ z < r i.succ ∧ v ∈ hang z) ∨
        (i.val ≠ 0 ∧ v ∈ hang (r i.castSucc)) := by
    intro i v hv
    unfold childR at hv
    split_ifs at hv with h0
    · rcases mem_sideR.mp hv with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases mem_union.mp hv with hv | hv
      · rcases mem_sideR.mp hv with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨h0, hv⟩))
  -- the children, one by one
  have hloop : ∀ k, k ≤ m + 1 → ∃ tgk, TagBuiltW G R rule glue vrule
      (T₁ ∪ (univ.filter fun i : Fin (m + 1) => i.val < k).biUnion
        fun i => childR ψ hang r i) tgk ∧
      ∀ p ∈ T₁, ∀ q ∈ T₁, (∀ i : Fin (m + 1), i.val < k →
        ¬ (p = ψ (r i.castSucc) ∧ q = ψ (r i.succ))) → tgk p q = tg₁ p q := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨tg₁, ?_, fun _ _ _ _ _ => rfl⟩
      have : (univ.filter fun i : Fin (m + 1) => i.val < 0) = ∅ := by
        ext i; simp
      rw [this, biUnion_empty, union_empty]
      exact hT1
    | succ k ihk =>
      intro hk
      obtain ⟨tgk, hTk, hpres⟩ := ihk (by omega)
      set i : Fin (m + 1) := ⟨k, by omega⟩ with hi
      set Tk := T₁ ∪ (univ.filter fun i : Fin (m + 1) => i.val < k).biUnion
        fun i => childR ψ hang r i with hTkdef
      have hw := he.width i
      have hlti := he.lt i
      -- where the vertices of `Tk` are
      have hTkmem : ∀ v ∈ Tk, v ∈ T ∨ (∃ j : Fin (m + 2), ψ (r j) = v) ∨
          (∃ i' : Fin (m + 1), i'.val < k ∧ ∃ z, r i'.castSucc < z ∧ z < r i'.succ ∧
            v ∈ hang z) ∨
          (∃ i' : Fin (m + 1), i'.val < k ∧ i'.val ≠ 0 ∧ v ∈ hang (r i'.castSucc)) := by
        intro v hv
        rcases mem_union.mp hv with h | h
        · rcases hT₁mem v h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · obtain ⟨i', hi', hv'⟩ := mem_biUnion.mp h
          have hi'k := (mem_filter.mp hi').2
          rcases hchild i' v hv' with h | h | h | ⟨h0, h⟩
          · exact Or.inr (Or.inl ⟨_, h.symm⟩)
          · exact Or.inr (Or.inl ⟨_, h.symm⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨i', hi'k, h⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨i', hi'k, h0, h⟩))
      have hc1 : ψ (r i.castSucc) ∈ Tk := mem_union_left _ (hRT _)
      have hc2 : ψ (r i.succ) ∈ Tk := mem_union_left _ (hRT _)
      have hcadj : G.Adj (ψ (r i.castSucc)) (ψ (r i.succ)) := (hGH _ _).mpr (he.adj hH hadj hab i)
      have hcdem : tgk (ψ (r i.castSucc)) (ψ (r i.succ)) = tagR (childR ψ hang r i) := by
        rw [hpres _ (hRT _) _ (hRT _) fun l hl he' => by
          have := he.mono.injective (hψ he'.1)
          have := congrArg Fin.val this
          simp [hi] at this
          omega]
        rw [htg₁, ← hpath i.castSucc, ← hpath i.succ,
          earTags_fwd (R := R) (tg := tg) (τ := τ) hear i]
      -- before the child: the branches at `r i`, if it is an interior vertex
      have hprep : ∃ (T' : Finset V) (tg'' : V → V → R.Tag),
          TagBuiltW G R rule glue vrule T' tg'' ∧
          T' ∪ sideR ψ hang (r i.castSucc) (r i.succ) = Tk ∪ childR ψ hang r i ∧ Tk ⊆ T' ∧
          (∀ v ∈ T', v ∈ Tk ∨ (i.val ≠ 0 ∧ v ∈ hang (r i.castSucc))) ∧
          tg'' (ψ (r i.castSucc)) (ψ (r i.succ)) = tagR (sideR ψ hang (r i.castSucc) (r i.succ)) ∧
          ∀ p ∈ Tk, ∀ q ∈ Tk, ¬ (p = ψ (r i.castSucc) ∧ q = ψ (r i.succ)) → tg'' p q = tgk p q := by
        by_cases h0 : i.val = 0
        · refine ⟨Tk, tgk, hTk, ?_, subset_refl _, fun v hv => Or.inl hv, ?_,
            fun _ _ _ _ _ => rfl⟩
          · unfold childR; rw [ite_eq_left h0]
          · rw [hcdem]; unfold childR; rw [ite_eq_left h0]
        · have hri := hrin i.castSucc (by simp [hi] at h0 ⊢; omega) (by simp [hi]; omega)
          have hfree : ∀ v ∈ hang (r i.castSucc), v ∈ Tk → v = ψ (r i.castSucc) := by
            intro v hv hvT
            rcases hTkmem v hvT with h | ⟨j, rfl⟩ | ⟨i', hi'k, z, hz1, hz2, hz⟩ |
                ⟨i', hi'k, -, hz⟩
            · exact absurd h (hint _ hri.1 hri.2 v hv)
            · rw [hok.idx hv]
            · have := hok.disj _ _ v hz hv
              subst this
              have : r i'.succ ≤ r i.castSucc := he.mono.monotone (by
                show i'.val + 1 ≤ k; omega)
              exact absurd (hz2.trans_le this) (lt_irrefl _)
            · have := he.mono.injective (hok.disj _ _ v hz hv)
              have := congrArg Fin.val this
              simp [hi] at this
              omega
          have hXU : ∀ v ∈ sideR ψ hang (r i.castSucc) (r i.succ), v ∈ hang (r i.castSucc) →
              v = ψ (r i.castSucc) := by
            intro v hv hvU
            rcases mem_sideR.mp hv with h | h | ⟨z, hz1, -, hz⟩
            · exact h
            · rw [h] at hvU
              exact absurd (hok.idx hvU) (ne_of_gt hlti)
            · exact absurd (hok.disj _ _ v hz hvU) (ne_of_gt hz1)
          have hd' : tgk (ψ (r i.castSucc)) (ψ (r i.succ))
              = tagR (sideR ψ hang (r i.castSucc) (r i.succ) ∪ hang (r i.castSucc)) := by
            rw [hcdem]; unfold childR; rw [ite_eq_right h0]
          obtain ⟨tg'', hT'', hdem'', hpres''⟩ := hbr _ (ha₀.trans_lt hri.1)
            (hri.2.trans_le hb₀) Tk tgk hTk hc1 hfree _ hc2 hcadj _ (mem_insert_self _ _) hXU hd'
          refine ⟨Tk ∪ hang (r i.castSucc), tg'', hT'', ?_, subset_union_left, fun v hv => ?_,
            hdem'', hpres''⟩
          · unfold childR; rw [ite_eq_right h0, union_assoc, union_comm (hang _)]
          · rcases mem_union.mp hv with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h0, h⟩
      obtain ⟨T', tg'', hT'', hset', hsub', hT'mem, hdem'', hpres''⟩ := hprep
      have hc3 : ∀ z, r i.castSucc < z → z < r i.succ → ∀ v ∈ hang z, v ∉ T' := by
        intro z hz1 hz2 v hv hvT
        have hza : a < z := lt_of_le_of_lt (he.ge _) hz1
        have hzb : z < b := lt_of_lt_of_le hz2 (he.le _)
        rcases hT'mem v hvT with hvT | ⟨-, h⟩
        · rcases hTkmem v hvT with h | ⟨j, rfl⟩ | ⟨i', hi'k, z', hz1', hz2', hz'⟩ |
              ⟨i', hi'k, -, hz'⟩
          · exact hint z hza hzb v hv h
          · have := hok.idx hv
            subst this
            exact he.gap i _ (he.mem j) ⟨hz1, hz2⟩
          · have := hok.disj _ _ v hz' hv
            subst this
            have : r i'.succ ≤ r i.castSucc := he.mono.monotone (by
              show i'.val + 1 ≤ k; omega)
            exact absurd (hz2'.trans (this.trans_lt hz1)) (lt_irrefl _)
          · have := hok.disj _ _ v hz' hv
            subst this
            have : r i'.castSucc ≤ r i.castSucc := he.mono.monotone (by
              show i'.val ≤ k; omega)
            exact absurd (this.trans_lt hz1) (lt_irrefl _)
        · have := hok.disj _ _ v h hv
          subst this
          exact lt_irrefl _ hz1
      obtain ⟨tg', hT', hpres'⟩ := ih (r i.castSucc) (r i.succ) (by omega) (ha₀.trans (he.ge _))
        ((he.le _).trans hb₀) hlti (he.adj hH hadj hab i) T' tg'' hT'' (hsub' hc1) (hsub' hc2)
        hc3 hdem''
      refine ⟨tg', ?_, fun p hp q hq hnot => ?_⟩
      · have hset : Tk ∪ childR ψ hang r i = T₁ ∪
            (univ.filter fun i : Fin (m + 1) => i.val < k + 1).biUnion
              fun i => childR ψ hang r i := by
          ext y
          simp only [hTkdef, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
          constructor
          · rintro ((h | ⟨l, hl, h⟩) | h)
            · exact Or.inl h
            · exact Or.inr ⟨l, by omega, h⟩
            · exact Or.inr ⟨i, by simp [hi], h⟩
          · rintro (h | ⟨l, hl, h⟩)
            · exact Or.inl (Or.inl h)
            · by_cases hlk : l.val < k
              · exact Or.inl (Or.inr ⟨l, hlk, h⟩)
              · have : l = i := Fin.ext (by simp [hi]; omega)
                exact Or.inr (this ▸ h)
        rw [← hset, ← hset']; exact hT'
      · have hpk : p ∈ Tk := mem_union_left _ hp
        have hqk : q ∈ Tk := mem_union_left _ hq
        rw [hpres' p (hsub' hpk) q (hsub' hqk) (hnot i (by simp [hi])),
          hpres'' p hpk q hqk (hnot i (by simp [hi])), hpres p hp q hq fun l hl => hnot l (by omega)]
  obtain ⟨tgf, hTf, hpresf⟩ := hloop (m + 1) le_rfl
  refine ⟨tgf, ?_, fun p hp q hq hnot => ?_⟩
  · have hset : T₁ ∪ (univ.filter fun i : Fin (m + 1) => i.val < m + 1).biUnion
        (fun i => childR ψ hang r i) = T ∪ sideR ψ hang a b := by
      ext y
      constructor
      · intro hy
        rcases mem_union.mp hy with hy | hy
        · rcases hT₁mem y hy with h | ⟨j, rfl⟩
          · exact mem_union_left _ h
          · by_cases hj0 : j.val = 0
            · have : j = 0 := Fin.ext hj0
              rw [this, he.first]; exact mem_union_left _ ha
            · by_cases hjl : j.val = m + 1
              · have : j = Fin.last (m + 1) := Fin.ext hjl
                rw [this, he.last]; exact mem_union_left _ hb
              · have := hrin j (by omega) (by have := j.isLt; omega)
                exact mem_union_right _ (mem_sideR.mpr (Or.inr (Or.inr
                  ⟨r j, this.1, this.2, hok.self _⟩)))
        · obtain ⟨i, -, hyi⟩ := mem_biUnion.mp hy
          -- an end of a child, or what hangs inside it
          have hend : ∀ j : Fin (m + 2), y = ψ (r j) → y ∈ T ∪ sideR ψ hang a b := by
            intro j hj
            subst hj
            by_cases hj0 : j.val = 0
            · have : j = 0 := Fin.ext hj0
              rw [this, he.first]; exact mem_union_left _ ha
            · by_cases hjl : j.val = m + 1
              · have : j = Fin.last (m + 1) := Fin.ext hjl
                rw [this, he.last]; exact mem_union_left _ hb
              · have := hrin j (by omega) (by have := j.isLt; omega)
                exact mem_union_right _ (mem_sideR.mpr (Or.inr (Or.inr
                  ⟨r j, this.1, this.2, hok.self _⟩)))
          rcases hchild i y hyi with h | h | ⟨z, hz1, hz2, hz⟩ | ⟨h0, h⟩
          · exact hend _ h
          · exact hend _ h
          · exact mem_union_right _ (mem_sideR.mpr (Or.inr (Or.inr
              ⟨z, lt_of_le_of_lt (he.ge _) hz1, lt_of_lt_of_le hz2 (he.le _), hz⟩)))
          · have := hrin i.castSucc (show 0 < i.val by omega) (show i.val < m + 1 from i.isLt)
            exact mem_union_right _ (mem_sideR.mpr (Or.inr (Or.inr
              ⟨_, this.1, this.2, h⟩)))
      · intro hy
        rcases mem_union.mp hy with hy | hy
        · exact mem_union_left _ (mem_union_left _ hy)
        · rcases mem_sideR.mp hy with rfl | rfl | ⟨z, hz1, hz2, hz⟩
          · exact mem_union_left _ (mem_union_left _ ha)
          · exact mem_union_left _ (mem_union_left _ hb)
          · obtain ⟨i, hi1, hi2⟩ := he.cover_Icc hz1.le hz2.le
            apply mem_union_right
            rcases hi1.lt_or_eq with hi1 | hi1
            · rcases hi2.lt_or_eq with hi2 | hi2
              · refine mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, i.isLt⟩, ?_⟩
                unfold childR
                split_ifs
                · exact mem_sideR.mpr (Or.inr (Or.inr ⟨z, hi1, hi2, hz⟩))
                · exact mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inr ⟨z, hi1, hi2, hz⟩)))
              · -- `z = r (i + 1)`, an interior vertex of the root face
                have hil : i.val + 1 < m + 1 := by
                  by_contra hc
                  have : i.succ = Fin.last (m + 1) := Fin.ext (by simp; omega)
                  rw [hi2, this, he.last] at hz2
                  exact lt_irrefl _ hz2
                set i' : Fin (m + 1) := ⟨i.val + 1, hil⟩
                refine mem_biUnion.mpr ⟨i', mem_filter.mpr ⟨mem_univ _, i'.isLt⟩, ?_⟩
                unfold childR
                rw [ite_eq_right (by simp [i'])]
                have : i'.castSucc = i.succ := Fin.ext (by simp [i'])
                rw [this, ← hi2]
                exact mem_union_right _ hz
            · -- `z = r i`, an interior vertex of the root face
              have hi0 : i.val ≠ 0 := by
                intro h0
                have : i.castSucc = 0 := Fin.ext (by simp [h0])
                rw [this, he.first] at hi1
                rw [hi1] at hz1
                exact lt_irrefl _ hz1
              refine mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, i.isLt⟩, ?_⟩
              unfold childR
              rw [ite_eq_right hi0, hi1]
              exact mem_union_right _ hz
    rw [← hset]; exact hTf
  · have hp1 : p ∈ T₁ := mem_union_left _ hp
    have hq1 : q ∈ T₁ := mem_union_left _ hq
    rw [hpresf p hp1 q hq1 fun i _ ⟨e1, e2⟩ => ?_, htg₁,
      earTags_old (R := R) (tg := tg) (τ := τ) hear hp hq hnot]
    -- a child's ends are not both in `T`
    have hw := he.width i
    have k1 : r i.castSucc = a := by
      by_contra h
      have hlt : a < r i.castSucc := lt_of_le_of_ne (he.ge _) (Ne.symm h)
      exact hT' _ hlt ((he.lt i).trans_le (he.le _)) (e1 ▸ hp)
    have k2 : r i.succ = b := by
      by_contra h
      have hlt : r i.succ < b := lt_of_le_of_ne (he.le _) h
      exact hT' _ ((he.ge _).trans_lt (he.lt i)) hlt (e2 ▸ hq)
    rw [k1, k2] at hw
    omega

end Extend

end Outerplanar
