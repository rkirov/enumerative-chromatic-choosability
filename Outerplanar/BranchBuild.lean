/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.BlockModel

/-!
# Building a graph with a block decomposition

For a graph with a block decomposition (`Outerplanar/BlockModel.lean`) and any class system, tags
given as functions of vertex regions (`tagR : Finset V → R.Tag`), face rules and vertex rules:

* `RuleOn D rule tagR U` — the face rule holds at the root face of every side of every block
  whose *half* (the side and what hangs at its first vertex) lies in `U`;
* `SplitOK D vrule tagR` — the vertex rule splits the demand `tagR (X ∪ B)` into `tagR X` and
  `tagR B` for every branch `B` of a block at a vertex `x` and every `X` meeting it in `x`;
* `brR D j z₀` — the branch of the block `j` at its vertex `ψ j z₀`: the block and everything
  hanging at its other vertices;
* **`hangBuild`** — what hangs at a vertex of a block is buildable (`HangBuild`) when the face
  rule holds in it: one branch after the other, each one started by a pendant edge `xw` to the
  next vertex `w` of its block, reoriented, then what hangs at `w`, then the block by `extendW`
  from the edge `(w, x)`, by induction on the size;
* **`buildComp`** — a connected component is built from the edge `pq` of one of its blocks, on
  top of what is built of the other components, if the face rule holds in the two halves
  `halfR D i p q` and `halfR D i q p` of the edge (and the glue holds for their tags); the
  component is the union of the two halves (`Outerplanar/BlockFaces.lean`'s `halves_union`).

Part of the formalization of the seven-even-face theorem with cut vertices (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`); formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### Sides and halves -/

section Sides

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {N : ℕ} {ψ : Fin N → V}
  {hang : Fin N → Finset V} [DecidableRel G.Adj]

theorem half_sub (hok : HangOK G ψ hang) {a b a' b' : Fin N} (h1 : a ≤ a') (h2 : b' ≤ b)
    (h3 : a' < b') : sideR ψ hang a' b' ∪ hang a' ⊆ sideR ψ hang a b ∪ hang a := by
  have hstart : hang a' ⊆ sideR ψ hang a b ∪ hang a := by
    intro v hv
    rcases h1.lt_or_eq with h1 | rfl
    · exact mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inr ⟨a', h1, h3.trans_le h2, hv⟩)))
    · exact mem_union_right _ hv
  intro v hv
  rcases mem_union.mp hv with hv | hv
  · rcases mem_sideR.mp hv with rfl | rfl | ⟨z, hz1, hz2, hz⟩
    · exact hstart (hok.self a')
    · rcases h2.lt_or_eq with h2 | rfl
      · exact mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inr
          ⟨b', h1.trans_lt h3, h2, hok.self b'⟩)))
      · exact mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inl rfl)))
    · exact mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inr
        ⟨z, h1.trans_lt hz1, hz2.trans_le h2, hz⟩)))
  · exact hstart hv

theorem sideR_inter_hang (hok : HangOK G ψ hang) {a b : Fin N} (hab : a < b) {v : V}
    (hv : v ∈ sideR ψ hang a b) (hv' : v ∈ hang a) : v = ψ a := by
  rcases mem_sideR.mp hv with h | h | ⟨z, hz1, -, hz⟩
  · exact h
  · rw [h] at hv'
    exact absurd (hok.idx hv') (ne_of_gt hab)
  · exact absurd (hok.disj _ _ v hz hv') (ne_of_gt hz1)

end Sides

/-! ### Arithmetic of rotations -/

section Arith

variable {n : ℕ}

theorem sub_val' (a b : Fin n) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else n + a.val - b.val := by
  split_ifs with h
  · exact sub_val_le h
  · exact sub_val_lt (not_le.mp h)

variable [NeZero n]

theorem rot_zero' (c : Fin n) : rot c 0 = c := zero_add c

theorem rot_sub' (c z : Fin n) : rot c (z - c) = z := sub_add_cancel z c

theorem rot_eq_iff {c k z : Fin n} : rot c k = z ↔ k = z - c := by
  constructor
  · rintro rfl; simp [rot]
  · rintro rfl; exact rot_sub' c z

/-- The vertices of a polygon other than `p` and `q`: on the arc from `p` to `q`, or on the arc
from `q` to `p`. -/
theorem arc_cases (p q z : Fin n) (hpq : p ≠ q) :
    z = p ∨ z = q ∨ (0 < (z - p).val ∧ (z - p).val < (q - p).val) ∨
      (0 < (z - q).val ∧ (z - q).val < (p - q).val) := by
  have hp := p.isLt; have hq := q.isLt; have hz := z.isLt
  have hpq' : p.val ≠ q.val := fun h => hpq (Fin.ext h)
  rw [sub_val' z p, sub_val' q p, sub_val' z q, sub_val' p q]
  by_cases h1 : z.val = p.val
  · exact Or.inl (Fin.ext h1)
  by_cases h2 : z.val = q.val
  · exact Or.inr (Or.inl (Fin.ext h2))
  right; right
  split_ifs <;> omega

theorem arc_disj (p q z : Fin n) :
    ¬ ((0 < (z - p).val ∧ (z - p).val < (q - p).val) ∧
      (0 < (z - q).val ∧ (z - q).val < (p - q).val)) := by
  have hp := p.isLt; have hq := q.isLt; have hz := z.isLt
  rw [sub_val' z p, sub_val' q p, sub_val' z q, sub_val' p q]
  split_ifs <;> omega

end Arith

/-! ### Branches -/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {ι : Type} (D : BlockDecomp G ι)

instance BlockDecomp.neZero (i : ι) : NeZero (D.n i) := ⟨by have := D.two_le i; omega⟩

variable {R : ClassSys} (rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop)
  (glue : R.Tag → R.Tag → Prop) (vrule : R.Tag → R.Tag → R.Tag → Prop)
  (tagR : Finset V → R.Tag)

/-- The face rule holds at the root face of every side whose half lies in `U`. -/
def RuleOn (U : Finset V) : Prop :=
  ∀ (j : ι) (c a b : Fin (D.n j)) (m : ℕ) (r : Fin (m + 2) → Fin (D.n j)),
    (D.vH j c).Adj a b → a < b → RootEnum (D.vH j c) a b m r →
    sideR (D.vψ j c) (D.vhang j c) a b ∪ D.vhang j c a ⊆ U →
    rule (tagR (sideR (D.vψ j c) (D.vhang j c) a b)) m
      fun i => tagR (childR (D.vψ j c) (D.vhang j c) r i)

variable {D rule tagR} in
theorem RuleOn.mono {U U' : Finset V} (h : RuleOn D rule tagR U) (hsub : U' ⊆ U) :
    RuleOn D rule tagR U' :=
  fun j c a b m r h1 h2 h3 h4 => h j c a b m r h1 h2 h3 (h4.trans hsub)

/-- The branch of the block `j` at its vertex `ψ j z₀`. -/
noncomputable def BlockDecomp.brR (j : ι) (z₀ : Fin (D.n j)) : Finset V :=
  insert (D.ψ j z₀) ((univ.filter fun z => z ≠ z₀).biUnion (D.hang j))

/-- The vertex rule splits off every branch. -/
def SplitOK : Prop :=
  ∀ (j : ι) (z₀ : Fin (D.n j)) (X : Finset V), D.ψ j z₀ ∈ X →
    (∀ v ∈ X, v ∈ D.brR j z₀ → v = D.ψ j z₀) →
      vrule (tagR (X ∪ D.brR j z₀)) (tagR X) (tagR (D.brR j z₀))

/-- The half of the edge `pq` of the block `i` on the side of `p`: the arc from `p` to `q` with
what hangs at its interior vertices, and what hangs at `p`. -/
noncomputable def BlockDecomp.halfR (i : ι) (p q : Fin (D.n i)) : Finset V :=
  sideR (D.vψ i p) (D.vhang i p) 0 (q - p) ∪ D.hang i p

variable {D}

open BlockDecomp

theorem BlockDecomp.mem_brR {j : ι} {z₀ : Fin (D.n j)} {v : V} :
    v ∈ D.brR j z₀ ↔ v = D.ψ j z₀ ∨ ∃ z, z ≠ z₀ ∧ v ∈ D.hang j z := by
  unfold brR
  simp only [mem_insert, mem_biUnion, mem_filter, mem_univ, true_and]

theorem BlockDecomp.vψ_apply (i : ι) (c k : Fin (D.n i)) : D.vψ i c k = D.ψ i (rot c k) := rfl

theorem BlockDecomp.vhang_apply (i : ι) (c k : Fin (D.n i)) : D.vhang i c k = D.hang i (rot c k) := rfl

variable {rule glue vrule tagR}

/-- **A branch is buildable** when what hangs at the other vertices of its block is. -/
theorem branchBuild (hsplit : SplitOK D vrule tagR) {j : ι} {z₀ : Fin (D.n j)}
    (hR : RuleOn D rule tagR (D.brR j z₀))
    (ih : ∀ z, z ≠ z₀ → HangBuild G R rule glue vrule tagR (D.hang j z) (D.ψ j z)) :
    HangBuild G R rule glue vrule tagR (D.brR j z₀) (D.ψ j z₀) := by
  intro T tg hT hx hfree y' hy' hxy' X hxX hXU hdem
  have hn := D.two_le j
  set x := D.ψ j z₀ with hxdef
  -- the next vertex of the polygon
  set c : Fin (D.n j) := ⟨(z₀.val + 1) % D.n j, Nat.mod_lt _ (by omega)⟩ with hcdef
  have hcv : c.val = if z₀.val + 1 < D.n j then z₀.val + 1 else 0 := by
    have := z₀.isLt
    show (z₀.val + 1) % D.n j = _
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show z₀.val + 1 = D.n j by omega, Nat.mod_self]
  set b₀ : Fin (D.n j) := z₀ - c with hb₀def
  have hb₀v : b₀.val = D.n j - 1 := by
    have := z₀.isLt
    rw [hb₀def, sub_val' z₀ c, hcv]
    split_ifs <;> omega
  have hc0 : c ≠ z₀ := fun e => by
    have := congrArg Fin.val e
    rw [hcv] at this
    split_ifs at this <;> omega
  have hrb : rot c b₀ = z₀ := rot_sub' c z₀
  have hr0 : rot c 0 = c := rot_zero' c
  have hb₀pos : (0 : Fin (D.n j)) < b₀ := by
    rw [Fin.lt_def, hb₀v]; simp; omega
  set w := D.ψ j c with hwdef
  set ψ' := D.vψ j c with hψ'
  set hang' := D.vhang j c with hhang'
  have hψ0 : ψ' 0 = w := by rw [hψ', vψ_apply, hr0]
  have hψb : ψ' b₀ = x := by rw [hψ', vψ_apply, hrb]
  have hh0 : hang' 0 = D.hang j c := by rw [hhang', vhang_apply, hr0]
  have hok' := D.view_hangOK j c
  have hwx : G.Adj w x := by
    have h := (D.view_diss j c).2.1 0 b₀ rfl (by rw [hb₀v]; omega) (ne_of_lt hb₀pos)
    have := (D.view_adj j c 0 b₀).mpr h
    rwa [← hψ', hψ0, hψb] at this
  -- the indices of the view
  have hidx : ∀ k : Fin (D.n j), 0 < k → k < b₀ → rot c k ≠ z₀ ∧ rot c k ≠ c := by
    intro k h1 h2
    refine ⟨fun e => ?_, fun e => ?_⟩
    · exact ne_of_lt h2 (rot_injective c (e.trans hrb.symm))
    · exact ne_of_gt h1 (rot_injective c (e.trans hr0.symm))
  have hint : ∀ z, z ≠ z₀ → z ≠ c → 0 < z - c ∧ z - c < b₀ := by
    intro z hz hzc
    refine ⟨Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr hzc), lt_of_le_of_ne ?_ fun e => hz ?_⟩
    · rw [Fin.le_def, hb₀v]; have := (z - c).isLt; omega
    · rw [← rot_sub' c z, e, hrb]
  -- the branch is the side of `(w, x)` and what hangs at `w`
  have hBr : D.brR j z₀ = sideR ψ' hang' 0 b₀ ∪ D.hang j c := by
    ext v
    rw [mem_brR, mem_union, mem_sideR]
    constructor
    · rintro (rfl | ⟨z, hz, hv⟩)
      · exact Or.inl (Or.inr (Or.inl hψb.symm))
      · by_cases hzc : z = c
        · subst hzc; exact Or.inr hv
        · obtain ⟨h1, h2⟩ := hint z hz hzc
          refine Or.inl (Or.inr (Or.inr ⟨z - c, h1, h2, ?_⟩))
          rw [hhang', vhang_apply, rot_sub']; exact hv
    · rintro ((h | h | ⟨k, h1, h2, hv⟩) | hv)
      · rw [hψ0] at h
        exact Or.inr ⟨c, hc0, h ▸ D.hang_self j c⟩
      · rw [hψb] at h; exact Or.inl h
      · exact Or.inr ⟨rot c k, (hidx k h1 h2).1, hv⟩
      · exact Or.inr ⟨c, hc0, hv⟩
  have hcBr : D.hang j c ⊆ D.brR j z₀ := fun v hv => mem_brR.mpr (Or.inr ⟨c, hc0, hv⟩)
  have hxc : x ∉ D.hang j c := fun h => hc0 (BlockDecomp.hang_idx h).symm
  -- the pendant edge `xw`
  have hw : w ∉ T := fun h => by
    have := hfree w (hcBr (D.hang_self j c)) h
    exact hc0 (D.inj j this)
  have huniq : ∀ z ∈ T, G.Adj w z → z = x := by
    intro z hz hwz
    rcases (D.hangOK j).nbr c z hwz with ⟨b, rfl⟩ | h
    · by_cases hb : b = z₀
      · rw [hb]
      · exact hfree _ (mem_brR.mpr (Or.inr ⟨b, hb, D.hang_self j b⟩)) hz
    · exact hfree z (hcBr h) hz
  have hwy : w ≠ y' := fun e => hw (e ▸ hy')
  have hxw : x ≠ w := fun e => hc0 (D.inj j e).symm
  have hr : vrule (tg x y') (tagR X) (tagR (D.brR j z₀)) := by
    rw [hdem]; exact hsplit j z₀ X hxX hXU
  have hT1 := TagBuiltW.pendant T tg x y' w hx hy' hxy' hw hwx huniq _ _ hr hT
  have hT2 := TagBuiltW.swap _ _ x w (mem_insert_of_mem hx) (mem_insert_self w T) hwx.symm hT1
  set tg₂ := swapTags R (pendTags R tg x y' w (tagR X) (tagR (D.brR j z₀))) x w with htg₂
  have e2wx : tg₂ w x = tagR (D.brR j z₀) := by
    have h1 : ¬ (w = x ∧ x = w) := fun h => hxw h.2
    have h2 : ¬ (x = x ∧ w = y') := fun h => hwy h.2
    rw [htg₂]
    unfold swapTags
    rw [ite_eq_right h1, ite_eq_left ⟨rfl, rfl⟩]
    unfold pendTags
    rw [ite_eq_right h2, ite_eq_left ⟨rfl, rfl⟩]
  have e2xy : tg₂ x y' = tagR X := by
    have h1 : ¬ (x = x ∧ y' = w) := fun h => hwy h.2.symm
    have h2 : ¬ (x = w ∧ y' = x) := fun h => hxw h.1
    rw [htg₂]
    unfold swapTags
    rw [ite_eq_right h1, ite_eq_right h2]
    unfold pendTags
    rw [ite_eq_left ⟨rfl, rfl⟩]
  have e2 : ∀ p ∈ T, ∀ q ∈ T, ¬ (p = x ∧ q = y') → tg₂ p q = tg p q := by
    intro p hp q hq hpq
    have hpw : p ≠ w := fun e => hw (e ▸ hp)
    have hqw : q ≠ w := fun e => hw (e ▸ hq)
    simp [htg₂, swapTags, pendTags, hpq, hpw, hqw]
  -- what hangs at `w`
  set Xw := sideR ψ' hang' 0 b₀ with hXw
  have hwXw : w ∈ Xw := by rw [hXw, ← hψ0]; exact mem_insert_self _ _
  obtain ⟨tg₃, hT3, e3wx, e3⟩ := ih c hc0 (insert w T) tg₂ hT2 (mem_insert_self w T)
    (fun v hv hvT => by
      rcases mem_insert.mp hvT with h | h
      · exact h
      · have := hfree v (hcBr hv) h
        exact absurd (this ▸ hv) hxc)
    x (mem_insert_of_mem hx) hwx Xw hwXw
    (fun v hv hv' => by
      have := sideR_inter_hang hok' hb₀pos hv (by rw [vhang_apply, hr0]; exact hv')
      rw [vψ_apply, hr0] at this
      exact this)
    (by rw [e2wx, hBr])
  -- the block, from the edge `(w, x)`
  have hfree' : ∀ k, 0 < k → k < b₀ → ∀ v ∈ hang' k, v ∉ insert w T ∪ D.hang j c := by
    intro k h1 h2 v hv hvT
    obtain ⟨hk1, hk2⟩ := hidx k h1 h2
    rw [hhang', vhang_apply] at hv
    rcases mem_union.mp hvT with h | h
    · rcases mem_insert.mp h with rfl | h
      · exact hk2 (D.hang_disj hv (D.hang_self j c))
      · have := hfree v (mem_brR.mpr (Or.inr ⟨_, hk1, hv⟩)) h
        rw [this] at hv
        exact hk1 (BlockDecomp.hang_idx hv).symm
    · exact hk2 (D.hang_disj hv h)
  obtain ⟨tg₄, hT4, e4⟩ := extendW (D.view_diss j c) ψ' (D.view_inj j c) (D.view_adj j c) hang'
    hok' tagR 0 b₀
    (fun a b m r _ hb hadj hab he => hR j c a b m r hadj hab he (by
      rw [hBr, ← hh0]; exact half_sub hok' (Fin.zero_le a) hb hab))
    (fun k h1 h2 => ih (rot c k) (hidx k h1 h2).1)
    b₀.val 0 b₀ (by simp) le_rfl le_rfl hb₀pos
    ((D.view_diss j c).2.1 0 b₀ rfl (by rw [hb₀v]; omega) (ne_of_lt hb₀pos))
    _ tg₃ hT3 (by rw [hψ0]; exact mem_union_left _ (mem_insert_self w T))
    (by rw [hψb]; exact mem_union_left _ (mem_insert_of_mem hx)) hfree'
    (by rw [hψ0, hψb]; exact e3wx)
  refine ⟨tg₄, ?_, ?_, fun p hp q hq hpq => ?_⟩
  · have hset : insert w T ∪ D.hang j c ∪ sideR ψ' hang' 0 b₀ = T ∪ D.brR j z₀ := by
      rw [hBr]
      apply Finset.Subset.antisymm
      · intro v hv
        rcases mem_union.mp hv with hv | hv
        · rcases mem_union.mp hv with hv | hv
          · rcases mem_insert.mp hv with hv | hv
            · rw [hv]; exact mem_union_right _ (mem_union_left _ hwXw)
            · exact mem_union_left _ hv
          · exact mem_union_right _ (mem_union_right _ hv)
        · exact mem_union_right _ (mem_union_left _ hv)
      · intro v hv
        rcases mem_union.mp hv with hv | hv
        · exact mem_union_left _ (mem_union_left _ (mem_insert_of_mem hv))
        · rcases mem_union.mp hv with hv | hv
          · exact mem_union_right _ hv
          · exact mem_union_left _ (mem_union_right _ hv)
    rw [← hset]; exact hT4
  · have hxT : x ∈ insert w T ∪ D.hang j c := mem_union_left _ (mem_insert_of_mem hx)
    have hyT : y' ∈ insert w T ∪ D.hang j c := mem_union_left _ (mem_insert_of_mem hy')
    rw [e4 x hxT y' hyT (fun h => hxw (by rw [hψ0] at h; exact h.1)),
      e3 x (mem_insert_of_mem hx) y' (mem_insert_of_mem hy') (fun h => hxw h.1), e2xy]
  · have hpT : p ∈ insert w T ∪ D.hang j c := mem_union_left _ (mem_insert_of_mem hp)
    have hqT : q ∈ insert w T ∪ D.hang j c := mem_union_left _ (mem_insert_of_mem hq)
    have hpw : p ≠ w := fun e => hw (e ▸ hp)
    rw [e4 p hpT q hqT (fun h => hpw (by rw [hψ0] at h; exact h.1)),
      e3 p (mem_insert_of_mem hp) q (mem_insert_of_mem hq) (fun h => hpw h.1), e2 p hp q hq hpq]

/-! ### What hangs at a vertex -/

/-- **What hangs at a vertex of a block is buildable** when the face rule holds in it. -/
theorem hangBuild [Fintype ι] (hsplit : SplitOK D vrule tagR) :
    ∀ (s : ℕ) (i : ι) (y : Fin (D.n i)), (D.hang i y).card ≤ s →
      RuleOn D rule tagR (D.hang i y) →
      HangBuild G R rule glue vrule tagR (D.hang i y) (D.ψ i y) := by
  intro s
  induction s with
  | zero =>
    intro i y h
    exact absurd (card_pos.mpr ⟨_, D.hang_self i y⟩) (by omega)
  | succ s ih =>
  intro i y hcard hR
  classical
  set x := D.ψ i y with hxdef
  set J := univ.filter fun j => j ≠ i ∧ ∃ z, D.ψ j z = x with hJ
  set z₀ : (j : ι) → Fin (D.n j) := fun j =>
    if h : ∃ z, D.ψ j z = x then h.choose else 0 with hz₀def
  have hz₀ : ∀ j ∈ J, D.ψ j (z₀ j) = x := by
    intro j hj
    have h := (mem_filter.mp hj).2.2
    simp only [hz₀def, dite_eq_left h]
    exact h.choose_spec
  have hJi : ∀ j ∈ J, j ≠ i := fun j hj => (mem_filter.mp hj).2.1
  have hsub : ∀ j ∈ J, ∀ z, z ≠ z₀ j → D.hang j z ⊆ D.hang i y :=
    fun j hj z hz => D.hang_sub (hJi j hj) (hz₀ j hj) hz
  have hxz : ∀ j ∈ J, ∀ z, z ≠ z₀ j → x ∉ D.hang j z := fun j hj z hz h => by
    rw [← hz₀ j hj] at h
    exact hz (BlockDecomp.hang_idx h).symm
  have hlt : ∀ j ∈ J, ∀ z, z ≠ z₀ j → (D.hang j z).card ≤ s := by
    intro j hj z hz
    have : (D.hang j z).card < (D.hang i y).card :=
      card_lt_card ((Finset.ssubset_iff_of_subset (hsub j hj z hz)).mpr
        ⟨x, D.hang_self i y, hxz j hj z hz⟩)
    omega
  have hbrsub : ∀ j ∈ J, D.brR j (z₀ j) ⊆ D.hang i y := by
    intro j hj v hv
    rcases mem_brR.mp hv with h | ⟨z, hz, h⟩
    · rw [h, hz₀ j hj]; exact D.hang_self i y
    · exact hsub j hj z hz h
  have hbrB : ∀ j ∈ J, HangBuild G R rule glue vrule tagR (D.brR j (z₀ j)) x := by
    intro j hj
    have := branchBuild (glue := glue) hsplit (hR.mono (hbrsub j hj)) fun z hz =>
      ih j z (hlt j hj z hz) (hR.mono (hsub j hj z hz))
    rwa [hz₀ j hj] at this
  -- branches of different blocks meet only in `x`
  have hbrdisj : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∀ v ∈ D.brR j (z₀ j), v ∈ D.brR j' (z₀ j') →
      v = x := by
    intro j hj j' hj' hjj v hv hv'
    rcases mem_brR.mp hv with h | ⟨z, hz, h⟩
    · rw [h, hz₀ j hj]
    · rcases mem_brR.mp hv' with h' | ⟨z', hz', h'⟩
      · rw [h', hz₀ j' hj']
      · exact (D.branch_disj hjj ((hz₀ j' hj').trans (hz₀ j hj).symm) hz hz' h h').elim
  -- the decomposition
  have hdec : D.hang i y = insert x (J.biUnion fun j => D.brR j (z₀ j)) := by
    ext v
    rw [mem_insert, mem_biUnion]
    constructor
    · intro hv
      rcases D.hang_decomp hv with h | ⟨j, hji, z₀', z, he, hz, h⟩
      · exact Or.inl h
      · have hj : j ∈ J := mem_filter.mpr ⟨mem_univ _, hji, z₀', he⟩
        have e : z₀' = z₀ j := D.inj j (he.trans (hz₀ j hj).symm)
        exact Or.inr ⟨j, hj, mem_brR.mpr (Or.inr ⟨z, e ▸ hz, h⟩)⟩
    · rintro (h | ⟨j, hj, h⟩)
      · rw [h]; exact D.hang_self i y
      · exact hbrsub j hj h
  -- one branch after the other
  have key : ∀ J' : Finset ι, J' ⊆ J →
      HangBuild G R rule glue vrule tagR (insert x (J'.biUnion fun j => D.brR j (z₀ j))) x := by
    intro J'
    induction J' using Finset.induction_on with
    | empty =>
      intro _ T tg hT hx _ y' _ _ X hxX _ hdem
      refine ⟨tg, ?_, ?_, fun _ _ _ _ _ => rfl⟩
      · rw [biUnion_empty, union_insert, union_empty, insert_eq_of_mem hx]
        exact hT
      · rw [hdem, biUnion_empty, union_insert, union_empty, insert_eq_of_mem hxX]
    | insert j J'' hj ihJ =>
      intro hJ' T tg hT hx hfree y' hy' hadj X hxX hXU hdem
      have hjJ : j ∈ J := hJ' (mem_insert_self j J'')
      set U'' := insert x (J''.biUnion fun j => D.brR j (z₀ j)) with hU''
      have hU' : insert x ((insert j J'').biUnion fun j => D.brR j (z₀ j)) = U'' ∪ D.brR j (z₀ j) := by
        rw [biUnion_insert, hU'']
        ext v
        simp only [mem_insert, mem_union]
        tauto
      rw [hU'] at hfree hXU hdem ⊢
      -- `U''` meets the branch of `j` only in `x`
      have hUB : ∀ v ∈ U'', v ∈ D.brR j (z₀ j) → v = x := by
        intro v hv hv'
        rcases mem_insert.mp hv with h | h
        · exact h
        · obtain ⟨j', hj', h⟩ := mem_biUnion.mp h
          exact hbrdisj j' (hJ' (mem_insert_of_mem hj')) j hjJ (fun e => hj (e ▸ hj')) v h hv'
      obtain ⟨tg₁, hT₁, e₁, p₁⟩ := hbrB j hjJ T tg hT hx
        (fun v hv hvT => hfree v (mem_union_right _ hv) hvT) y' hy' hadj (X ∪ U'')
        (mem_union_left _ hxX)
        (fun v hv hv' => by
          rcases mem_union.mp hv with h | h
          · exact hXU v h (mem_union_right _ hv')
          · exact hUB v h hv')
        (by rw [hdem, union_assoc])
      obtain ⟨tg₂, hT₂, e₂, p₂⟩ := ihJ (fun j' hj' => hJ' (mem_insert_of_mem hj'))
        (T ∪ D.brR j (z₀ j)) tg₁ hT₁ (mem_union_left _ hx)
        (fun v hv hvT => by
          rcases mem_union.mp hvT with h | h
          · exact hfree v (mem_union_left _ hv) h
          · exact hUB v hv h)
        y' (mem_union_left _ hy') hadj X hxX (fun v hv hv' => hXU v hv (mem_union_left _ hv'))
        e₁
      refine ⟨tg₂, ?_, e₂, fun p hp q hq hpq => ?_⟩
      · have : T ∪ D.brR j (z₀ j) ∪ U'' = T ∪ (U'' ∪ D.brR j (z₀ j)) := by
          rw [union_assoc, union_comm (D.brR j _)]
        rw [← this]; exact hT₂
      · rw [p₂ p (mem_union_left _ hp) q (mem_union_left _ hq) hpq, p₁ p hp q hq hpq]
  rw [hdec]
  exact key J subset_rfl

/-! ### The whole graph -/

/-- **A connected component is built** from the edge `pq` of one of its blocks, on top of
what is built of the other components, if the face rule holds in the two halves of the edge and
the glue holds for their tags. The component is the union of the two halves. -/
theorem buildComp [Fintype ι] (hsplit : SplitOK D vrule tagR) (i : ι)
    (p q : Fin (D.n i)) (hpq : (D.H i).Adj p q)
    (hg : glue (tagR (D.halfR i p q)) (tagR (D.halfR i q p)))
    (h₁ : RuleOn D rule tagR (D.halfR i p q)) (h₂ : RuleOn D rule tagR (D.halfR i q p))
    (T : Finset V) (tg : V → V → R.Tag) (hT : TagBuiltW G R rule glue vrule T tg)
    (hTK : ∀ v ∈ T, ¬ G.Reachable (D.ψ i p) v) :
    ∃ tg', TagBuiltW G R rule glue vrule (T ∪ (D.halfR i p q ∪ D.halfR i q p)) tg' := by
  have hne : p ≠ q := hpq.ne
  -- what hangs at the block is not built yet
  have hnT : ∀ z v, v ∈ D.hang i z → v ∉ T := by
    intro z v hv hvT
    have h1 : G.Reachable (D.ψ i p) (D.ψ i z) := by
      have := D.block_reach (E := ∅) (k := i) (fun _ _ _ => Set.notMem_empty _) p z
      rwa [SimpleGraph.deleteEdges_empty] at this
    exact hTK v hvT (h1.trans (SimpleGraph.Reachable.mono (SimpleGraph.deleteEdges_le _)
      (BlockDecomp.mem_hang.mp hv)))
  have hne' : D.ψ i p ≠ D.ψ i q := fun e => hne (D.inj i e)
  set bq : Fin (D.n i) := q - p with hbq
  set bp : Fin (D.n i) := p - q with hbp
  have hbq0 : (0 : Fin (D.n i)) < bq := Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hbp0 : (0 : Fin (D.n i)) < bp := Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hp0 : D.vψ i p 0 = D.ψ i p := by rw [vψ_apply, rot_zero']
  have hpb : D.vψ i p bq = D.ψ i q := by rw [vψ_apply, hbq, rot_sub']
  have hq0 : D.vψ i q 0 = D.ψ i q := by rw [vψ_apply, rot_zero']
  have hqb : D.vψ i q bp = D.ψ i p := by rw [vψ_apply, hbp, rot_sub']
  have hhp : D.vhang i p 0 = D.hang i p := by rw [vhang_apply, rot_zero']
  have hhq : D.vhang i q 0 = D.hang i q := by rw [vhang_apply, rot_zero']
  have hadj₁ : (D.vH i p).Adj 0 bq := by
    show (D.H i).Adj (rot p 0) (rot p bq)
    rw [rot_zero', hbq, rot_sub']; exact hpq
  have hadj₂ : (D.vH i q).Adj 0 bp := by
    show (D.H i).Adj (rot q 0) (rot q bp)
    rw [rot_zero', hbp, rot_sub']; exact hpq.symm
  have hok₁ := D.view_hangOK i p
  have hok₂ := D.view_hangOK i q
  set X₁ := sideR (D.vψ i p) (D.vhang i p) 0 bq with hX₁
  set X₂ := sideR (D.vψ i q) (D.vhang i q) 0 bp with hX₂
  have hpX₁ : D.ψ i p ∈ X₁ := by rw [hX₁, ← hp0]; exact mem_insert_self _ _
  have hqX₂ : D.ψ i q ∈ X₂ := by rw [hX₂, ← hq0]; exact mem_insert_self _ _
  have hGpq : G.Adj (D.ψ i p) (D.ψ i q) := BlockDecomp.adj_block.mpr hpq
  -- the interior vertices of the two arcs
  have hk₁ : ∀ k : Fin (D.n i), 0 < k → k < bq → rot p k ≠ p ∧ rot p k ≠ q := by
    intro k h1 h2
    refine ⟨fun e => ne_of_gt h1 (rot_injective p (e.trans (rot_zero' p).symm)),
      fun e => ne_of_lt h2 (rot_injective p (e.trans (rot_sub' p q).symm))⟩
  have hk₂ : ∀ k : Fin (D.n i), 0 < k → k < bp → rot q k ≠ q ∧ rot q k ≠ p := by
    intro k h1 h2
    refine ⟨fun e => ne_of_gt h1 (rot_injective q (e.trans (rot_zero' q).symm)),
      fun e => ne_of_lt h2 (rot_injective q (e.trans (rot_sub' q p).symm))⟩
  -- the base edge
  have hpT : D.ψ i p ∉ T := hnT p _ (D.hang_self i p)
  have hqT : D.ψ i q ∉ T := hnT q _ (D.hang_self i q)
  have hT0 := TagBuiltW.comp T tg (D.ψ i p) (D.ψ i q) hpT hqT hGpq
    (fun z hz => ⟨fun h => hTK z hz h.reachable, fun h => hTK z hz (hGpq.reachable.trans
      h.reachable)⟩) _ _ hg hT
  -- what hangs at `p`
  obtain ⟨tg₁, hT₁, e₁, p₁⟩ := hangBuild (glue := glue) hsplit _ i p le_rfl
    (h₁.mono subset_union_right) _ _ hT0 (by simp)
    (fun v hv hvT => by
      rcases mem_insert.mp hvT with h | h
      · exact h
      · rcases mem_insert.mp h with h | h
        · rw [h] at hv
          exact absurd (BlockDecomp.hang_idx hv) (Ne.symm hne)
        · exact absurd h (hnT p v hv))
    _ (by simp) hGpq X₁ hpX₁
    (fun v hv hv' => by
      have := sideR_inter_hang hok₁ hbq0 hv (by rw [hhp]; exact hv')
      rwa [hp0] at this)
    (by simp [compTags, BlockDecomp.halfR, hX₁, hbq])
  -- what hangs at `q`
  obtain ⟨tg₂, hT₂, e₂, p₂⟩ := hangBuild (glue := glue) hsplit _ i q le_rfl
    (h₂.mono subset_union_right) _ _ hT₁ (by simp)
    (fun v hv hvT => by
      rcases mem_union.mp hvT with h | h
      · rcases mem_insert.mp h with h | h
        · rw [h] at hv
          exact absurd (BlockDecomp.hang_idx hv) hne
        · rcases mem_insert.mp h with h | h
          · exact h
          · exact absurd h (hnT q v hv)
      · exact absurd (D.hang_disj h hv) hne)
    (D.ψ i p) (by simp) hGpq.symm X₂ hqX₂
    (fun v hv hv' => by
      have := sideR_inter_hang hok₂ hbp0 hv (by rw [hhq]; exact hv')
      rwa [hq0] at this)
    (by
      rw [p₁ _ (by simp) _ (by simp) (fun h => hne' h.2)]
      simp [compTags, hne', Ne.symm hne', BlockDecomp.halfR, hX₂, hbp])
  have e₂' : tg₂ (D.ψ i p) (D.ψ i q) = tagR X₁ := by
    rw [p₂ _ (by simp) _ (by simp) (fun h => hne' h.2.symm), e₁]
  set T₂ := insert (D.ψ i p) (insert (D.ψ i q) T) ∪ D.hang i p ∪ D.hang i q with hT₂def
  have hT₂mem : ∀ v ∈ T₂, v ∈ T ∨ v ∈ D.hang i p ∨ v ∈ D.hang i q := by
    intro v hv
    simp only [hT₂def, mem_union, mem_insert] at hv
    rcases hv with ((h | h | h) | h) | h
    · rw [h]; exact Or.inr (Or.inl (D.hang_self i p))
    · rw [h]; exact Or.inr (Or.inr (D.hang_self i q))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- the arc from `p` to `q`
  obtain ⟨tg₃, hT₃, p₃⟩ := extendW (D.view_diss i p) (D.vψ i p) (D.view_inj i p)
    (D.view_adj i p) (D.vhang i p) hok₁ tagR 0 bq
    (fun a b m r _ hb hadj hab he => h₁ i p a b m r hadj hab he (by
      unfold BlockDecomp.halfR
      rw [← hhp]; exact half_sub hok₁ (Fin.zero_le a) hb hab))
    (fun k h1 h2 => hangBuild hsplit _ i _ le_rfl (h₁.mono (fun v hv =>
      mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inr ⟨k, h1, h2, hv⟩))))))
    bq.val 0 bq (by simp) le_rfl le_rfl hbq0 hadj₁ T₂ tg₂ hT₂
    (by rw [hp0, hT₂def]; simp) (by rw [hpb, hT₂def]; simp)
    (fun k h1 h2 v hv hvT => by
      obtain ⟨n1, n2⟩ := hk₁ k h1 h2
      rw [vhang_apply] at hv
      rcases hT₂mem v hvT with h | h | h
      · exact hnT _ v hv h
      · exact n1 (D.hang_disj hv h)
      · exact n2 (D.hang_disj hv h))
    (by rw [hp0, hpb]; exact e₂')
  -- the arc from `q` to `p`
  have hT₃mem : ∀ v ∈ T₂ ∪ X₁, v ∈ T ∨ v ∈ D.hang i p ∨ v ∈ D.hang i q ∨
      ∃ k, 0 < k ∧ k < bq ∧ v ∈ D.hang i (rot p k) := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rcases hT₂mem v h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases mem_sideR.mp h with h | h | ⟨k, h1, h2, h⟩
      · rw [h, hp0]; exact Or.inr (Or.inl (D.hang_self i p))
      · rw [h, hpb]; exact Or.inr (Or.inr (Or.inl (D.hang_self i q)))
      · exact Or.inr (Or.inr (Or.inr ⟨k, h1, h2, h⟩))
  obtain ⟨tg₄, hT₄, -⟩ := extendW (D.view_diss i q) (D.vψ i q) (D.view_inj i q)
    (D.view_adj i q) (D.vhang i q) hok₂ tagR 0 bp
    (fun a b m r _ hb hadj hab he => h₂ i q a b m r hadj hab he (by
      unfold BlockDecomp.halfR
      rw [← hhq]; exact half_sub hok₂ (Fin.zero_le a) hb hab))
    (fun k h1 h2 => hangBuild hsplit _ i _ le_rfl (h₂.mono (fun v hv =>
      mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inr ⟨k, h1, h2, hv⟩))))))
    bp.val 0 bp (by simp) le_rfl le_rfl hbp0 hadj₂ (T₂ ∪ X₁) tg₃ hT₃
    (by rw [hq0, hT₂def]; simp) (by rw [hqb, hT₂def]; simp)
    (fun k h1 h2 v hv hvT => by
      obtain ⟨n1, n2⟩ := hk₂ k h1 h2
      rw [vhang_apply] at hv
      rcases hT₃mem v hvT with h | h | h | ⟨k', h1', h2', h⟩
      · exact hnT _ v hv h
      · exact n2 (D.hang_disj hv h)
      · exact n1 (D.hang_disj hv h)
      · have e := D.hang_disj hv h
        apply arc_disj p q (rot q k)
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rw [e, show rot p k' - p = k' from (rot_eq_iff.mp rfl).symm]; exact h1'
        · rw [e, show rot p k' - p = k' from (rot_eq_iff.mp rfl).symm]; exact h2'
        · rw [show rot q k - q = k from (rot_eq_iff.mp rfl).symm]; exact h1
        · rw [show rot q k - q = k from (rot_eq_iff.mp rfl).symm]; exact h2)
    (by
      rw [hq0, hqb, p₃ _ (by rw [hT₂def]; simp) _ (by rw [hT₂def]; simp)
        (fun h => hne' (by rw [hp0] at h; exact h.1.symm))]
      exact e₂)
  refine ⟨tg₄, ?_⟩
  have hset : T₂ ∪ X₁ ∪ X₂ = T ∪ (D.halfR i p q ∪ D.halfR i q p) := by
    have e1 : D.halfR i p q = X₁ ∪ D.hang i p := by rw [hX₁, hbq]; rfl
    have e2 : D.halfR i q p = X₂ ∪ D.hang i q := by rw [hX₂, hbp]; rfl
    rw [e1, e2]
    have hTT : T ⊆ T₂ := fun v hv => by
      rw [hT₂def]
      exact mem_union_left _ (mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem hv)))
    have hpT₂ : D.hang i p ⊆ T₂ := fun v hv => by
      rw [hT₂def]; exact mem_union_left _ (mem_union_right _ hv)
    have hqT₂ : D.hang i q ⊆ T₂ := fun v hv => by
      rw [hT₂def]; exact mem_union_right _ hv
    apply Subset.antisymm
    · intro v hv
      rcases mem_union.mp hv with hv | hv
      · rcases mem_union.mp hv with hv | hv
        · rcases hT₂mem v hv with h | h | h
          · exact mem_union_left _ h
          · exact mem_union_right _ (mem_union_left _ (mem_union_right _ h))
          · exact mem_union_right _ (mem_union_right _ (mem_union_right _ h))
        · exact mem_union_right _ (mem_union_left _ (mem_union_left _ hv))
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ hv))
    · intro v hv
      rcases mem_union.mp hv with h | h
      · exact mem_union_left _ (mem_union_left _ (hTT h))
      · rcases mem_union.mp h with h | h
        · rcases mem_union.mp h with h | h
          · exact mem_union_left _ (mem_union_right _ h)
          · exact mem_union_left _ (mem_union_left _ (hpT₂ h))
        · rcases mem_union.mp h with h | h
          · exact mem_union_right _ h
          · exact mem_union_left _ (mem_union_left _ (hqT₂ h))
  rw [← hset]; exact hT₄

end Outerplanar
