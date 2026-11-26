/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SevenBlocks
import Outerplanar.ThirteenSys

/-!
# Outerplanar graphs with at most thirteen even faces per component

**`ecc_three_of_blocks_thirteen`**: a graph with a block decomposition
(`Outerplanar/BlockModel.lean`: its blocks are polygon dissections or single edges, arranged in a
tree) whose connected components have at most thirteen even faces in their blocks is 3-ECC;
bridges, cut vertices, isolated vertices and odd faces are unrestricted.
**`ecc_three_of_blocks_thirteen_connected`**: the connected case. This is the thirteen-even-face
theorem of the research note `ai_research_notes/OUTERPLANAR_THIRTEEN_AND_GAUGE_OBSTRUCTION_2026-11-23.md`
(another AI session of this repository's collaboration; audited); formalized by Claude.

The proof instantiates the generic building of `Outerplanar/BranchBuild.lean` with the class system
of `Outerplanar/ThirteenSys.lean`, one component at a time:

* if some edge has two halves with at most six marks each, the base is that edge and the tags are
  `small (marks)` up to six marks, `triv` above (`tag13 none`);
* otherwise the base is the edge of a half `X₀` with at least seven marks and the fewest vertices
  (the weighted centroid of the note): inside it every child region of a face lies in a smaller
  half, so has at most six marks (`ruleOn_X₀`), and the other half has at most six; the regions
  inside `X₀` with at least seven marks get the dual tag `top (T - marks)`, `T` the marks of the
  component (`tag13 (some X₀)`);
* `SplitOK` holds for every region: a branch is a half (`brR_half`), so a branch with seven marks
  inside `X₀` is `X₀` itself (`splitOK_some`).
-/

namespace Outerplanar

open Finset BlockDecomp

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {ι : Type} [Fintype ι] [DecidableEq ι] (D : BlockDecomp G ι)

namespace BlockDecomp

open Classical in
/-- **The tags**: small up to six marks; inside the centroid half `X₀` the dual of the rest of the
component; trivial otherwise. -/
noncomputable def tag13 (X₀ : Option (Finset V)) (T : ℕ) (U : Finset V) : T13 :=
  if D.marksR U ≤ 6 then .small (D.marksR U)
  else match X₀ with
    | some X => if U ⊆ X then .top (T - D.marksR U) else .triv
    | none => .triv

variable {D}

theorem tag13_small {X₀ : Option (Finset V)} {T : ℕ} {U : Finset V} (h : D.marksR U ≤ 6) :
    D.tag13 X₀ T U = .small (D.marksR U) := by
  unfold tag13; simp [h]

theorem tag13_top {X : Finset V} {T : ℕ} {U : Finset V} (h : 7 ≤ D.marksR U) (hU : U ⊆ X) :
    D.tag13 (some X) T U = .top (T - D.marksR U) := by
  unfold tag13; simp [show ¬ D.marksR U ≤ 6 by omega, hU]

theorem tag13_triv_some {X : Finset V} {T : ℕ} {U : Finset V} (h : 7 ≤ D.marksR U)
    (hU : ¬ U ⊆ X) : D.tag13 (some X) T U = .triv := by
  unfold tag13; simp [show ¬ D.marksR U ≤ 6 by omega, hU]

theorem tag13_triv_none {T : ℕ} {U : Finset V} (h : 7 ≤ D.marksR U) :
    D.tag13 none T U = .triv := by
  unfold tag13; simp [show ¬ D.marksR U ≤ 6 by omega]

/-! ### The face rule at a side -/

/-- **The face rule at the root face of a side**: children with at most six marks if the side has
seven, and then the side lies in the centroid half. -/
theorem rule13_view (X₀ : Option (Finset V)) (T : ℕ) (j : ι) (c a b : Fin (D.n j)) (m : ℕ)
    (r : Fin (m + 2) → Fin (D.n j)) (hadj : (D.vH j c).Adj a b) (hab : a < b)
    (he : RootEnum (D.vH j c) a b m r)
    (hc : 7 ≤ D.marksR (sideR (D.vψ j c) (D.vhang j c) a b) →
      ∀ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i) ≤ 6)
    (htop : 7 ≤ D.marksR (sideR (D.vψ j c) (D.vhang j c) a b) →
      ∃ X, X₀ = some X ∧ sideR (D.vψ j c) (D.vhang j c) a b ⊆ X ∧
        D.marksR (sideR (D.vψ j c) (D.vhang j c) a b) ≤ T ∧ T ≤ 13) :
    rule13 (D.tag13 X₀ T (sideR (D.vψ j c) (D.vhang j c) a b)) m
      fun i => D.tag13 X₀ T (childR (D.vψ j c) (D.vhang j c) r i) := by
  have hside := marksR_side hadj hab he
  have hevm : Even (m + 2) ↔ Even m := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have hfle : ∀ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i)
      ≤ ∑ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i) := fun i =>
    Finset.single_le_sum (f := fun i => D.marksR (childR (D.vψ j c) (D.vhang j c) r i))
      (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hsum : D.marksR (sideR (D.vψ j c) (D.vhang j c) a b)
      = (if Even m then 1 else 0) + ∑ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i) := by
    rw [hside]; simp only [hevm]
  rcases Nat.lt_or_ge (D.marksR (sideR (D.vψ j c) (D.vhang j c) a b)) 7 with h6 | h7
  · left
    refine ⟨_, fun i => D.marksR (childR (D.vψ j c) (D.vhang j c) r i), tag13_small (by omega),
      fun i => tag13_small ?_, he.one_le, by beta_reduce; omega, by omega⟩
    have := hfle i
    split_ifs at hsum <;> omega
  · right; left
    obtain ⟨X, rfl, hsub, hT, hT13⟩ := htop h7
    refine ⟨_, fun i => D.marksR (childR (D.vψ j c) (D.vhang j c) r i), tag13_top h7 hsub,
      fun i => tag13_small (hc h7 i), he.one_le, fun hev => ?_⟩
    simp only [hev, ↓reduceIte] at hsum
    beta_reduce
    omega

/-! ### A branch is a half -/

theorem brR_half (j : ι) (z₀ : Fin (D.n j)) :
    ∃ c, (D.H j).Adj c z₀ ∧ D.brR j z₀ = D.halfR j c z₀ := by
  have hn := D.two_le j
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
  have hψ0 : D.vψ j c 0 = D.ψ j c := by rw [vψ_apply, hr0]
  have hψb : D.vψ j c b₀ = D.ψ j z₀ := by rw [vψ_apply, hrb]
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
  have hBr : D.brR j z₀ = sideR (D.vψ j c) (D.vhang j c) 0 b₀ ∪ D.hang j c := by
    ext v
    rw [mem_brR, mem_union, mem_sideR]
    constructor
    · rintro (rfl | ⟨z, hz, hv⟩)
      · exact Or.inl (Or.inr (Or.inl hψb.symm))
      · by_cases hzc : z = c
        · subst hzc; exact Or.inr hv
        · obtain ⟨h1, h2⟩ := hint z hz hzc
          refine Or.inl (Or.inr (Or.inr ⟨z - c, h1, h2, ?_⟩))
          rw [vhang_apply, rot_sub']; exact hv
    · rintro ((h | h | ⟨k, h1, h2, hv⟩) | hv)
      · rw [hψ0] at h
        exact Or.inr ⟨c, hc0, h ▸ D.hang_self j c⟩
      · rw [hψb] at h; exact Or.inl h
      · exact Or.inr ⟨rot c k, (hidx k h1 h2).1, hv⟩
      · exact Or.inr ⟨c, hc0, hv⟩
  have hadj : (D.H j).Adj c z₀ := by
    have h := (D.view_diss j c).2.1 0 b₀ rfl (by rw [hb₀v]; omega) (ne_of_lt hb₀pos)
    have h' : (D.H j).Adj (rot c 0) (rot c b₀) := h
    rwa [hr0, hrb] at h'
  refine ⟨c, hadj, ?_⟩
  have hs := half_shift (D := D) (j := j) (c := c) hb₀pos
  rw [hr0, hrb, vhang_apply, hr0] at hs
  rw [hBr, hs]

/-! ### The vertex rule for every split -/

theorem splitOK_none (T : ℕ) : SplitOK (R := sys13) D vrule13 (D.tag13 none T) := by
  intro j z₀ X hx hX
  have hu := marksR_union (sep_brR hx hX)
  rcases Nat.lt_or_ge (D.marksR (X ∪ D.brR j z₀)) 7 with h6 | h7
  · left
    exact ⟨_, _, _, tag13_small (by omega), tag13_small (by omega), tag13_small (by omega),
      by omega, by omega⟩
  · right; left
    exact tag13_triv_none h7

/-- **The vertex rule for every split, the centroid half `X₀` given.** -/
theorem splitOK_some {v₀ : V} {X₀ : Finset V} {T : ℕ} (hX₀ : X₀ ⊆ compR G v₀)
    (hT : D.marksR (compR G v₀) = T) (hT13 : T ≤ 13)
    (hmin : ∀ j (c z : Fin (D.n j)), (D.H j).Adj c z → G.Reachable v₀ (D.ψ j c) →
      7 ≤ D.marksR (D.halfR j c z) → X₀.card ≤ (D.halfR j c z).card) :
    SplitOK (R := sys13) D vrule13 (D.tag13 (some X₀) T) := by
  intro j z₀ X hx hX
  have hu := marksR_union (sep_brR hx hX)
  rcases Nat.lt_or_ge (D.marksR (X ∪ D.brR j z₀)) 7 with h6 | h7
  · left
    exact ⟨_, _, _, tag13_small (by omega), tag13_small (by omega), tag13_small (by omega),
      by omega, by omega⟩
  by_cases hsub : X ∪ D.brR j z₀ ⊆ X₀
  swap
  · right; left
    exact tag13_triv_some h7 hsub
  have hle : D.marksR (X ∪ D.brR j z₀) ≤ T := hT ▸ marksR_mono (hsub.trans hX₀)
  rw [tag13_top h7 hsub]
  rcases Nat.lt_or_ge (D.marksR X) 7 with hx6 | hx7
  · rcases Nat.lt_or_ge (D.marksR (D.brR j z₀)) 7 with hb6 | hb7
    · right; right; right; left
      exact ⟨_, _, _, rfl, tag13_small (by omega), tag13_small (by omega)⟩
    · -- the branch is the centroid half itself, and `X` is a single vertex
      obtain ⟨c, hcz, hBc⟩ := brR_half (D := D) j z₀
      have hBX₀ : D.brR j z₀ ⊆ X₀ := subset_union_right.trans hsub
      have hreach : G.Reachable v₀ (D.ψ j c) := by
        have : D.ψ j c ∈ D.brR j z₀ := by
          rw [mem_brR]
          exact Or.inr ⟨c, hcz.ne, D.hang_self j c⟩
        exact mem_compR.mp (hX₀ (hBX₀ this))
      have hcard := hmin j c z₀ hcz hreach (by rw [← hBc]; exact hb7)
      rw [← hBc] at hcard
      have hEq : D.brR j z₀ = X₀ := eq_of_subset_of_card_le hBX₀ hcard
      have hXB : X ∪ D.brR j z₀ = D.brR j z₀ := union_eq_right.mpr (subset_union_left.trans (hsub.trans hEq.symm.le))
      have hx0 : D.marksR X = 0 := by rw [hXB] at hu; omega
      right; right; right; right
      refine ⟨_, rfl, by rw [tag13_small (by omega), hx0], ?_, by omega⟩
      rw [tag13_top hb7 hBX₀, hXB]
  · right; right; left
    have hb6 : D.marksR (D.brR j z₀) ≤ 6 := by omega
    exact ⟨_, _, _, rfl, tag13_top hx7 (subset_union_left.trans hsub), tag13_small hb6,
      by omega, by omega⟩

/-! ### The face rule in the halves -/

theorem ruleOn_light13 (X₀ : Option (Finset V)) (T : ℕ) {U : Finset V} (hU : D.marksR U ≤ 6) :
    RuleOn (R := sys13) D rule13 (D.tag13 X₀ T) U :=
  fun j c a b m r hadj hab he hsub => rule13_view X₀ T j c a b m r hadj hab he
    (fun h => absurd ((marksR_mono (subset_union_left.trans hsub)).trans hU) (by omega))
    (fun h => absurd ((marksR_mono (subset_union_left.trans hsub)).trans hU) (by omega))

variable (D) in
/-- **The base edge of a component, with its tags.** -/
theorem exists_base13 (v₀ : V) (i₀ : ι) (y₀ : Fin (D.n i₀)) (h₀ : G.Reachable v₀ (D.ψ i₀ y₀))
    (h13 : D.marksR (compR G v₀) ≤ 13) :
    ∃ (tagR : Finset V → T13) (i : ι) (p q : Fin (D.n i)), (D.H i).Adj p q ∧
      G.Reachable v₀ (D.ψ i p) ∧ SplitOK (R := sys13) D vrule13 tagR ∧
      glue13 (tagR (D.halfR i p q)) (tagR (D.halfR i q p)) ∧
      RuleOn (R := sys13) D rule13 tagR (D.halfR i p q) ∧
      RuleOn (R := sys13) D rule13 tagR (D.halfR i q p) := by
  classical
  set T := D.marksR (compR G v₀) with hT
  have hM : ∀ i (p q : Fin (D.n i)), (D.H i).Adj p q → G.Reachable v₀ (D.ψ i p) →
      D.marksR (D.halfR i p q) + D.marksR (D.halfR i q p) = T := by
    intro i p q hpq hr
    rw [marks_halves hpq, compR_eq hr]
  by_cases hA : ∃ i p q, (D.H i).Adj p q ∧ G.Reachable v₀ (D.ψ i p) ∧
      D.marksR (D.halfR i p q) ≤ 6 ∧ D.marksR (D.halfR i q p) ≤ 6
  · obtain ⟨i, p, q, hpq, hr, h1, h2⟩ := hA
    exact ⟨D.tag13 none T, i, p, q, hpq, hr, splitOK_none T,
      Or.inl ⟨_, _, tag13_small h1, tag13_small h2⟩, ruleOn_light13 none T h1,
      ruleOn_light13 none T h2⟩
  push Not at hA
  have hn := D.two_le i₀
  have h01 : (D.H i₀).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := (D.diss i₀).1 _ _ rfl
  have hr0 : G.Reachable v₀ (D.ψ i₀ ⟨0, by omega⟩) := h₀.trans (block_reachable _ _)
  have hr1 : G.Reachable v₀ (D.ψ i₀ ⟨1, by omega⟩) := h₀.trans (block_reachable _ _)
  have hex : ∃ d, ∃ i p q, (D.H i).Adj p q ∧ G.Reachable v₀ (D.ψ i p) ∧
      7 ≤ D.marksR (D.halfR i p q) ∧ (D.halfR i p q).card = d := by
    by_cases h : 7 ≤ D.marksR (D.halfR i₀ ⟨0, by omega⟩ ⟨1, by omega⟩)
    · exact ⟨_, i₀, _, _, h01, hr0, h, rfl⟩
    · exact ⟨_, i₀, _, _, h01.symm, hr1, by have := hA i₀ _ _ h01 hr0 (by omega); omega, rfl⟩
  obtain ⟨i, p, q, hpq, hr, h7, hd⟩ := Nat.find_spec hex
  have hmin : ∀ i' (p' q' : Fin (D.n i')), (D.H i').Adj p' q' → G.Reachable v₀ (D.ψ i' p') →
      7 ≤ D.marksR (D.halfR i' p' q') → (D.halfR i p q).card ≤ (D.halfR i' p' q').card :=
    fun i' p' q' h1 h2 h3 => hd ▸ Nat.find_min' hex ⟨i', p', q', h1, h2, h3, rfl⟩
  have hOK : D.halfR i p q ⊆ compR G v₀ := by
    rw [← compR_eq hr, ← halves_union hpq.ne]; exact subset_union_left
  have hT13 : T ≤ 13 := h13
  have hY : D.marksR (D.halfR i q p) ≤ 6 := by have := hM i p q hpq hr; omega
  refine ⟨D.tag13 (some (D.halfR i p q)) T, i, p, q, hpq, hr, splitOK_some hOK rfl hT13 hmin, ?_, ?_,
    ruleOn_light13 _ T hY⟩
  · right; left
    refine ⟨_, tag13_top h7 subset_rfl, ?_⟩
    rw [tag13_small hY]
    congr 1
    have := hM i p q hpq hr
    omega
  -- the centroid half: every child region lies in a smaller half
  intro j c a b m r hadj hab he hsub
  refine rule13_view (some (D.halfR i p q)) T j c a b m r hadj hab he (fun _ i' => ?_)
    fun _ => ⟨(D.halfR i p q), rfl, subset_union_left.trans hsub,
      hT ▸ marksR_mono ((subset_union_left.trans hsub).trans hOK), hT13⟩
  set Hc := sideR (D.vψ j c) (D.vhang j c) (r i'.castSucc) (r i'.succ) ∪
    D.vhang j c (r i'.castSucc) with hHc
  have hchild : childR (D.vψ j c) (D.vhang j c) r i' ⊆ Hc := by
    unfold childR
    split_ifs
    · exact subset_union_left
    · exact subset_rfl
  have hshift : Hc = D.halfR j (rot c (r i'.castSucc)) (rot c (r i'.succ)) := half_shift (he.lt i')
  have hadjc : (D.H j).Adj (rot c (r i'.castSucc)) (rot c (r i'.succ)) :=
    he.adj (D.view_diss j c) hadj hab i'
  have hok := D.view_hangOK j c
  have hHcO : Hc ⊆ (D.halfR i p q) := (half_sub hok (he.ge _) (he.le _) (he.lt i')).trans hsub
  have hrc : G.Reachable v₀ (D.ψ j (rot c (r i'.castSucc))) :=
    mem_compR.mp (hOK (hHcO (mem_union_left _ (mem_insert_self _ _))))
  have hm1 := he.one_le
  obtain ⟨l, hl1, hl2⟩ : ∃ l : Fin (m + 2), l.val ≠ i'.val ∧ l.val ≠ i'.val + 1 := by
    by_cases hi : i'.val + 1 < m + 1
    · exact ⟨Fin.last (m + 1), by simp; omega, by simp; omega⟩
    · exact ⟨0, by simp; omega, by simp⟩
  have hlS : D.vψ j c (r l) ∈ sideR (D.vψ j c) (D.vhang j c) a b := by
    rcases (he.ge l).lt_or_eq with h1 | h1
    · rcases (he.le l).lt_or_eq with h2 | h2
      · exact mem_sideR.mpr (Or.inr (Or.inr ⟨r l, h1, h2, hok.self _⟩))
      · rw [h2]; exact mem_sideR.mpr (Or.inr (Or.inl rfl))
    · rw [← h1]; exact mem_sideR.mpr (Or.inl rfl)
  have hlHc : D.vψ j c (r l) ∉ Hc := by
    intro h
    have key : ∀ z, D.vψ j c (r l) ∈ D.vhang j c z → r l = z := fun z hz => by
      have := vψ_mem_vhang (y := rot c (r l)) hz
      simpa [rot] using this
    rcases mem_union.mp h with h | h
    · obtain ⟨z, h1, h2, h3, -, -⟩ := anchor_sideR h (he.lt i')
      have e := key z h3
      rw [← e] at h1 h2
      have h1' : i'.castSucc ≤ l := he.mono.le_iff_le.mp h1
      have h2' : l ≤ i'.succ := he.mono.le_iff_le.mp h2
      have : i'.val ≤ l.val := h1'
      have : l.val ≤ i'.val + 1 := h2'
      omega
    · have e := he.mono.injective (key _ h)
      exact hl1 (by rw [e]; simp)
  have hlt : Hc.card < (D.halfR i p q).card :=
    card_lt_card ((ssubset_iff_of_subset hHcO).mpr ⟨_, hsub (mem_union_left _ hlS), hlHc⟩)
  have hle6 : D.marksR Hc ≤ 6 := by
    by_contra h
    have := hmin j _ _ hadjc hrc (by rw [← hshift]; omega)
    rw [← hshift] at this
    omega
  exact (marksR_mono hchild).trans hle6

end BlockDecomp

/-! ### The theorem -/

/-- **A graph whose blocks are polygon dissections or single edges, with at most thirteen even
faces in the blocks of each connected component, is 3-ECC**: every assignment of lists of three
colours has at least as many proper colourings as there are `3`-colourings. Bridges, cut
vertices, isolated vertices and odd faces are unrestricted. The blocks of the component of `v₀`
are the blocks `i` whose vertex `ψ i 0` is reachable from `v₀`. -/
theorem ecc_three_of_blocks_thirteen (D : BlockDecomp G ι)
    (h13 : ∀ v₀ : V, ∑ i ∈ univ.filter (fun i => G.Reachable v₀ (D.ψ i 0)),
      numEvenFaces (D.H i) ≤ 13) :
    G.ECCAt 3 := by
  classical
  have key : ∀ (n : ℕ) (s : Finset V), s.card ≤ n → (∀ v ∈ s, ∀ w, G.Reachable v w → w ∈ s) →
      ∃ tg, TagBuiltW G sys13 rule13 glue13 vrule13 s tg := by
    intro n
    induction n with
    | zero =>
      intro s hs _
      have : s = ∅ := card_eq_zero.mp (by omega)
      subst this
      exact ⟨_, TagBuiltW.empty (fun _ _ => T13.small 0)⟩
    | succ n ih =>
      intro s hs hcl
      rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
      · exact ⟨_, TagBuiltW.empty (fun _ _ => T13.small 0)⟩
      set K := compR G v₀ with hK
      have hKs : K ⊆ s := fun w hw => hcl v₀ hv₀ w (mem_compR.mp hw)
      have hv₀K : v₀ ∈ K := mem_compR.mpr (SimpleGraph.Reachable.refl _)
      have hcl' : ∀ v ∈ s \ K, ∀ w, G.Reachable v w → w ∈ s \ K := by
        intro v hv w hw
        obtain ⟨hvs, hvK⟩ := mem_sdiff.mp hv
        refine mem_sdiff.mpr ⟨hcl v hvs w hw, fun hwK => hvK ?_⟩
        exact mem_compR.mpr ((mem_compR.mp hwK).trans hw.symm)
      have hcard : (s \ K).card ≤ n := by
        have := card_lt_card ((ssubset_iff_of_subset (sdiff_subset (s := s) (t := K))).mpr
          ⟨v₀, hv₀, fun h => (mem_sdiff.mp h).2 hv₀K⟩)
        omega
      obtain ⟨tg', hT'⟩ := ih (s \ K) hcard hcl'
      have hset : s \ K ∪ K = s := sdiff_union_of_subset hKs
      by_cases hblk : ∃ (i : ι) (y : Fin (D.n i)), G.Reachable v₀ (D.ψ i y)
      · obtain ⟨i₀, y₀, h₀⟩ := hblk
        obtain ⟨tagR, i, p, q, hpq, hr, hsplit, hg, h1, h2⟩ := D.exists_base13 v₀ i₀ y₀ h₀
          (by rw [D.marksR_comp]; exact h13 v₀)
        obtain ⟨tg, h⟩ := buildComp (D := D) (R := sys13) (rule := rule13) (glue := glue13)
          (vrule := vrule13) (tagR := tagR) hsplit i p q hpq hg h1 h2 (s \ K) tg' hT'
          (fun v hv hrv => (mem_sdiff.mp hv).2 (mem_compR.mpr (hr.trans hrv)))
        rw [halves_union hpq.ne, compR_eq hr, ← hK, hset] at h
        exact ⟨tg, h⟩
      · -- an isolated vertex
        push Not at hblk
        have hiso : ∀ w, ¬ G.Adj v₀ w := fun w h => by
          obtain ⟨i, a, b, -, ha, -⟩ := (D.adj v₀ w).mp h
          exact hblk i a (by rw [ha])
        have hK1 : K = {v₀} := by
          ext w
          rw [mem_singleton, mem_compR]
          refine ⟨fun h => ?_, fun h => h ▸ SimpleGraph.Reachable.refl _⟩
          exact reach_closed (G' := G) (s := v₀) (P := fun w => w = v₀) rfl
            (fun u w _ huw hu => absurd (hu ▸ huw) (hiso w)) h
        have := TagBuiltW.iso (s \ K) tg' v₀ (fun h => (mem_sdiff.mp h).2 hv₀K)
          (fun z _ => hiso z) hT'
        have hs' : insert v₀ (s \ K) = s := by rw [insert_eq, union_comm, ← hK1, hset]
        rw [hs'] at this
        exact ⟨tg', this⟩
  obtain ⟨tg, h⟩ := key _ univ le_rfl fun _ _ _ _ => mem_univ _
  exact ecc_three_of_thirteenBuiltW G h

/-- **A connected graph whose blocks are polygon dissections or single edges, with at most
thirteen even faces in all its blocks, is 3-ECC.** -/
theorem ecc_three_of_blocks_thirteen_connected (D : BlockDecomp G ι) (hc : G.Connected)
    (h13 : ∑ i, numEvenFaces (D.H i) ≤ 13) : G.ECCAt 3 :=
  ecc_three_of_blocks_thirteen D fun v₀ => by
    rw [filter_true_of_mem fun i _ => hc.preconnected _ _]
    exact h13

end Outerplanar
