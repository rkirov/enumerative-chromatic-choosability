/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.BlockFaces
import Outerplanar.SevenCount
import Outerplanar.SevenSwap

/-!
# Outerplanar graphs with at most seven even faces, cut vertices included

**`ecc_three_of_blocks_seven`**: a graph with a block decomposition (`Outerplanar/BlockModel.lean`:
its blocks are polygon dissections or single edges, arranged in a tree) whose blocks have at most
seven even faces in each connected component is 3-ECC; bridges, cut vertices, isolated vertices
and odd faces are unrestricted. **`ecc_three_of_blocks_seven_connected`**: the connected case,
with the bound on all blocks together. This is the seven-even-face theorem of the research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md` (another AI session of this
repository's collaboration) with its cut-vertex bookkeeping; formalized by Claude. The 2-connected
case is `ecc_three_of_seven_even` (`Outerplanar/SevenEven.lean`).

The proof instantiates the generic building of `Outerplanar/BranchBuild.lean`:

* the *marks* of a vertex region `U` (`marksR`, `Outerplanar/BlockFaces.lean`) are the even faces
  of all blocks lying in `U`, and `sqR U` says that one of them is a square; the tag of `U` is
  `tag7N` of these (`Outerplanar/SevenCount.lean`);
* the vertex rule `VCond` (`Outerplanar/SevenVertex.lean`) holds for the tags of two regions whose
  faces are separated (`vcond_tagR`), in particular for a branch and what it is attached to;
* at the root face of a side the marks of the side are those of the root face and of the
  children, the branches at an interior vertex of the face counted with the path edge after it
  (`marksR_side`), so the face rule holds when the side has at most four marks or the children
  at most two each (`rule_view`);
* the base edge (`exists_base`): an edge both of whose halves have at most four marks if there
  is one; otherwise a half with at least five marks and the fewest vertices, inside which every
  child region of a face is a smaller half, hence has at most two marks;
* the components one after the other (`buildComp`), an isolated vertex by itself.
-/

namespace Outerplanar

open Finset BlockDecomp

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {ι : Type} [Fintype ι] [DecidableEq ι] (D : BlockDecomp G ι)

namespace BlockDecomp

/-- **The tag of a region**: by its marks, and whether a single mark is a square. -/
noncomputable def tagR (U : Finset V) : STag := tag7N (D.marksR U) (D.sqR U)

end BlockDecomp

/-! ### The vertex rule -/

/-- **The vertex rule holds for a product of two nonempty tags.** -/
theorem vcond_prod {k₀ k₁ : ℕ} (h₀ : 1 ≤ k₀) (h₁ : 1 ≤ k₁) (sq s₀ s₁ : Prop) :
    VCond (tag7N (k₀ + k₁) sq) (tag7N k₀ s₀) (tag7N k₁ s₁) := by
  right; right
  have hp : 0 ≤ (tagN k₀ s₀).tv * (tagN k₁ s₁).tv := mul_nonneg (tagN k₀ s₀).tv0 (tagN k₁ s₁).tv0
  have hpf : 0 ≤ (tagN k₀ s₀).fl * (tagN k₁ s₁).fl := mul_nonneg (tagN k₀ s₀).fl0 (tagN k₁ s₁).fl0
  show ((tagN (k₀ + k₁) sq).mb = true → (tagN k₀ s₀).mb = true) ∧
    (tagN (k₀ + k₁) sq).tv ≤ (tagN k₀ s₀).tv * (tagN k₁ s₁).tv ∧
    (tagN (k₀ + k₁) sq).fl ≤ (tagN k₀ s₀).fl * (tagN k₁ s₁).fl ∧ (tagN (k₀ + k₁) sq).hull = false ∧
    ((tag7N (k₀ + k₁) sq).ball = true → (tag7N k₀ s₀).isBall ∧ (tag7N k₁ s₁).isBall) ∧
    (tag7N (k₀ + k₁) sq).gain = false
  have hball : (tag7N (k₀ + k₁) sq).ball = true → (tag7N k₀ s₀).isBall ∧ (tag7N k₁ s₁).isBall :=
    fun hball => by
      have := tag7N_ball_le hball
      exact ⟨tag7N_isBall (by omega), tag7N_isBall (by omega)⟩
  have hgain : (tag7N (k₀ + k₁) sq).gain = false := by
    unfold tag7N
    simp only [decide_eq_false_iff_not]
    omega
  rcases (by omega : k₀ + k₁ = 2 ∨ 3 ≤ k₀ + k₁) with h | h
  · rw [tagN_two h, tagN_one_tv (show k₀ = 1 by omega), tagN_one_tv (show k₁ = 1 by omega)]
    refine ⟨fun _ => tagN_one_mb (by omega), ?_, hpf, rfl, hball, hgain⟩
    show (1 / 2 : ℝ) ≤ 3 / 4 * (3 / 4)
    norm_num
  · rw [tagN_three h]
    exact ⟨fun h => absurd h (by decide), hp, hpf, rfl, hball, hgain⟩

namespace BlockDecomp

variable {D}

/-- **The vertex rule holds for the tags of separated regions.** -/
theorem vcond_tagR {X Y : Finset V} (h : D.Sep X Y) :
    VCond (D.tagR (X ∪ Y)) (D.tagR X) (D.tagR Y) := by
  unfold tagR
  rw [marksR_union h]
  rcases Nat.eq_zero_or_pos (D.marksR Y) with h1 | h1
  · left
    refine ⟨tag7N_zero h1, ?_⟩
    rw [h1, add_zero]
    congr 1
    apply propext
    rw [sqR_union h]
    exact ⟨fun h' => h'.resolve_right fun hs => by
      have := marksR_pos_of_sqR hs; omega, Or.inl⟩
  rcases Nat.eq_zero_or_pos (D.marksR X) with h0 | h0
  · right; left
    refine ⟨tag7N_zero h0, ?_⟩
    rw [h0, zero_add]
    congr 1
    apply propext
    rw [sqR_union h]
    exact ⟨fun h' => h'.resolve_left fun hs => by
      have := marksR_pos_of_sqR hs; omega, Or.inr⟩
  · exact vcond_prod h0 h1 _ _ _

theorem splitOK_seven : SplitOK (R := sevenSys) D VCond D.tagR :=
  fun _ _ _ hx hX => vcond_tagR (sep_brR hx hX)

end BlockDecomp

namespace BlockDecomp

variable {D} {j : ι} {c : Fin (D.n j)}

variable (D) in
/-- **The face rule at the root face of a side** with at most four marks, or whose children
have at most two marks each. -/
theorem rule_view (j : ι) (c a b : Fin (D.n j)) (m : ℕ) (r : Fin (m + 2) → Fin (D.n j))
    (hadj : (D.vH j c).Adj a b) (hab : a < b)
    (he : RootEnum (D.vH j c) a b m r)
    (hg : D.marksR (sideR (D.vψ j c) (D.vhang j c) a b) ≤ 4 ∨
      ∀ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i) ≤ 2) :
    sevenRule (D.tagR (sideR (D.vψ j c) (D.vhang j c) a b)) m
      fun i => D.tagR (childR (D.vψ j c) (D.vhang j c) r i) :=
  rule7_of_counts he.one_le (marksR_side hadj hab he)
    (fun _ h0 => sqR_side_root hadj hab he h0)
    (fun hodd i₀ _ h0 => sqR_side_child hadj hab he hodd i₀ h0)
    (hg.imp id fun h _ _ => h)

variable (D) in
/-- **A region with at most four marks satisfies the face rule.** -/
theorem ruleOn_light {U : Finset V} (hU : D.marksR U ≤ 4) :
    RuleOn (R := sevenSys) D sevenRule D.tagR U :=
  fun j c a b m r hadj hab he hsub => rule_view D j c a b m r hadj hab he
    (Or.inl ((marksR_mono (subset_union_left.trans hsub)).trans hU))

/-! ### The base edge -/

variable (D) in
/-- **The base edge of a component**: both halves satisfy the face rule. -/
theorem exists_base (v₀ : V) (i₀ : ι) (y₀ : Fin (D.n i₀)) (h₀ : G.Reachable v₀ (D.ψ i₀ y₀))
    (h7 : D.marksR (compR G v₀) ≤ 7) :
    ∃ i p q, (D.H i).Adj p q ∧ G.Reachable v₀ (D.ψ i p) ∧
      RuleOn (R := sevenSys) D sevenRule D.tagR (D.halfR i p q) ∧
      RuleOn (R := sevenSys) D sevenRule D.tagR (D.halfR i q p) := by
  classical
  have hM : ∀ i (p q : Fin (D.n i)), (D.H i).Adj p q → G.Reachable v₀ (D.ψ i p) →
      D.marksR (D.halfR i p q) + D.marksR (D.halfR i q p) ≤ 7 := by
    intro i p q hpq hr
    rw [marks_halves hpq, compR_eq hr]; exact h7
  by_cases hA : ∃ i p q, (D.H i).Adj p q ∧ G.Reachable v₀ (D.ψ i p) ∧
      D.marksR (D.halfR i p q) ≤ 4 ∧ D.marksR (D.halfR i q p) ≤ 4
  · obtain ⟨i, p, q, hpq, hr, h1, h2⟩ := hA
    exact ⟨i, p, q, hpq, hr, ruleOn_light D h1, ruleOn_light D h2⟩
  push Not at hA
  have hlight : ∀ i p q, (D.H i).Adj p q → G.Reachable v₀ (D.ψ i p) →
      D.marksR (D.halfR i p q) ≤ 4 → D.marksR (D.halfR i p q) ≤ 2 := by
    intro i p q hpq hr h4
    have := hA i p q hpq hr h4
    have := hM i p q hpq hr
    omega
  have hn := D.two_le i₀
  have h01 : (D.H i₀).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := (D.diss i₀).1 _ _ rfl
  have hr0 : G.Reachable v₀ (D.ψ i₀ ⟨0, by omega⟩) := h₀.trans (block_reachable _ _)
  have hr1 : G.Reachable v₀ (D.ψ i₀ ⟨1, by omega⟩) := h₀.trans (block_reachable _ _)
  have hex : ∃ d, ∃ i p q, (D.H i).Adj p q ∧ G.Reachable v₀ (D.ψ i p) ∧
      5 ≤ D.marksR (D.halfR i p q) ∧ (D.halfR i p q).card = d := by
    by_cases h : 5 ≤ D.marksR (D.halfR i₀ ⟨0, by omega⟩ ⟨1, by omega⟩)
    · exact ⟨_, i₀, _, _, h01, hr0, h, rfl⟩
    · exact ⟨_, i₀, _, _, h01.symm, hr1, by have := hA i₀ _ _ h01 hr0 (by omega); omega, rfl⟩
  obtain ⟨i, p, q, hpq, hr, h5, hd⟩ := Nat.find_spec hex
  have hmin : ∀ i' p' q', (D.H i').Adj p' q' → G.Reachable v₀ (D.ψ i' p') →
      5 ≤ D.marksR (D.halfR i' p' q') → Nat.find hex ≤ (D.halfR i' p' q').card :=
    fun i' p' q' h1 h2 h3 => Nat.find_min' hex ⟨i', p', q', h1, h2, h3, rfl⟩
  have hOK : D.halfR i p q ⊆ compR G v₀ := by
    rw [← compR_eq hr, ← halves_union hpq.ne]; exact subset_union_left
  refine ⟨i, p, q, hpq, hr, ?_, ruleOn_light D (by have := hM i p q hpq hr; omega)⟩
  intro j c a b m r hadj hab he hsub
  refine rule_view D j c a b m r hadj hab he (Or.inr fun i' => ?_)
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
  have hHcO : Hc ⊆ D.halfR i p q := (half_sub hok (he.ge _) (he.le _) (he.lt i')).trans hsub
  have hrc : G.Reachable v₀ (D.ψ j (rot c (r i'.castSucc))) :=
    mem_compR.mp (hOK (hHcO (mem_union_left _ (mem_insert_self _ _))))
  -- a vertex of the root face outside the child
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
    card_lt_card ((ssubset_iff_of_subset hHcO).mpr
      ⟨_, hsub (mem_union_left _ hlS), hlHc⟩)
  have hle4 : D.marksR Hc ≤ 4 := by
    by_contra h
    have := hmin j _ _ hadjc hrc (by rw [← hshift]; omega)
    rw [← hshift] at this
    omega
  have := hlight j _ _ hadjc hrc (by rw [← hshift]; exact hle4)
  rw [← hshift] at this
  exact (marksR_mono hchild).trans this

end BlockDecomp

/-! ### The theorem -/

/-- **A graph whose blocks are polygon dissections or single edges, with at most seven even
faces in the blocks of each connected component, is 3-ECC**: every assignment of lists of three
colours has at least as many proper colourings as there are `3`-colourings. Bridges, cut
vertices, isolated vertices and odd faces are unrestricted. The blocks of the component of `v₀`
are the blocks `i` whose vertex `ψ i 0` is reachable from `v₀`. -/
theorem ecc_three_of_blocks_seven (D : BlockDecomp G ι)
    (h7 : ∀ v₀ : V, ∑ i ∈ univ.filter (fun i => G.Reachable v₀ (D.ψ i 0)),
      numEvenFaces (D.H i) ≤ 7) :
    G.ECCAt 3 := by
  classical
  -- every union of components is built
  have key : ∀ (n : ℕ) (s : Finset V), s.card ≤ n → (∀ v ∈ s, ∀ w, G.Reachable v w → w ∈ s) →
      ∃ tg, TagBuiltW G sevenSys sevenRule (fun _ _ => True) VCond s tg := by
    intro n
    induction n with
    | zero =>
      intro s hs _
      have : s = ∅ := card_eq_zero.mp (by omega)
      subst this
      exact ⟨_, TagBuiltW.empty (fun _ _ => STag.plain)⟩
    | succ n ih =>
      intro s hs hcl
      rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
      · exact ⟨_, TagBuiltW.empty (fun _ _ => STag.plain)⟩
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
        obtain ⟨i, p, q, hpq, hr, h1, h2⟩ := D.exists_base v₀ i₀ y₀ h₀
          (by rw [D.marksR_comp]; exact h7 v₀)
        obtain ⟨tg, h⟩ := buildComp (D := D) (R := sevenSys) (rule := sevenRule)
          (glue := fun _ _ => True) (vrule := VCond) (tagR := D.tagR) splitOK_seven i p q hpq
          trivial h1 h2 (s \ K) tg' hT' (fun v hv hrv => (mem_sdiff.mp hv).2
            (mem_compR.mpr (hr.trans hrv)))
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
  exact ecc_three_of_sevenBuiltW G h

/-- **A connected graph whose blocks are polygon dissections or single edges, with at most seven
even faces in all its blocks, is 3-ECC.** -/
theorem ecc_three_of_blocks_seven_connected (D : BlockDecomp G ι) (hc : G.Connected)
    (h7 : ∑ i, numEvenFaces (D.H i) ≤ 7) : G.ECCAt 3 :=
  ecc_three_of_blocks_seven D fun v₀ => by
    rw [filter_true_of_mem fun i _ => hc.preconnected _ _]
    exact h7

end Outerplanar
