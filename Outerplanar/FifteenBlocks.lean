/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.ThirteenBlocks
import Outerplanar.FifteenSys

/-!
# Outerplanar graphs with at most fifteen even faces per component

**`ecc_three_of_blocks_fifteen`**: a graph with a block decomposition
(`Outerplanar/BlockModel.lean`: its blocks are polygon dissections or single edges, arranged in a
tree) whose connected components have at most fifteen even faces in their blocks is 3-ECC;
bridges, cut vertices, isolated vertices and odd faces are unrestricted.
**`ecc_three_of_blocks_fifteen_connected`**: the connected case. This is the fifteen-even-face
theorem of the research note `ai_research_notes/OUTERPLANAR_FIFTEEN_EVEN_2026-11-25.md` (proof
and certificates by a Claude worker, audited by another; the route is from the thirteen-face note,
probably by the agy session); formalized by Claude (milestone M5 of
`ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).

The proof is that of `Outerplanar/ThirteenBlocks.lean` with the class system of
`Outerplanar/FifteenSys.lean` and the caps raised: small tags up to seven marks; if no edge has two
halves with at most seven marks each, the base is the edge of a half `X₀` with at least eight marks
and the fewest vertices (the weighted centroid of the note), whose child regions have at most seven
marks, and the other half has at most `15 - 8 = 7`.
-/

namespace Outerplanar

open Finset BlockDecomp Outerplanar.F15

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {ι : Type} [Fintype ι] [DecidableEq ι] (D : BlockDecomp G ι)

namespace BlockDecomp

open Classical in
/-- **The tags**: small up to seven marks; inside the centroid half `X₀` the dual of the rest of the
component; trivial otherwise. -/
noncomputable def tag15 (X₀ : Option (Finset V)) (T : ℕ) (U : Finset V) : T15 :=
  if D.marksR U ≤ 7 then .small (D.marksR U)
  else match X₀ with
    | some X => if U ⊆ X then .top (T - D.marksR U) else .triv
    | none => .triv

variable {D}

theorem tag15_small {X₀ : Option (Finset V)} {T : ℕ} {U : Finset V} (h : D.marksR U ≤ 7) :
    D.tag15 X₀ T U = .small (D.marksR U) := by
  unfold tag15; simp [h]

theorem tag15_top {X : Finset V} {T : ℕ} {U : Finset V} (h : 8 ≤ D.marksR U) (hU : U ⊆ X) :
    D.tag15 (some X) T U = .top (T - D.marksR U) := by
  unfold tag15; simp [show ¬ D.marksR U ≤ 7 by omega, hU]

theorem tag15_triv_some {X : Finset V} {T : ℕ} {U : Finset V} (h : 8 ≤ D.marksR U)
    (hU : ¬ U ⊆ X) : D.tag15 (some X) T U = .triv := by
  unfold tag15; simp [show ¬ D.marksR U ≤ 7 by omega, hU]

theorem tag15_triv_none {T : ℕ} {U : Finset V} (h : 8 ≤ D.marksR U) :
    D.tag15 none T U = .triv := by
  unfold tag15; simp [show ¬ D.marksR U ≤ 7 by omega]

/-! ### The face rule at a side -/

/-- **The face rule at the root face of a side**: children with at most seven marks if the side has
eight, and then the side lies in the centroid half. -/
theorem rule15_view (X₀ : Option (Finset V)) (T : ℕ) (j : ι) (c a b : Fin (D.n j)) (m : ℕ)
    (r : Fin (m + 2) → Fin (D.n j)) (hadj : (D.vH j c).Adj a b) (hab : a < b)
    (he : RootEnum (D.vH j c) a b m r)
    (hc : 8 ≤ D.marksR (sideR (D.vψ j c) (D.vhang j c) a b) →
      ∀ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i) ≤ 7)
    (htop : 8 ≤ D.marksR (sideR (D.vψ j c) (D.vhang j c) a b) →
      ∃ X, X₀ = some X ∧ sideR (D.vψ j c) (D.vhang j c) a b ⊆ X ∧
        D.marksR (sideR (D.vψ j c) (D.vhang j c) a b) ≤ T ∧ T ≤ 15) :
    rule15 (D.tag15 X₀ T (sideR (D.vψ j c) (D.vhang j c) a b)) m
      fun i => D.tag15 X₀ T (childR (D.vψ j c) (D.vhang j c) r i) := by
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
  rcases Nat.lt_or_ge (D.marksR (sideR (D.vψ j c) (D.vhang j c) a b)) 8 with h6 | h7
  · left
    refine ⟨_, fun i => D.marksR (childR (D.vψ j c) (D.vhang j c) r i), tag15_small (by omega),
      fun i => tag15_small ?_, he.one_le, by beta_reduce; omega, by omega⟩
    have := hfle i
    split_ifs at hsum <;> omega
  · right; left
    obtain ⟨X, rfl, hsub, hT, hT15⟩ := htop h7
    refine ⟨_, fun i => D.marksR (childR (D.vψ j c) (D.vhang j c) r i), tag15_top h7 hsub,
      fun i => tag15_small (hc h7 i), he.one_le, by omega, hc h7, fun hev => ?_⟩
    simp only [hev, ↓reduceIte] at hsum
    beta_reduce
    omega

/-! ### The vertex rule for every split -/

theorem splitOK_none15 (T : ℕ) : SplitOK (R := sys15) D vrule15 (D.tag15 none T) := by
  intro j z₀ X hx hX
  have hu := marksR_union (sep_brR hx hX)
  rcases Nat.lt_or_ge (D.marksR (X ∪ D.brR j z₀)) 8 with h6 | h7
  · left
    exact ⟨_, _, _, tag15_small (by omega), tag15_small (by omega), tag15_small (by omega),
      by omega, by omega⟩
  · right; left
    exact tag15_triv_none h7

/-- **The vertex rule for every split, the centroid half `X₀` given.** -/
theorem splitOK_some15 {v₀ : V} {X₀ : Finset V} {T : ℕ} (hX₀ : X₀ ⊆ compR G v₀)
    (hT : D.marksR (compR G v₀) = T) (hT15 : T ≤ 15)
    (hmin : ∀ j (c z : Fin (D.n j)), (D.H j).Adj c z → G.Reachable v₀ (D.ψ j c) →
      8 ≤ D.marksR (D.halfR j c z) → X₀.card ≤ (D.halfR j c z).card) :
    SplitOK (R := sys15) D vrule15 (D.tag15 (some X₀) T) := by
  intro j z₀ X hx hX
  have hu := marksR_union (sep_brR hx hX)
  rcases Nat.lt_or_ge (D.marksR (X ∪ D.brR j z₀)) 8 with h6 | h7
  · left
    exact ⟨_, _, _, tag15_small (by omega), tag15_small (by omega), tag15_small (by omega),
      by omega, by omega⟩
  by_cases hsub : X ∪ D.brR j z₀ ⊆ X₀
  swap
  · right; left
    exact tag15_triv_some h7 hsub
  have hle : D.marksR (X ∪ D.brR j z₀) ≤ T := hT ▸ marksR_mono (hsub.trans hX₀)
  rw [tag15_top h7 hsub]
  rcases Nat.lt_or_ge (D.marksR X) 8 with hx6 | hx7
  · rcases Nat.lt_or_ge (D.marksR (D.brR j z₀)) 8 with hb6 | hb7
    · right; right; right; left
      exact ⟨_, _, _, rfl, tag15_small (by omega), tag15_small (by omega)⟩
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
      have hXB : X ∪ D.brR j z₀ = D.brR j z₀ :=
        union_eq_right.mpr (subset_union_left.trans (hsub.trans hEq.symm.le))
      have hx0 : D.marksR X = 0 := by rw [hXB] at hu; omega
      right; right; right; right
      refine ⟨_, rfl, by rw [tag15_small (by omega), hx0], ?_, by omega⟩
      rw [tag15_top hb7 hBX₀, hXB]
  · right; right; left
    have hb6 : D.marksR (D.brR j z₀) ≤ 7 := by omega
    exact ⟨_, _, _, rfl, tag15_top hx7 (subset_union_left.trans hsub), tag15_small hb6,
      by omega, by omega⟩

/-! ### The face rule in the halves -/

theorem ruleOn_light15 (X₀ : Option (Finset V)) (T : ℕ) {U : Finset V} (hU : D.marksR U ≤ 7) :
    RuleOn (R := sys15) D rule15 (D.tag15 X₀ T) U :=
  fun j c a b m r hadj hab he hsub => rule15_view X₀ T j c a b m r hadj hab he
    (fun h => absurd ((marksR_mono (subset_union_left.trans hsub)).trans hU) (by omega))
    (fun h => absurd ((marksR_mono (subset_union_left.trans hsub)).trans hU) (by omega))

variable (D) in
/-- **The base edge of a component, with its tags.** -/
theorem exists_base15 (v₀ : V) (i₀ : ι) (y₀ : Fin (D.n i₀)) (h₀ : G.Reachable v₀ (D.ψ i₀ y₀))
    (h15 : D.marksR (compR G v₀) ≤ 15) :
    ∃ (tagR : Finset V → T15) (i : ι) (p q : Fin (D.n i)), (D.H i).Adj p q ∧
      G.Reachable v₀ (D.ψ i p) ∧ SplitOK (R := sys15) D vrule15 tagR ∧
      glue15 (tagR (D.halfR i p q)) (tagR (D.halfR i q p)) ∧
      RuleOn (R := sys15) D rule15 tagR (D.halfR i p q) ∧
      RuleOn (R := sys15) D rule15 tagR (D.halfR i q p) := by
  classical
  set T := D.marksR (compR G v₀) with hT
  have hM : ∀ i (p q : Fin (D.n i)), (D.H i).Adj p q → G.Reachable v₀ (D.ψ i p) →
      D.marksR (D.halfR i p q) + D.marksR (D.halfR i q p) = T := by
    intro i p q hpq hr
    rw [marks_halves hpq, compR_eq hr]
  by_cases hA : ∃ i p q, (D.H i).Adj p q ∧ G.Reachable v₀ (D.ψ i p) ∧
      D.marksR (D.halfR i p q) ≤ 7 ∧ D.marksR (D.halfR i q p) ≤ 7
  · obtain ⟨i, p, q, hpq, hr, h1, h2⟩ := hA
    exact ⟨D.tag15 none T, i, p, q, hpq, hr, splitOK_none15 T,
      Or.inl ⟨_, _, tag15_small h1, tag15_small h2⟩, ruleOn_light15 none T h1,
      ruleOn_light15 none T h2⟩
  push Not at hA
  have hn := D.two_le i₀
  have h01 : (D.H i₀).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := (D.diss i₀).1 _ _ rfl
  have hr0 : G.Reachable v₀ (D.ψ i₀ ⟨0, by omega⟩) := h₀.trans (block_reachable _ _)
  have hr1 : G.Reachable v₀ (D.ψ i₀ ⟨1, by omega⟩) := h₀.trans (block_reachable _ _)
  have hex : ∃ d, ∃ i p q, (D.H i).Adj p q ∧ G.Reachable v₀ (D.ψ i p) ∧
      8 ≤ D.marksR (D.halfR i p q) ∧ (D.halfR i p q).card = d := by
    by_cases h : 8 ≤ D.marksR (D.halfR i₀ ⟨0, by omega⟩ ⟨1, by omega⟩)
    · exact ⟨_, i₀, _, _, h01, hr0, h, rfl⟩
    · exact ⟨_, i₀, _, _, h01.symm, hr1, by have := hA i₀ _ _ h01 hr0 (by omega); omega, rfl⟩
  obtain ⟨i, p, q, hpq, hr, h7, hd⟩ := Nat.find_spec hex
  have hmin : ∀ i' (p' q' : Fin (D.n i')), (D.H i').Adj p' q' → G.Reachable v₀ (D.ψ i' p') →
      8 ≤ D.marksR (D.halfR i' p' q') → (D.halfR i p q).card ≤ (D.halfR i' p' q').card :=
    fun i' p' q' h1 h2 h3 => hd ▸ Nat.find_min' hex ⟨i', p', q', h1, h2, h3, rfl⟩
  have hOK : D.halfR i p q ⊆ compR G v₀ := by
    rw [← compR_eq hr, ← halves_union hpq.ne]; exact subset_union_left
  have hT15 : T ≤ 15 := h15
  have hY : D.marksR (D.halfR i q p) ≤ 7 := by have := hM i p q hpq hr; omega
  refine ⟨D.tag15 (some (D.halfR i p q)) T, i, p, q, hpq, hr, splitOK_some15 hOK rfl hT15 hmin,
    ?_, ?_,
    ruleOn_light15 _ T hY⟩
  · right; left
    refine ⟨_, tag15_top h7 subset_rfl, ?_⟩
    rw [tag15_small hY]
    congr 1
    have := hM i p q hpq hr
    omega
  -- the centroid half: every child region lies in a smaller half
  intro j c a b m r hadj hab he hsub
  refine rule15_view (some (D.halfR i p q)) T j c a b m r hadj hab he (fun _ i' => ?_)
    fun _ => ⟨(D.halfR i p q), rfl, subset_union_left.trans hsub,
      hT ▸ marksR_mono ((subset_union_left.trans hsub).trans hOK), hT15⟩
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
  have hle6 : D.marksR Hc ≤ 7 := by
    by_contra h
    have := hmin j _ _ hadjc hrc (by rw [← hshift]; omega)
    rw [← hshift] at this
    omega
  exact (marksR_mono hchild).trans hle6

end BlockDecomp

/-! ### The theorem -/

/-- **A graph whose blocks are polygon dissections or single edges, with at most fifteen even
faces in the blocks of each connected component, is 3-ECC**: every assignment of lists of three
colours has at least as many proper colourings as there are `3`-colourings. Bridges, cut
vertices, isolated vertices and odd faces are unrestricted. The blocks of the component of `v₀`
are the blocks `i` whose vertex `ψ i 0` is reachable from `v₀`. -/
theorem ecc_three_of_blocks_fifteen (D : BlockDecomp G ι)
    (h15 : ∀ v₀ : V, ∑ i ∈ univ.filter (fun i => G.Reachable v₀ (D.ψ i 0)),
      numEvenFaces (D.H i) ≤ 15) :
    G.ECCAt 3 := by
  classical
  have key : ∀ (n : ℕ) (s : Finset V), s.card ≤ n → (∀ v ∈ s, ∀ w, G.Reachable v w → w ∈ s) →
      ∃ tg, TagBuiltW G sys15 rule15 glue15 vrule15 s tg := by
    intro n
    induction n with
    | zero =>
      intro s hs _
      have : s = ∅ := card_eq_zero.mp (by omega)
      subst this
      exact ⟨_, TagBuiltW.empty (fun _ _ => T15.small 0)⟩
    | succ n ih =>
      intro s hs hcl
      rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
      · exact ⟨_, TagBuiltW.empty (fun _ _ => T15.small 0)⟩
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
        obtain ⟨tagR, i, p, q, hpq, hr, hsplit, hg, h1, h2⟩ := D.exists_base15 v₀ i₀ y₀ h₀
          (by rw [D.marksR_comp]; exact h15 v₀)
        obtain ⟨tg, h⟩ := buildComp (D := D) (R := sys15) (rule := rule15) (glue := glue15)
          (vrule := vrule15) (tagR := tagR) hsplit i p q hpq hg h1 h2 (s \ K) tg' hT'
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
  exact ecc_three_of_fifteenBuiltW G h

/-- **A connected graph whose blocks are polygon dissections or single edges, with at most
fifteen even faces in all its blocks, is 3-ECC.** -/
theorem ecc_three_of_blocks_fifteen_connected (D : BlockDecomp G ι) (hc : G.Connected)
    (h15 : ∑ i, numEvenFaces (D.H i) ≤ 15) : G.ECCAt 3 :=
  ecc_three_of_blocks_fifteen D fun v₀ => by
    rw [filter_true_of_mem fun i _ => hc.preconnected _ _]
    exact h15

end Outerplanar
