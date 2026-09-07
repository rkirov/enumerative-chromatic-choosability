import Grid3.Three.Seam
import Grid3.Three.Slots

/-!
# The colour maps of a seam

For a concrete seam `(Lc, Lc')` and a valid maximal key `M` above its actual matching, the
canonical colour list `cs := Cert.colours (packType Lc) (packType Lc') M` is a list of slots.
`exists_colourMaps` produces maps `φL`, `φR` from actual colours to slot indices and inverses
`ψL`, `ψR` on the active slots, such that

* `φL` preserves the left pattern and `φR` the right pattern,
* common colours with intersecting patterns (`commonI`) go to the same slot under `φL` and `φR`,
* `ψL ∘ φL = id` on the left colours, and `φL ∘ ψL = id` on the left-active slots (similarly on
  the right).

The construction glues three families of class bijections (`Glue.exists_glued`): the common
kinds `(p, q)` onto a reserved subset `T (p, q)` of the matched slots of that kind; the left-only
colours of each pattern onto the remaining left-active slots of that pattern (the surplus matched
slots of the maximal key and the left-only slots); and symmetrically on the right.
-/

open Finset

namespace Grid3.Three.Seam

open Cert Col Glue Slots

variable (Lc Lc' : Fin 3 → Finset ℕ) (M : ℕ)

/-- the canonical colour list of the seam with matching `M` -/
def cols : List (ℕ × ℕ) := Cert.colours (packType Lc) (packType Lc') M

/-- the colour maps of a seam (see the module docstring) -/
structure ColourMaps where
  φL : ℕ → ℕ
  φR : ℕ → ℕ
  ψL : ℕ → ℕ
  ψR : ℕ → ℕ
  φL_lt : ∀ c ∈ colours Lc, φL c < (cols Lc Lc' M).length
  φL_pat : ∀ c ∈ colours Lc, ((cols Lc Lc' M).getD (φL c) (0, 0)).1 = patOf Lc c
  φR_lt : ∀ c ∈ colours Lc', φR c < (cols Lc Lc' M).length
  φR_pat : ∀ c ∈ colours Lc', ((cols Lc Lc' M).getD (φR c) (0, 0)).2 = patOf Lc' c
  common : ∀ c ∈ commonI Lc Lc', φL c = φR c
  ψL_φL : ∀ c ∈ colours Lc, ψL (φL c) = c
  ψR_φR : ∀ c ∈ colours Lc', ψR (φR c) = c
  φL_ψL : ∀ i, i < (cols Lc Lc' M).length → ((cols Lc Lc' M).getD i (0, 0)).1 ≠ 0 →
    ψL i ∈ colours Lc ∧ φL (ψL i) = i
  φR_ψR : ∀ i, i < (cols Lc Lc' M).length → ((cols Lc Lc' M).getD i (0, 0)).2 ≠ 0 →
    ψR i ∈ colours Lc' ∧ φR (ψR i) = i

/-! ### Counting the active slots of one pattern -/

/-- the left-active slots of pattern `a + 1` -/
def leftActive (a : ℕ) : Finset (Fin (cols Lc Lc' M).length) :=
  Finset.univ.filter fun i => ((cols Lc Lc' M)[i]).1 = a + 1

/-- the right-active slots of pattern `b + 1` -/
def rightActive (b : ℕ) : Finset (Fin (cols Lc Lc' M).length) :=
  Finset.univ.filter fun i => ((cols Lc Lc' M)[i]).2 = b + 1

theorem slot_subset_leftActive (a b : ℕ) :
    slot (cols Lc Lc' M) (a + 1, b) ⊆ leftActive Lc Lc' M a := by
  intro i hi
  rw [mem_slot] at hi
  unfold leftActive
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [hi]⟩

theorem slot_subset_rightActive (a b : ℕ) :
    slot (cols Lc Lc' M) (a, b + 1) ⊆ rightActive Lc Lc' M b := by
  intro i hi
  rw [mem_slot] at hi
  unfold rightActive
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [hi]⟩

theorem slot_disjoint (x y : ℕ × ℕ) (hxy : x ≠ y) :
    Disjoint (slot (cols Lc Lc' M) x) (slot (cols Lc Lc' M) y) := by
  rw [Finset.disjoint_left]
  intro i hx hy
  rw [mem_slot] at hx hy
  exact hxy (hx.symm.trans hy)

/-- the left-active slots of a pattern are its matched slots and its left-only slots -/
theorem leftActive_eq (a : ℕ) :
    leftActive Lc Lc' M a
      = (Finset.univ.biUnion fun q : Fin 7 => slot (cols Lc Lc' M) (a + 1, q.val + 1))
        ∪ slot (cols Lc Lc' M) (a + 1, 0) := by
  ext i
  unfold leftActive
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_biUnion,
    mem_slot]
  constructor
  · intro h
    have hmem : (cols Lc Lc' M)[i] ∈ cols Lc Lc' M := List.getElem_mem _
    rcases mem_colours_kinds _ _ _ _ hmem with ⟨p, hp, q, hq, hx⟩ | ⟨p, hp, hx⟩ | ⟨q, hq, hx⟩
    · left
      refine ⟨⟨q, hq⟩, ?_⟩
      rw [hx] at h ⊢
      simp only at h
      rw [h]
    · right
      rw [hx] at h ⊢
      simp only at h
      rw [h]
    · rw [hx] at h; simp at h
  · rintro (⟨q, hq⟩ | hq)
    · rw [hq]
    · rw [hq]

theorem rightActive_eq (b : ℕ) :
    rightActive Lc Lc' M b
      = (Finset.univ.biUnion fun p : Fin 7 => slot (cols Lc Lc' M) (p.val + 1, b + 1))
        ∪ slot (cols Lc Lc' M) (0, b + 1) := by
  ext i
  unfold rightActive
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_biUnion,
    mem_slot]
  constructor
  · intro h
    have hmem : (cols Lc Lc' M)[i] ∈ cols Lc Lc' M := List.getElem_mem _
    rcases mem_colours_kinds _ _ _ _ hmem with ⟨p, hp, q, hq, hx⟩ | ⟨p, hp, hx⟩ | ⟨q, hq, hx⟩
    · left
      refine ⟨⟨p, hp⟩, ?_⟩
      rw [hx] at h ⊢
      simp only at h
      rw [h]
    · rw [hx] at h; simp at h
    · right
      rw [hx] at h ⊢
      simp only at h
      rw [h]
  · rintro (⟨p, hp⟩ | hp)
    · rw [hp]
    · rw [hp]

theorem sum_mcount_row (M a : ℕ) : ∑ q : Fin 7, mcount M a q.val = sumRow M a := by
  rw [sumRow_eq, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.univ_eq_empty,
    Finset.sum_empty]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, Nat.reduceAdd]
  omega

theorem sum_mcount_col (M b : ℕ) : ∑ p : Fin 7, mcount M p.val b = sumCol M b := by
  rw [sumCol_eq, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.univ_eq_empty,
    Finset.sum_empty]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, Nat.reduceAdd]
  omega

theorem leftActive_card (hv : validKey (packType Lc) (packType Lc') M = true) (a : ℕ)
    (ha : a < 7) : (leftActive Lc Lc' M a).card = mult (packType Lc) a := by
  rw [leftActive_eq, Finset.card_union_of_disjoint, Finset.card_biUnion]
  · simp only [card_slot]
    unfold cols
    rw [count_left _ _ _ a ha]
    have : ∑ q : Fin 7, (Cert.colours (packType Lc) (packType Lc') M).count (a + 1, q.val + 1)
        = sumRow M a := by
      rw [← sum_mcount_row]
      apply Finset.sum_congr rfl
      intro q _
      exact count_pair _ _ _ a q.val ha q.isLt
    rw [this]
    have := validKey_row hv a ha
    omega
  · intro q _ q' _ hqq'
    apply slot_disjoint
    intro h; apply hqq'; ext; simpa using (Prod.mk.inj h).2
  · rw [Finset.disjoint_left]
    intro i hi hi0
    rw [Finset.mem_biUnion] at hi
    obtain ⟨q, _, hq⟩ := hi
    rw [mem_slot] at hq hi0
    rw [hq] at hi0
    simp at hi0

theorem rightActive_card (hv : validKey (packType Lc) (packType Lc') M = true) (b : ℕ)
    (hb : b < 7) : (rightActive Lc Lc' M b).card = mult (packType Lc') b := by
  rw [rightActive_eq, Finset.card_union_of_disjoint, Finset.card_biUnion]
  · simp only [card_slot]
    unfold cols
    rw [count_right _ _ _ b hb]
    have : ∑ p : Fin 7, (Cert.colours (packType Lc) (packType Lc') M).count (p.val + 1, b + 1)
        = sumCol M b := by
      rw [← sum_mcount_col]
      apply Finset.sum_congr rfl
      intro p _
      exact count_pair _ _ _ p.val b p.isLt hb
    rw [this]
    have := validKey_col hv b hb
    omega
  · intro p _ p' _ hpp'
    apply slot_disjoint
    intro h; apply hpp'; ext; simpa using (Prod.mk.inj h).1
  · rw [Finset.disjoint_left]
    intro i hi hi0
    rw [Finset.mem_biUnion] at hi
    obtain ⟨p, _, hp⟩ := hi
    rw [mem_slot] at hp hi0
    rw [hp] at hi0
    simp at hi0

/-! ### The classes of actual colours -/

/-- the common colours of kind `(p, q)` -/
def Acom (k : Fin 7 × Fin 7) : Finset ℕ :=
  (commonI Lc Lc').filter fun c => patOf Lc c = k.1.val + 1 ∧ patOf Lc' c = k.2.val + 1

/-- the left-only colours of pattern `a + 1` -/
def ALO (a : Fin 7) : Finset ℕ :=
  ((colours Lc) \ commonI Lc Lc').filter fun c => patOf Lc c = a.val + 1

/-- the right-only colours of pattern `b + 1` -/
def ARO (b : Fin 7) : Finset ℕ :=
  ((colours Lc') \ commonI Lc Lc').filter fun c => patOf Lc' c = b.val + 1

theorem Acom_card (k : Fin 7 × Fin 7) : (Acom Lc Lc' k).card = mact Lc Lc' k.1.val k.2.val := rfl

theorem ALO_card (a : Fin 7) : (ALO Lc Lc' a).card
    = cnt Lc a.val - ((commonI Lc Lc').filter fun c => patOf Lc c = a.val + 1).card := by
  have : ALO Lc Lc' a = ((colours Lc).filter fun c => patOf Lc c = a.val + 1)
      \ ((commonI Lc Lc').filter fun c => patOf Lc c = a.val + 1) := by
    ext c
    unfold ALO
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hsub : ((commonI Lc Lc').filter fun c => patOf Lc c = a.val + 1)
      ⊆ ((colours Lc).filter fun c => patOf Lc c = a.val + 1) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨commonI_subset_left Lc Lc' hc.1, hc.2⟩
  rw [this, Finset.card_sdiff, Finset.inter_eq_left.2 hsub]
  rfl

theorem ARO_card (b : Fin 7) : (ARO Lc Lc' b).card
    = cnt Lc' b.val - ((commonI Lc Lc').filter fun c => patOf Lc' c = b.val + 1).card := by
  have : ARO Lc Lc' b = ((colours Lc').filter fun c => patOf Lc' c = b.val + 1)
      \ ((commonI Lc Lc').filter fun c => patOf Lc' c = b.val + 1) := by
    ext c
    unfold ARO
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hsub : ((commonI Lc Lc').filter fun c => patOf Lc' c = b.val + 1)
      ⊆ ((colours Lc').filter fun c => patOf Lc' c = b.val + 1) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨commonI_subset_right Lc Lc' hc.1, hc.2⟩
  rw [this, Finset.card_sdiff, Finset.inter_eq_left.2 hsub]
  rfl

/-- a pattern index from a pattern value -/
def pidx (x : ℕ) : Fin 7 := ⟨(x - 1) % 7, Nat.mod_lt _ (by decide)⟩

theorem pidx_succ (a : Fin 7) : pidx (a.val + 1) = a := by
  unfold pidx; ext; simp [Nat.mod_eq_of_lt a.isLt]

/-! ### The construction -/

theorem exists_colourMaps (h3 : ∀ r, (Lc r).card = 3) (h3' : ∀ r, (Lc' r).card = 3)
    (hv : validKey (packType Lc) (packType Lc') M = true) (hle : keyLE (Mact Lc Lc') M) :
    Nonempty (ColourMaps Lc Lc' M) := by
  classical
  set cs := cols Lc Lc' M with hcs
  -- the reserved matched slots of each common kind
  have hT : ∀ k : Fin 7 × Fin 7, ∃ t ⊆ slot cs (k.1.val + 1, k.2.val + 1),
      t.card = mact Lc Lc' k.1.val k.2.val := by
    intro k
    apply Finset.exists_subset_card_eq
    rw [card_slot]
    unfold cs cols
    rw [count_pair _ _ _ _ _ k.1.isLt k.2.isLt, ← mcount_Mact Lc Lc' h3 _ _ k.1.isLt k.2.isLt]
    exact hle k.1.val k.1.isLt k.2.val k.2.isLt
  choose T hTsub hTcard using hT
  -- slots are nonempty: some left pattern has a colour
  have hne : Nonempty (Fin cs.length) := by
    obtain ⟨c, hc⟩ : (Lc 0).Nonempty := Finset.card_pos.1 (by rw [h3 0]; decide)
    have hcc : c ∈ colours Lc := (mem_colours Lc c).2 ⟨0, hc⟩
    have hpos := patOf_pos Lc c hcc
    have hle7 := patOf_le Lc c
    have hcnt : 0 < cnt Lc (patOf Lc c - 1) := by
      apply Finset.card_pos.2
      exact ⟨c, Finset.mem_filter.2 ⟨hcc, by omega⟩⟩
    rw [← mult_packType Lc h3 _ (by omega), ← leftActive_card Lc Lc' M hv _ (by omega),
      Finset.card_pos] at hcnt
    obtain ⟨i, _⟩ := hcnt
    exact ⟨i⟩
  have : Inhabited (Fin cs.length) := ⟨Classical.choice hne⟩
  -- the left-only and right-only slot classes
  let TU : Finset (Fin cs.length) := Finset.univ.biUnion fun k => T k
  let BLO : Fin 7 → Finset (Fin cs.length) := fun a =>
    leftActive Lc Lc' M a.val \ (Finset.univ.biUnion fun q : Fin 7 => T (a, q))
  let BRO : Fin 7 → Finset (Fin cs.length) := fun b =>
    rightActive Lc Lc' M b.val \ (Finset.univ.biUnion fun p : Fin 7 => T (p, b))
  have hT_pat : ∀ k i, i ∈ T k → cs[i] = (k.1.val + 1, k.2.val + 1) := fun k i hi =>
    (mem_slot _ _ _).1 (hTsub k hi)
  have hT_disj : ∀ k k', k ≠ k' → Disjoint (T k) (T k') := by
    intro k k' hkk'
    rw [Finset.disjoint_left]
    intro i hi hi'
    have h1 := hT_pat k i hi
    have h2 := hT_pat k' i hi'
    rw [h1] at h2
    apply hkk'
    have h12 := Prod.mk.inj h2
    have e1 := h12.1; have e2 := h12.2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  -- cardinalities of the left-only classes
  have hBLO_card : ∀ a : Fin 7, (BLO a).card = (ALO Lc Lc' a).card := by
    intro a
    have hsub : (Finset.univ.biUnion fun q : Fin 7 => T (a, q)) ⊆ leftActive Lc Lc' M a.val := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨q, _, hq⟩ := hi
      exact slot_subset_leftActive Lc Lc' M _ _ (hTsub (a, q) hq)
    have hcardU : (Finset.univ.biUnion fun q : Fin 7 => T (a, q)).card
        = ((commonI Lc Lc').filter fun c => patOf Lc c = a.val + 1).card := by
      rw [Finset.card_biUnion]
      · rw [← sumRow_Mact Lc Lc' h3 a.val a.isLt, ← sum_mcount_row]
        apply Finset.sum_congr rfl
        intro q _
        rw [hTcard, mcount_Mact Lc Lc' h3 _ _ a.isLt q.isLt]
      · intro q _ q' _ hqq'
        exact hT_disj _ _ (by intro h; exact hqq' (Prod.mk.inj h).2)
    show (leftActive Lc Lc' M a.val \ _).card = _
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, hcardU, leftActive_card Lc Lc' M hv a.val a.isLt,
      mult_packType Lc h3 a.val a.isLt, ALO_card]
  have hBRO_card : ∀ b : Fin 7, (BRO b).card = (ARO Lc Lc' b).card := by
    intro b
    have hsub : (Finset.univ.biUnion fun p : Fin 7 => T (p, b)) ⊆ rightActive Lc Lc' M b.val := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨p, _, hp⟩ := hi
      exact slot_subset_rightActive Lc Lc' M _ _ (hTsub (p, b) hp)
    have hcardU : (Finset.univ.biUnion fun p : Fin 7 => T (p, b)).card
        = ((commonI Lc Lc').filter fun c => patOf Lc' c = b.val + 1).card := by
      rw [Finset.card_biUnion]
      · rw [← sumCol_Mact Lc Lc' h3 b.val b.isLt, ← sum_mcount_col]
        apply Finset.sum_congr rfl
        intro p _
        rw [hTcard, mcount_Mact Lc Lc' h3 _ _ p.isLt b.isLt]
      · intro p _ p' _ hpp'
        exact hT_disj _ _ (by intro h; exact hpp' (Prod.mk.inj h).1)
    show (rightActive Lc Lc' M b.val \ _).card = _
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, hcardU, rightActive_card Lc Lc' M hv b.val b.isLt,
      mult_packType Lc' h3' b.val b.isLt, ARO_card]
  -- the three glued maps
  obtain ⟨Gc⟩ := exists_glued (Acom Lc Lc') T
    (fun c => (pidx (patOf Lc c), pidx (patOf Lc' c)))
    (fun i => (pidx (cs[i]).1, pidx (cs[i]).2))
    (by
      intro k c hc
      unfold Acom at hc
      rw [Finset.mem_filter] at hc
      rw [hc.2.1, hc.2.2, pidx_succ, pidx_succ])
    (by
      intro k i hi
      rw [hT_pat k i hi]
      show (pidx (k.1.val + 1), pidx (k.2.val + 1)) = k
      rw [pidx_succ, pidx_succ])
    (fun k => by rw [Acom_card, hTcard])
  obtain ⟨Gl⟩ := exists_glued (ALO Lc Lc') BLO
    (fun c => pidx (patOf Lc c))
    (fun i => pidx (cs[i]).1)
    (by
      intro a c hc
      unfold ALO at hc
      rw [Finset.mem_filter] at hc
      rw [hc.2, pidx_succ])
    (by
      intro a i hi
      have hi' : i ∈ leftActive Lc Lc' M a.val := (Finset.mem_sdiff.1 hi).1
      unfold leftActive at hi'
      rw [Finset.mem_filter] at hi'
      rw [hi'.2, pidx_succ])
    (fun a => (hBLO_card a).symm)
  obtain ⟨Gr⟩ := exists_glued (ARO Lc Lc') BRO
    (fun c => pidx (patOf Lc' c))
    (fun i => pidx (cs[i]).2)
    (by
      intro b c hc
      unfold ARO at hc
      rw [Finset.mem_filter] at hc
      rw [hc.2, pidx_succ])
    (by
      intro b i hi
      have hi' : i ∈ rightActive Lc Lc' M b.val := (Finset.mem_sdiff.1 hi).1
      unfold rightActive at hi'
      rw [Finset.mem_filter] at hi'
      rw [hi'.2, pidx_succ])
    (fun b => (hBRO_card b).symm)
  -- the class of a colour
  have hmemAcom : ∀ c ∈ commonI Lc Lc', c ∈ Acom Lc Lc' (pidx (patOf Lc c), pidx (patOf Lc' c)) := by
    intro c hc
    have hL := patOf_pos Lc c (commonI_subset_left Lc Lc' hc)
    have hL7 := patOf_le Lc c
    have hR := patOf_pos Lc' c (commonI_subset_right Lc Lc' hc)
    have hR7 := patOf_le Lc' c
    unfold Acom
    rw [Finset.mem_filter]
    refine ⟨hc, ?_, ?_⟩
    · show patOf Lc c = (patOf Lc c - 1) % 7 + 1
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · show patOf Lc' c = (patOf Lc' c - 1) % 7 + 1
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hmemALO : ∀ c ∈ colours Lc, c ∉ commonI Lc Lc' → c ∈ ALO Lc Lc' (pidx (patOf Lc c)) := by
    intro c hc hnc
    have hL := patOf_pos Lc c hc
    have hL7 := patOf_le Lc c
    unfold ALO
    rw [Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨hc, hnc⟩, ?_⟩
    show patOf Lc c = (patOf Lc c - 1) % 7 + 1
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hmemARO : ∀ c ∈ colours Lc', c ∉ commonI Lc Lc' → c ∈ ARO Lc Lc' (pidx (patOf Lc' c)) := by
    intro c hc hnc
    have hR := patOf_pos Lc' c hc
    have hR7 := patOf_le Lc' c
    unfold ARO
    rw [Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨hc, hnc⟩, ?_⟩
    show patOf Lc' c = (patOf Lc' c - 1) % 7 + 1
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  -- the maps
  let φL : ℕ → ℕ := fun c => if c ∈ commonI Lc Lc' then (Gc.toFun c).val else (Gl.toFun c).val
  let φR : ℕ → ℕ := fun c => if c ∈ commonI Lc Lc' then (Gc.toFun c).val else (Gr.toFun c).val
  let ψL : ℕ → ℕ := fun i => if h : i < cs.length then
    (if (⟨i, h⟩ : Fin cs.length) ∈ TU then Gc.invFun ⟨i, h⟩ else Gl.invFun ⟨i, h⟩) else 0
  let ψR : ℕ → ℕ := fun i => if h : i < cs.length then
    (if (⟨i, h⟩ : Fin cs.length) ∈ TU then Gc.invFun ⟨i, h⟩ else Gr.invFun ⟨i, h⟩) else 0
  -- slot facts of the images
  have hGc_slot : ∀ c ∈ commonI Lc Lc',
      cs[Gc.toFun c] = (patOf Lc c, patOf Lc' c) ∧ Gc.toFun c ∈ TU := by
    intro c hc
    have hmem := Gc.mem _ c (hmemAcom c hc)
    have hL := patOf_pos Lc c (commonI_subset_left Lc Lc' hc)
    have hL7 := patOf_le Lc c
    have hR := patOf_pos Lc' c (commonI_subset_right Lc Lc' hc)
    have hR7 := patOf_le Lc' c
    refine ⟨?_, Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hmem⟩⟩
    rw [hT_pat _ _ hmem]
    show ((patOf Lc c - 1) % 7 + 1, (patOf Lc' c - 1) % 7 + 1) = _
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    congr 1 <;> omega
  have hGl_slot : ∀ c ∈ colours Lc, c ∉ commonI Lc Lc' →
      (cs[Gl.toFun c]).1 = patOf Lc c ∧ Gl.toFun c ∉ TU := by
    intro c hc hnc
    have hmem := Gl.mem _ c (hmemALO c hc hnc)
    have hL := patOf_pos Lc c hc
    have hL7 := patOf_le Lc c
    rw [Finset.mem_sdiff] at hmem
    have hact := hmem.1
    unfold leftActive at hact
    rw [Finset.mem_filter] at hact
    refine ⟨?_, ?_⟩
    · rw [hact.2]
      show (patOf Lc c - 1) % 7 + 1 = _
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro hTU
      apply hmem.2
      rw [Finset.mem_biUnion] at hTU ⊢
      obtain ⟨k, _, hk⟩ := hTU
      have hpat := hT_pat k _ hk
      rw [hpat] at hact
      have hk1 : k.1 = pidx (patOf Lc c) := by
        have h2 := hact.2
        simp only at h2
        apply Fin.ext
        omega
      refine ⟨k.2, Finset.mem_univ _, ?_⟩
      rw [← hk1]; exact hk
  have hGr_slot : ∀ c ∈ colours Lc', c ∉ commonI Lc Lc' →
      (cs[Gr.toFun c]).2 = patOf Lc' c ∧ Gr.toFun c ∉ TU := by
    intro c hc hnc
    have hmem := Gr.mem _ c (hmemARO c hc hnc)
    have hR := patOf_pos Lc' c hc
    have hR7 := patOf_le Lc' c
    rw [Finset.mem_sdiff] at hmem
    have hact := hmem.1
    unfold rightActive at hact
    rw [Finset.mem_filter] at hact
    refine ⟨?_, ?_⟩
    · rw [hact.2]
      show (patOf Lc' c - 1) % 7 + 1 = _
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro hTU
      apply hmem.2
      rw [Finset.mem_biUnion] at hTU ⊢
      obtain ⟨k, _, hk⟩ := hTU
      have hpat := hT_pat k _ hk
      rw [hpat] at hact
      have hk2 : k.2 = pidx (patOf Lc' c) := by
        have h2 := hact.2
        simp only at h2
        apply Fin.ext
        omega
      refine ⟨k.1, Finset.mem_univ _, ?_⟩
      rw [← hk2]; exact hk
  -- getD of a `Fin` index
  have hgetD : ∀ i : Fin cs.length, cs.getD i.val (0, 0) = cs[i] := fun i => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]; rfl
  refine ⟨⟨φL, φR, ψL, ψR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- φL_lt
    intro c hc
    show (if c ∈ commonI Lc Lc' then (Gc.toFun c).val else (Gl.toFun c).val) < cs.length
    split_ifs <;> exact Fin.isLt _
  · -- φL_pat
    intro c hc
    show (cs.getD (if c ∈ commonI Lc Lc' then (Gc.toFun c).val else (Gl.toFun c).val) (0, 0)).1
      = patOf Lc c
    by_cases hcc : c ∈ commonI Lc Lc'
    · rw [if_pos hcc, hgetD, (hGc_slot c hcc).1]
    · rw [if_neg hcc, hgetD, (hGl_slot c hc hcc).1]
  · -- φR_lt
    intro c hc
    show (if c ∈ commonI Lc Lc' then (Gc.toFun c).val else (Gr.toFun c).val) < cs.length
    split_ifs <;> exact Fin.isLt _
  · -- φR_pat
    intro c hc
    show (cs.getD (if c ∈ commonI Lc Lc' then (Gc.toFun c).val else (Gr.toFun c).val) (0, 0)).2
      = patOf Lc' c
    by_cases hcc : c ∈ commonI Lc Lc'
    · rw [if_pos hcc, hgetD, (hGc_slot c hcc).1]
    · rw [if_neg hcc, hgetD, (hGr_slot c hc hcc).1]
  · -- common
    intro c hc
    show (if c ∈ commonI Lc Lc' then (Gc.toFun c).val else (Gl.toFun c).val)
      = (if c ∈ commonI Lc Lc' then (Gc.toFun c).val else (Gr.toFun c).val)
    rw [if_pos hc, if_pos hc]
  · -- ψL_φL
    intro c hc
    by_cases hcc : c ∈ commonI Lc Lc'
    · have hlt := (Gc.toFun c).isLt
      simp only [ψL, φL, if_pos hcc, dif_pos hlt, Fin.eta]
      rw [if_pos (hGc_slot c hcc).2]
      exact Gc.left_inv _ c (hmemAcom c hcc)
    · have hlt := (Gl.toFun c).isLt
      simp only [ψL, φL, if_neg hcc, dif_pos hlt, Fin.eta]
      rw [if_neg (hGl_slot c hc hcc).2]
      exact Gl.left_inv _ c (hmemALO c hc hcc)
  · -- ψR_φR
    intro c hc
    by_cases hcc : c ∈ commonI Lc Lc'
    · have hlt := (Gc.toFun c).isLt
      simp only [ψR, φR, if_pos hcc, dif_pos hlt, Fin.eta]
      rw [if_pos (hGc_slot c hcc).2]
      exact Gc.left_inv _ c (hmemAcom c hcc)
    · have hlt := (Gr.toFun c).isLt
      simp only [ψR, φR, if_neg hcc, dif_pos hlt, Fin.eta]
      rw [if_neg (hGr_slot c hc hcc).2]
      exact Gr.left_inv _ c (hmemARO c hc hcc)
  · -- φL_ψL
    intro i hi hact
    rw [hgetD ⟨i, hi⟩] at hact
    have hi' : i < cs.length := hi
    simp only [ψL, φL, dif_pos hi']
    by_cases hTU : (⟨i, hi⟩ : Fin cs.length) ∈ TU
    · rw [if_pos hTU]
      rw [Finset.mem_biUnion] at hTU
      obtain ⟨k, _, hk⟩ := hTU
      have hinv := Gc.inv_mem k _ hk
      have hcom : Gc.invFun ⟨i, hi⟩ ∈ commonI Lc Lc' :=
        (Finset.mem_filter.1 hinv).1
      refine ⟨commonI_subset_left Lc Lc' hcom, ?_⟩
      rw [if_pos hcom, Gc.right_inv k _ hk]
    · rw [if_neg hTU]
      have hB : (⟨i, hi⟩ : Fin cs.length) ∈ BLO (pidx (cs[(⟨i, hi⟩ : Fin cs.length)]).1) := by
        rw [Finset.mem_sdiff]
        refine ⟨?_, ?_⟩
        · unfold leftActive
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hmem : cs[(⟨i, hi⟩ : Fin cs.length)] ∈ cs := List.getElem_mem _
          rcases mem_colours_kinds _ _ _ _ hmem with ⟨p, hp, q, hq, hx⟩ | ⟨p, hp, hx⟩ | ⟨q, hq, hx⟩
          · rw [hx]; simp only; unfold pidx; simp [Nat.mod_eq_of_lt hp]
          · rw [hx]; simp only; unfold pidx; simp [Nat.mod_eq_of_lt hp]
          · rw [hx] at hact; simp at hact
        · intro h
          apply hTU
          rw [Finset.mem_biUnion] at h ⊢
          obtain ⟨q, _, hq⟩ := h
          exact ⟨_, Finset.mem_univ _, hq⟩
      have hinv := Gl.inv_mem _ _ hB
      unfold ALO at hinv
      rw [Finset.mem_filter, Finset.mem_sdiff] at hinv
      refine ⟨hinv.1.1, ?_⟩
      rw [if_neg hinv.1.2, Gl.right_inv _ _ hB]
  · -- φR_ψR
    intro i hi hact
    rw [hgetD ⟨i, hi⟩] at hact
    have hi' : i < cs.length := hi
    simp only [ψR, φR, dif_pos hi']
    by_cases hTU : (⟨i, hi⟩ : Fin cs.length) ∈ TU
    · rw [if_pos hTU]
      rw [Finset.mem_biUnion] at hTU
      obtain ⟨k, _, hk⟩ := hTU
      have hinv := Gc.inv_mem k _ hk
      have hcom : Gc.invFun ⟨i, hi⟩ ∈ commonI Lc Lc' :=
        (Finset.mem_filter.1 hinv).1
      refine ⟨commonI_subset_right Lc Lc' hcom, ?_⟩
      rw [if_pos hcom, Gc.right_inv k _ hk]
    · rw [if_neg hTU]
      have hB : (⟨i, hi⟩ : Fin cs.length) ∈ BRO (pidx (cs[(⟨i, hi⟩ : Fin cs.length)]).2) := by
        rw [Finset.mem_sdiff]
        refine ⟨?_, ?_⟩
        · unfold rightActive
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hmem : cs[(⟨i, hi⟩ : Fin cs.length)] ∈ cs := List.getElem_mem _
          rcases mem_colours_kinds _ _ _ _ hmem with ⟨p, hp, q, hq, hx⟩ | ⟨p, hp, hx⟩ | ⟨q, hq, hx⟩
          · rw [hx]; simp only; unfold pidx; simp [Nat.mod_eq_of_lt hq]
          · rw [hx] at hact; simp at hact
          · rw [hx]; simp only; unfold pidx; simp [Nat.mod_eq_of_lt hq]
        · intro h
          apply hTU
          rw [Finset.mem_biUnion] at h ⊢
          obtain ⟨p, _, hp⟩ := h
          exact ⟨_, Finset.mem_univ _, hp⟩
      have hinv := Gr.inv_mem _ _ hB
      unfold ARO at hinv
      rw [Finset.mem_filter, Finset.mem_sdiff] at hinv
      refine ⟨hinv.1.1, ?_⟩
      rw [if_neg hinv.1.2, Gr.right_inv _ _ hB]

end Grid3.Three.Seam
