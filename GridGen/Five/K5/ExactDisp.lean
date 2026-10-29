/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.ExactSound
import GridGen.Five.Small5.DispBase

/-!
# Height five at `k = 5`: dispatching list systems to shapes, and row reflection

* **Row reflection** (`seam_of_rev55`): the seam inequality for the reversed lists gives it for the
  lists (`GU` and `GB` are invariant, `GU_rev55`, `Ex5.GB_rev`).
* **Reversed atoms** (`card_atomSet_rev`): the atom of mask `m` of the reversed lists is the atom
  of the bit-reversed mask `rbits m` of the lists.
* **Dispatch** (`dispatch_of_searchX`): the pruned search of `GridGen/Five/Small5/DispBase.lean`
  (`search`, complete by `search_sound`) over the atom sizes, with a hit test against a table of
  certificates in either orientation (`hitX`). Five `5`-lists have atoms of at most five colours
  (`atoms_lt7_5`).
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### Row reflection -/

theorem seam_of_rev55 {w : Wt5} {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (h : ∑ s ∈ sts X₅ X₄ X₃ X₂ X₁, GU 5 w s ≤ ∑ s ∈ sts X₅ X₄ X₃ X₂ X₁, GB w B₅ B₄ B₃ B₂ B₁ s) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  rw [sum_sts_rev X₁, sum_sts_rev X₁ X₂ X₃ X₄ X₅ (GB w B₁ B₂ B₃ B₄ B₅)]
  have e1 : ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GU 5 w (rev5 t) = ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GU 5 w t :=
    Finset.sum_congr rfl fun t ht => GU_rev55 w (proper_of_mem_sts ht)
  have e2 : ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GB w B₁ B₂ B₃ B₄ B₅ (rev5 t)
      = ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GB w B₅ B₄ B₃ B₂ B₁ t :=
    Finset.sum_congr rfl fun t _ => by rw [← GB_rev w B₅ B₄ B₃ B₂ B₁ t]
  rw [e1, e2]; exact h

/-! ### Reversed atoms -/

/-- Reverse five bits. -/
def rbits (m : ℕ) : ℕ :=
  mk5 (m.testBit 4) (m.testBit 3) (m.testBit 2) (m.testBit 1) (m.testBit 0)

theorem rbits_mk5 (b0 b1 b2 b3 b4 : Bool) : rbits (mk5 b0 b1 b2 b3 b4) = mk5 b4 b3 b2 b1 b0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem rbits_rbits : ∀ m < 32, rbits (rbits m) = m := by decide

theorem rbits_lt : ∀ m < 32, rbits m < 32 := by decide

theorem memv5_rev (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (c : ℕ) :
    memv5 B₅ B₄ B₃ B₂ B₁ c = rbits (memv5 B₁ B₂ B₃ B₄ B₅ c) := by
  rw [memv5_eq, memv5_eq, rbits_mk5]

theorem union_rev (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) :
    B₅ ∪ B₄ ∪ B₃ ∪ B₂ ∪ B₁ = B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ := by
  ext c; simp only [Finset.mem_union]; tauto

theorem card_atomSet_rev (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {m : ℕ} (hm : m < 32) :
    (atomSet B₅ B₄ B₃ B₂ B₁ m).card = (atomSet B₁ B₂ B₃ B₄ B₅ (rbits m)).card := by
  unfold atomSet
  rw [union_rev]
  congr 1
  refine Finset.filter_congr fun c _ => ?_
  rw [memv5_rev]
  constructor
  · intro h; rw [← h, rbits_rbits _ (memv5_lt _ _ _ _ _ c)]
  · intro h; rw [h, rbits_rbits _ hm]

/-! ### Dispatch -/

/-- The atom sizes (masks `1, …, 31`) of a table entry. -/
def sizesOf (A : List (ℕ × ℕ)) : List ℕ := masks31.map (asz A)

/-- The bit-reversed size vector. -/
def revSizes (xs : List ℕ) : List ℕ := masks31.map fun m => xs.getD (rbits m - 1) 0

/-- The hit test: the sizes are those of a certificate, or of its reflection. -/
def hitX (T : List XSpec) (xs : List ℕ) : Bool :=
  T.any fun sp => decide (sizesOf sp.atoms = xs) || decide (sizesOf sp.atoms = revSizes xs)

theorem sizes_get (f : ℕ → ℕ) {m : ℕ} (h1 : 0 < m) (h2 : m < 32) :
    (masks31.map f).getD (m - 1) 0 = f m := by
  interval_cases m <;> rfl

theorem atoms_of_sizes {sp : XSpec} {f : ℕ → ℕ} (h : sizesOf sp.atoms = masks31.map f) :
    ∀ m, 0 < m → m < 32 → f m = asz sp.atoms m := by
  intro m h1 h2
  have := congrArg (fun L => L.getD (m - 1) 0) h
  simp only [sizesOf] at this
  rw [sizes_get _ h1 h2, sizes_get _ h1 h2] at this
  exact this.symm

theorem hitX_atoms {T : List XSpec} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (h : hitX T (masks31.map fun k => (atomSet B₁ B₂ B₃ B₄ B₅ k).card) = true) :
    ∃ sp ∈ T, AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅ ∨ AtomsMatch sp.toSpec5 B₅ B₄ B₃ B₂ B₁ := by
  obtain ⟨sp, hsp, he⟩ := List.any_eq_true.mp h
  refine ⟨sp, hsp, ?_⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq] at he
  rcases he with he | he
  · left
    intro m h1 h2
    exact atoms_of_sizes he m h1 h2
  · right
    intro m h1 h2
    have e : revSizes (masks31.map fun k => (atomSet B₁ B₂ B₃ B₄ B₅ k).card)
        = masks31.map fun k => (atomSet B₅ B₄ B₃ B₂ B₁ k).card := by
      unfold revSizes
      refine List.map_congr_left fun k hk => ?_
      have hk' : 0 < k ∧ k < 32 := by
        simp only [masks31, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
      have hr1 : 0 < rbits k := by
        have := rbits_rbits k hk'.2
        by_contra h0; push_neg at h0
        have h00 : rbits k = 0 := by omega
        rw [h00] at this; simp [rbits, mk5] at this; omega
      rw [sizes_get _ hr1 (rbits_lt k hk'.2), card_atomSet_rev _ _ _ _ _ hk'.2]
    rw [e] at he
    exact atoms_of_sizes he m h1 h2

/-- **Dispatch from a search**, against a table of certificates. -/
theorem dispatch_of_searchX {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (T : List XSpec) (E : List (List ℕ × ℕ))
    (ord : List (ℕ × List ℕ × List ℕ))
    (hs : search E (fun a => hitX T (masks31.map a)) ord (fun _ => 0) (E.map fun _ => 0) = true ∧
      ordOk E ord = true)
    (hE : ∀ c ∈ E, lsum (fun k => (atomSet B₁ B₂ B₃ B₄ B₅ k).card) c.1 = c.2)
    (h7 : ∀ k, 0 < k → k < 32 → (atomSet B₁ B₂ B₃ B₄ B₅ k).card < 7) :
    ∃ sp ∈ T, AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅ ∨ AtomsMatch sp.toSpec5 B₅ B₄ B₃ B₂ B₁ := by
  obtain ⟨hs, hok⟩ := hs
  simp only [ordOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Nat.beq_eq, List.any_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hcov, hnod⟩, hind⟩, hnd⟩, hfl⟩ := hok
  refine hitX_atoms ?_
  have hs' : search E (fun a => hitX T (masks31.map a)) ord (fun _ => 0)
      (E.map fun c => lsum (fun _ => 0) c.1) = true := by
    have e : ∀ S : List ℕ, lsum (fun _ => 0) S = 0 := fun S => by
      induction S with
      | nil => rfl
      | cons m S ih => simp [lsum, ih]
    simpa [e] using hs
  have := search_sound E _ (fun k => (atomSet B₁ B₂ B₃ B₄ B₅ k).card) hE hnd ord (fun _ => 0) hnod
    hfl ?_ (fun _ => Nat.zero_le _) ?_ hs'
  · simpa using this
  · intro p hp
    refine ⟨?_, hind p hp, rfl⟩
    by_cases hk : p.1 = 0 ∨ 32 ≤ p.1
    · rw [atomSet_card_zero _ _ _ _ _ hk]; norm_num
    · exact h7 p.1 (by omega) (by omega)
  · intro k hk
    by_cases hk' : k = 0 ∨ 32 ≤ k
    · rw [atomSet_card_zero _ _ _ _ _ hk']
    · exfalso
      rcases hcov k (by omega) with h0 | ⟨p, hp, e⟩
      · omega
      · exact hk p hp e

/-- The atoms of five `5`-lists have fewer than `7` elements. -/
theorem atoms_lt7_5 {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) :
    ∀ k, 0 < k → k < 32 → (atomSet B₁ B₂ B₃ B₄ B₅ k).card < 7 := by
  obtain ⟨l1, l2, l3, l4, l5, -, -, -, -⟩ := venn_lin B₁ B₂ B₃ B₄ B₅
  intro k h0 h32
  interval_cases k
  all_goals first
    | (clear l2 l3 l4 l5; omega)
    | (clear l1 l3 l4 l5; omega)
    | (clear l1 l2 l4 l5; omega)
    | (clear l1 l2 l3 l5; omega)
    | (clear l1 l2 l3 l4; omega)

/-! ### Certificates checked in groups -/

/-- The default pattern data. -/
def dpc : PatD × List (List (ℕ × ℕ) × ℕ) := (⟨0, 0, []⟩, [])

/-- All split checks `(pattern position, i, j)`, in order. -/
def allTriples (sp : XSpec) : List (ℕ × ℕ × ℕ) :=
  (List.range sp.pds.length).flatMap fun p =>
    (List.range ((sp.pds.getD p dpc).1.chs.getD 0 []).length).flatMap fun i =>
      (List.range ((sp.pds.getD p dpc).1.chs.getD 1 []).length).map fun j => (p, i, j)

/-- The groups are the split checks, in order. -/
def coverOK (sp : XSpec) (G : List (List (ℕ × ℕ × ℕ))) : Bool := decide (G.flatten = allTriples sp)

/-- A group of split checks passes. -/
def grpOK (sp : XSpec) (g : List (ℕ × ℕ × ℕ)) : Bool :=
  g.all fun t => subOK sp (sp.pds.getD t.1 dpc) t.2.1 t.2.2

/-- **A certificate checked in groups passes.** -/
theorem xpass_of {sp : XSpec} (hspec : specOkX sp = true) (hhdr : sp.pds.all (hdrOK sp) = true)
    (G : List (List (ℕ × ℕ × ℕ))) (hcov : coverOK sp G = true)
    (hg : ∀ k < G.length, grpOK sp (G.getD k []) = true) : XPass sp := by
  refine ⟨hspec, fun pc hpc => ⟨List.all_eq_true.mp hhdr pc hpc, fun i hi j hj => ?_⟩⟩
  obtain ⟨p, hp, rfl⟩ := getD_of_mem dpc hpc
  have hmem : (p, i, j) ∈ G.flatten := by
    rw [of_decide_eq_true hcov]
    simp only [allTriples, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨p, hp, i, hi, j, hj, rfl⟩
  obtain ⟨g, hgm, hpg⟩ := List.mem_flatten.mp hmem
  obtain ⟨k, hk, rfl⟩ := getD_of_mem [] hgm
  exact List.all_eq_true.mp (hg k hk) (p, i, j) hpg

end GridGen.Five.K5
