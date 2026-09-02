import Mathlib
open Finset
namespace Grid3.Three.TypeClass

-- Sec2 type layer
def patHasRow (p : Fin 7) (i : Fin 3) : Bool := Nat.testBit (p.val + 1) i.val

/-- The row-`i` colour count of a type: `∑_{S ∋ i} m_S`. -/
def rowSum (m : Fin 7 → Fin 4) (i : Fin 3) : ℕ :=
  ∑ p : Fin 7, if patHasRow p i then (m p : ℕ) else 0

/-- A **type**: every row's list has exactly 3 colours. -/
def IsType (m : Fin 7 → Fin 4) : Prop := ∀ i : Fin 3, rowSum m i = 3

-- Bridge layer (column → pattern counts)
variable (L : Fin 3 → Finset ℕ)

/-- All colours appearing in the column. -/
def colColors : Finset ℕ := L 0 ∪ L 1 ∪ L 2

/-- The row-pattern of a colour. -/
def pat (c : ℕ) : Finset (Fin 3) := Finset.univ.filter (fun i => c ∈ L i)

/-- The type count for a nonempty pattern `S`: how many colours have exactly that pattern. -/
def mS (S : Finset (Fin 3)) : ℕ := ((colColors L).filter (fun c => pat L c = S)).card

lemma mem_colColors_of_mem {i : Fin 3} {c : ℕ} (h : c ∈ L i) : c ∈ colColors L := by
  fin_cases i <;> simp only [colColors, Finset.mem_union] <;> tauto

/-- The colours of row `i` are exactly the column-colours whose pattern contains `i`. -/
lemma filter_pat_mem (i : Fin 3) :
    (colColors L).filter (fun c => i ∈ pat L c) = L i := by
  ext c
  simp only [Finset.mem_filter, pat, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨mem_colColors_of_mem L h, h⟩

/-- **Row constraint:** each row lists exactly 3 colours. -/
lemma row_card_three (h3 : ∀ i, (L i).card = 3) (i : Fin 3) :
    ((colColors L).filter (fun c => i ∈ pat L c)).card = 3 := by
  rw [filter_pat_mem L i, h3 i]

/-- **Type constraint `∑_{S ∋ i} mS S = 3`.**  The patterns containing `i` partition the row-`i`
    colours, so the counts sum to `|L i| = 3`. -/
theorem type_constraint (h3 : ∀ i, (L i).card = 3) (i : Fin 3) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S), mS L S = 3 := by
  classical
  have hH : ∀ c ∈ (colColors L).filter (fun c => i ∈ pat L c),
      pat L c ∈ Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc.2
  have step : ((colColors L).filter (fun c => i ∈ pat L c)).card
      = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S), mS L S := by
    rw [Finset.card_eq_sum_card_fiberwise hH]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    unfold mS
    congr 1
    ext c
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hc, _⟩, hpat⟩; exact ⟨hc, hpat⟩
    · rintro ⟨hc, hpat⟩; exact ⟨⟨hc, hpat ▸ hS⟩, hpat⟩
  rw [← step]; exact row_card_three L h3 i

/-- The row-subset encoded by pattern index `p`. -/
def subset (p : Fin 7) : Finset (Fin 3) := Finset.univ.filter (fun i => patHasRow p i)

lemma mem_subset (p : Fin 7) (i : Fin 3) : i ∈ subset p ↔ patHasRow p i := by
  simp [subset]

/-- `subset` is injective and its image is exactly the nonempty subsets. -/
lemma subset_inj : Function.Injective subset := by decide

lemma subset_i_bij : ∀ i : Fin 3,
    (Finset.univ.filter (fun p : Fin 7 => patHasRow p i)).image subset
      = Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S) := by decide

/-- Column type as a count vector. -/
def colType (L : Fin 3 → Finset ℕ) (p : Fin 7) : ℕ := mS L (subset p)

lemma subset_nonempty : ∀ p : Fin 7, (subset p).Nonempty := by decide

lemma colType_le (L : Fin 3 → Finset ℕ) (h3 : ∀ i, (L i).card = 3) (p : Fin 7) : colType L p ≤ 3 := by
  obtain ⟨i, hi⟩ := subset_nonempty p
  have hmem : subset p ∈ Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
  calc colType L p = mS L (subset p) := rfl
    _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S), mS L S :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
    _ = 3 := type_constraint L h3 i

/-- **Column → Sec2 type.** -/
def colTypeFin (L : Fin 3 → Finset ℕ) (h3 : ∀ i, (L i).card = 3) : Fin 7 → Fin 4 :=
  fun p => ⟨colType L p, Nat.lt_succ_of_le (colType_le L h3 p)⟩

theorem colType_isType (L : Fin 3 → Finset ℕ) (h3 : ∀ i, (L i).card = 3) :
    IsType (colTypeFin L h3) := by
  intro i
  rw [rowSum]
  have step : (∑ p : Fin 7, if patHasRow p i then (colTypeFin L h3 p : ℕ) else 0)
      = ∑ p ∈ Finset.univ.filter (fun p : Fin 7 => patHasRow p i), colType L p := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun p _ => by by_cases h : patHasRow p i <;> simp [h, colTypeFin])
  have hb : (∑ p ∈ Finset.univ.filter (fun p : Fin 7 => patHasRow p i), colType L p)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S), mS L S := by
    rw [← subset_i_bij i, Finset.sum_image (fun a _ b _ h => subset_inj h)]
    rfl
  rw [step, hb]; exact type_constraint L h3 i

end Grid3.Three.TypeClass
