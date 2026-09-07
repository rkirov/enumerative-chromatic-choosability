import Grid3.Three.Column
import Grid3.Three.Glue
import Grid3.Three.Cert.KeyExt

/-!
# Concrete seams: the packed key and the colour maps

Two adjacent columns `Lc`, `Lc'` determine a packed key `(packType Lc, packType Lc', Mact)`:
`Mact` counts, for each pair of pattern indices `(p, q)`, the colours common to both columns whose
two patterns share a row (`commonI`). The key is valid (`validKey_Mact`), so by
`Cert.exists_maximal` it lies below a valid maximal key `M`, which is what the certificate
covers.

For such an `M`, the canonical colour list `Cert.colours mL mR M` is a list of *slots*, each
carrying a left pattern and a right pattern. `exists_colourMaps` builds injections from the
actual colours of each column into the slots: pattern-preserving, agreeing on the common
colours of `commonI` (whose slots are matched), and with inverses on the active slots. Every
class of colours (a common kind `(p, q)`, or the left-only/right-only colours of one pattern) is
matched with a class of slots of the same cardinality (`Glue.exists_glued`); the surplus
matched slots of the maximal key absorb left-only and right-only colours, which is exactly why
canonical compatibility implies actual compatibility (`Transport.lean`).
-/

open Finset

namespace Grid3.Three.Seam

open Cert Col Glue

/-! ### Packing a list of base-4 digits -/

def packL : List ℕ → ℕ
  | [] => 0
  | d :: L => d + 4 * packL L

theorem packL_lt : ∀ L : List ℕ, (∀ d ∈ L, d < 4) → packL L < 4 ^ L.length
  | [], _ => by simp [packL]
  | d :: L, h => by
    have hd : d < 4 := h d (by simp)
    have ih := packL_lt L (fun x hx => h x (by simp [hx]))
    simp only [packL, List.length_cons, Nat.pow_succ]
    omega

theorem packL_digit : ∀ (L : List ℕ), (∀ d ∈ L, d < 4) → ∀ j (hj : j < L.length),
    packL L / 4 ^ j % 4 = L[j]
  | [], _, j, hj => by simp at hj
  | d :: L, h, 0, _ => by
    have hd : d < 4 := h d (by simp)
    simp only [packL, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
    omega
  | d :: L, h, j + 1, hj => by
    have hd : d < 4 := h d (by simp)
    have ih := packL_digit L (fun x hx => h x (by simp [hx])) j (by simpa using hj)
    simp only [packL, List.getElem_cons_succ]
    rw [Nat.pow_succ, Nat.mul_comm (4 ^ j) 4, ← Nat.div_div_eq_div_mul,
      show (d + 4 * packL L) / 4 = packL L by omega]
    exact ih

/-! ### The actual matching of a seam -/

variable (Lc Lc' : Fin 3 → Finset ℕ)

/-- common colours whose two patterns share a row -/
def commonI : Finset ℕ :=
  (colours Lc ∩ colours Lc').filter fun c => (patOf Lc c) &&& (patOf Lc' c) ≠ 0

theorem commonI_subset_left : commonI Lc Lc' ⊆ colours Lc := fun c hc =>
  (Finset.mem_inter.1 (Finset.mem_filter.1 hc).1).1

theorem commonI_subset_right : commonI Lc Lc' ⊆ colours Lc' := fun c hc =>
  (Finset.mem_inter.1 (Finset.mem_filter.1 hc).1).2

theorem mem_commonI (c : ℕ) : c ∈ commonI Lc Lc' ↔
    c ∈ colours Lc ∧ c ∈ colours Lc' ∧ (patOf Lc c) &&& (patOf Lc' c) ≠ 0 := by
  unfold commonI; simp [Finset.mem_filter, Finset.mem_inter, and_assoc]

/-- the actual matching count of kind `(p, q)` (pattern indices) -/
def mact (p q : ℕ) : ℕ :=
  ((commonI Lc Lc').filter fun c => patOf Lc c = p + 1 ∧ patOf Lc' c = q + 1).card

/-- the packed actual matching matrix -/
def Mact : ℕ := packL (List.ofFn fun i : Fin 49 => mact Lc Lc' (i.val / 7) (i.val % 7))

theorem mact_le_cnt (p q : ℕ) : mact Lc Lc' p q ≤ cnt Lc p := by
  apply Finset.card_le_card
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨commonI_subset_left Lc Lc' hc.1, hc.2.1⟩

theorem mact_le_cnt' (p q : ℕ) : mact Lc Lc' p q ≤ cnt Lc' q := by
  apply Finset.card_le_card
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨commonI_subset_right Lc Lc' hc.1, hc.2.2⟩

theorem mact_lt (h3 : ∀ r, (Lc r).card = 3) (p q : ℕ) (hp : p < 7) : mact Lc Lc' p q < 4 :=
  lt_of_le_of_lt (mact_le_cnt Lc Lc' p q) (by have := cnt_le Lc h3 p hp; omega)

theorem Mact_digits_lt (h3 : ∀ r, (Lc r).card = 3) :
    ∀ d ∈ (List.ofFn fun i : Fin 49 => mact Lc Lc' (i.val / 7) (i.val % 7)), d < 4 := by
  intro d hd
  rw [List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  exact mact_lt Lc Lc' h3 _ _ (by omega)

theorem mcount_Mact (h3 : ∀ r, (Lc r).card = 3) (p q : ℕ) (hp : p < 7) (hq : q < 7) :
    mcount (Mact Lc Lc') p q = mact Lc Lc' p q := by
  rw [mcount_eq_digit_cell]
  unfold digit Mact
  have hj : 7 * p + q < (List.ofFn fun i : Fin 49 => mact Lc Lc' (i.val / 7) (i.val % 7)).length := by
    simp; omega
  rw [packL_digit _ (Mact_digits_lt Lc Lc' h3) (7 * p + q) hj, List.getElem_ofFn]
  simp only
  congr 1 <;> omega

theorem Mact_lt (h3 : ∀ r, (Lc r).card = 3) : Mact Lc Lc' < 16384 ^ 7 := by
  have := packL_lt _ (Mact_digits_lt Lc Lc' h3)
  simp only [List.length_ofFn] at this
  rw [pow49]; exact this

/-- the row sums of `Mact` count the common colours of a left pattern -/
theorem sumRow_Mact (h3 : ∀ r, (Lc r).card = 3) (p : ℕ) (hp : p < 7) :
    sumRow (Mact Lc Lc') p = ((commonI Lc Lc').filter fun c => patOf Lc c = p + 1).card := by
  rw [sumRow_eq]
  simp only [mcount_Mact Lc Lc' h3 p _ hp (by decide : (0:ℕ) < 7),
    mcount_Mact Lc Lc' h3 p _ hp (by decide : (1:ℕ) < 7),
    mcount_Mact Lc Lc' h3 p _ hp (by decide : (2:ℕ) < 7),
    mcount_Mact Lc Lc' h3 p _ hp (by decide : (3:ℕ) < 7),
    mcount_Mact Lc Lc' h3 p _ hp (by decide : (4:ℕ) < 7),
    mcount_Mact Lc Lc' h3 p _ hp (by decide : (5:ℕ) < 7),
    mcount_Mact Lc Lc' h3 p _ hp (by decide : (6:ℕ) < 7)]
  have key : ((commonI Lc Lc').filter fun c => patOf Lc c = p + 1).card
      = ∑ q ∈ range 7, mact Lc Lc' p q := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun c => patOf Lc' c - 1) (t := range 7)]
    · apply Finset.sum_congr rfl
      intro q hq
      unfold mact
      congr 1
      ext c
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hc, hpc⟩, hqc⟩
        have hpos := patOf_pos Lc' c (commonI_subset_right Lc Lc' hc)
        exact ⟨hc, hpc, by omega⟩
      · rintro ⟨hc, hpc, hqc⟩
        exact ⟨⟨hc, hpc⟩, by omega⟩
    · intro c hc
      have hle := patOf_le Lc' c
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hc
      show patOf Lc' c - 1 ∈ (range 7 : Set ℕ)
      rw [Finset.mem_coe, Finset.mem_range]; omega
  rw [key]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  omega

theorem sumCol_Mact (h3 : ∀ r, (Lc r).card = 3) (q : ℕ) (hq : q < 7) :
    sumCol (Mact Lc Lc') q = ((commonI Lc Lc').filter fun c => patOf Lc' c = q + 1).card := by
  rw [sumCol_eq]
  simp only [mcount_Mact Lc Lc' h3 _ q (by decide : (0:ℕ) < 7) hq,
    mcount_Mact Lc Lc' h3 _ q (by decide : (1:ℕ) < 7) hq,
    mcount_Mact Lc Lc' h3 _ q (by decide : (2:ℕ) < 7) hq,
    mcount_Mact Lc Lc' h3 _ q (by decide : (3:ℕ) < 7) hq,
    mcount_Mact Lc Lc' h3 _ q (by decide : (4:ℕ) < 7) hq,
    mcount_Mact Lc Lc' h3 _ q (by decide : (5:ℕ) < 7) hq,
    mcount_Mact Lc Lc' h3 _ q (by decide : (6:ℕ) < 7) hq]
  have key : ((commonI Lc Lc').filter fun c => patOf Lc' c = q + 1).card
      = ∑ p ∈ range 7, mact Lc Lc' p q := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun c => patOf Lc c - 1) (t := range 7)]
    · apply Finset.sum_congr rfl
      intro p hp
      unfold mact
      congr 1
      ext c
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hc, hqc⟩, hpc⟩
        have hpos := patOf_pos Lc c (commonI_subset_left Lc Lc' hc)
        exact ⟨hc, by omega, hqc⟩
      · rintro ⟨hc, hpc, hqc⟩
        exact ⟨⟨hc, hqc⟩, by omega⟩
    · intro c hc
      have hle := patOf_le Lc c
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hc
      show patOf Lc c - 1 ∈ (range 7 : Set ℕ)
      rw [Finset.mem_coe, Finset.mem_range]; omega
  rw [key]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  omega

/-- **The actual key is valid.** -/
theorem validKey_Mact (h3 : ∀ r, (Lc r).card = 3) (h3' : ∀ r, (Lc' r).card = 3) :
    validKey (packType Lc) (packType Lc') (Mact Lc Lc') = true := by
  apply validKey_of
  · intro p hp q hq hi
    rw [mcount_Mact Lc Lc' h3 p q hp hq]
    unfold mact
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc ⟨hpc, hqc⟩
    have := ((mem_commonI Lc Lc' c).1 hc).2.2
    rw [hpc, hqc] at this
    unfold inter at hi
    rw [bne_eq_false_iff_eq] at hi
    exact this hi
  · intro p hp
    rw [sumRow_Mact Lc Lc' h3 p hp, mult_packType Lc h3 p hp]
    apply Finset.card_le_card
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨commonI_subset_left Lc Lc' hc.1, hc.2⟩
  · intro q hq
    rw [sumCol_Mact Lc Lc' h3 q hq, mult_packType Lc' h3' q hq]
    apply Finset.card_le_card
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨commonI_subset_right Lc Lc' hc.1, hc.2⟩

/-- **A valid maximal key above the actual one.** -/
theorem exists_Mmax (h3 : ∀ r, (Lc r).card = 3) (h3' : ∀ r, (Lc' r).card = 3) :
    ∃ M, M < 16384 ^ 7 ∧ validKey (packType Lc) (packType Lc') M = true
      ∧ keyMax (packType Lc) (packType Lc') M = true ∧ keyLE (Mact Lc Lc') M :=
  exists_maximal _ _ _ (Mact_lt Lc Lc' h3) (validKey_Mact Lc Lc' h3 h3')

end Grid3.Three.Seam
