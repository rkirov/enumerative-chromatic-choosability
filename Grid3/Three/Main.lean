import Grid3.Three.SeamData
import Grid3.AllU
import Grid3.Statements
import Grid3.Three.FinalModel

/-!
# Height-three grids are `3`-ECC

`ecc_grid3_three`: for every `n`, `(pathG 2 □ pathG n).ECCAt 3` — no assignment of three-element
lists to the `3 × (n+1)` grid admits fewer proper colourings than the constant assignment.

The proof is the three-way split of Kirov–Naimi's argument. If every column is uniform (its
three lists agree), the gauge injection of `Grid3/AllU.lean` applies. Otherwise the concrete
columns carry the laws `lawC` and the seams the kernels of `seam_exists`, and the entropy
capstone `colConst_le_col_of_model` (`Grid3/Three/FinalModel.lean`) turns the chain into the
count inequality: a nonuniform first column has root entropy at least `log 12` (collision mass at
most `1/12`), while a uniform first column has `log 12 - log (18/17)` (collision mass `3/34`) and
the first seam into a nonuniform column repays the deficit. A single column (`n = 0`) is the
path `P₃`, and paths are ECC.
-/

open Finset ListColoring SimpleGraph
open scoped SimpleGraph

namespace Grid3.Three

open Seam Col

/-! ### Columns of a list assignment -/

/-- the lists of column `j`, in the model's indexing -/
def colOf (n : ℕ) (L : ListAssignment (PathV 2 × PathV n)) (j : Fin (n + 1)) :
    Fin 3 → Finset ℕ :=
  fun i => L ((Model.gridIso n).symm (i, j))

theorem gridIso_symm_apply (n : ℕ) (i : Fin 3) (j : Fin (n + 1)) :
    (Model.gridIso n).symm (i, j) = ((Model.pathEquiv 2).symm i, (Model.pathEquiv n).symm j) := rfl

/-- a bound above every colour of the assignment -/
def colourBound (n : ℕ) (L : ListAssignment (PathV 2 × PathV n)) : ℕ :=
  (Finset.univ.sup fun v => (L v).sup id) + 1

theorem lt_colourBound (n : ℕ) (L : ListAssignment (PathV 2 × PathV n)) (v : PathV 2 × PathV n)
    (c : ℕ) (hc : c ∈ L v) : c < colourBound n L := by
  unfold colourBound
  have h1 : c ≤ (L v).sup id := Finset.le_sup (f := id) hc
  have h2 : (L v).sup id ≤ Finset.univ.sup fun v => (L v).sup id :=
    Finset.le_sup (f := fun v => (L v).sup id) (Finset.mem_univ v)
  omega

theorem colours_lt (n : ℕ) (L : ListAssignment (PathV 2 × PathV n)) (j : Fin (n + 1)) (c : ℕ)
    (hc : c ∈ Col.colours (colOf n L j)) : c < colourBound n L := by
  obtain ⟨r, hr⟩ := (mem_colours _ c).1 hc
  exact lt_colourBound n L _ c hr

/-- uniformity of a column, in the model's indexing -/
def ColU (n : ℕ) (L : ListAssignment (PathV 2 × PathV n)) (j : Fin (n + 1)) : Prop :=
  ∀ r, colOf n L j r = colOf n L j 0

/-! ### The entropy half, `n ≥ 1` -/

theorem entropy_half_pos (n : ℕ) (L : ListAssignment (PathV 2 × PathV n))
    (h3 : IsNListAssignment L 3) (hne : ∃ j, ¬ ColU n L j) (hn : 1 ≤ n) :
    (pathG 2 □ pathG n).colConst 3 ≤ (pathG 2 □ pathG n).col L := by
  classical
  set B := colourBound n L with hBdef
  set C := B + 32 with hCdef
  have h3c : ∀ (j : Fin (n + 1)) (r : Fin 3), (colOf n L j r).card = 3 := fun j r => h3 _
  have hB : ∀ j, ∀ c ∈ Col.colours (colOf n L j), c < B := fun j c hc => colours_lt n L j c hc
  have hBC : B + 32 ≤ C := le_refl _
  -- one kernel per seam
  have hseam : ∀ k : Fin n, ∃ K : (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ,
      (∀ c s, 0 ≤ K c s) ∧ (∀ c, ∑ s, K c s = 1)
      ∧ (∀ s, ∑ c, lawC (colOf n L k.castSucc) c * K c s = lawC (colOf n L k.succ) s)
      ∧ (∀ c s, 0 < lawC (colOf n L k.castSucc) c → 0 < K c s → ∀ i, c i ≠ s i)
      ∧ Real.log rho ≤ ∑ c, lawC (colOf n L k.castSucc) c * rowH K c
      ∧ (ColU n L k.castSucc → ¬ ColU n L k.succ →
          Real.log rho + Real.log (18 / 17) ≤ ∑ c, lawC (colOf n L k.castSucc) c * rowH K c)
      ∧ (¬ ColU n L k.castSucc →
          ∑ c : Fin 3 → Fin C, lawC (colOf n L k.castSucc) c = 1
          ∧ ∑ c : Fin 3 → Fin C, lawC (colOf n L k.castSucc) c ^ 2 ≤ 1 / 12) :=
    fun k => seam_exists _ _ (h3c _) (h3c _) B C (hB _) (hB _) hBC
  choose Kf hKf using hseam
  let law : ℕ → (Fin 3 → Fin C) → ℝ := fun k =>
    if h : k < n + 1 then lawC (colOf n L ⟨k, h⟩) else 0
  let K : ℕ → (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ := fun k =>
    if h : k < n then Kf ⟨k, h⟩ else fun _ _ => 1 / (Fintype.card (Fin 3 → Fin C) : ℝ)
  have hlaw : ∀ (j : Fin (n + 1)), law j.val = lawC (colOf n L j) := fun j => by
    simp only [law, dif_pos j.isLt]
  have hK : ∀ (k : Fin n), K k.val = Kf k := fun k => by simp only [K, dif_pos k.isLt]
  have hfall : ∀ k, n ≤ k → K k = fun _ _ => 1 / (Fintype.card (Fin 3 → Fin C) : ℝ) := fun k hk => by
    simp only [K, dif_neg (not_lt.2 hk)]
  have hcard : (Fintype.card (Fin 3 → Fin C) : ℝ) ≠ 0 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have : 0 < C := by omega
    positivity
  -- the root facts
  have hroot0 : ∑ s, law 0 s = 1 ∧
      (ColU n L 0 → ∑ s, law 0 s ^ 2 = 3 / 34) ∧ (¬ ColU n L 0 → ∑ s, law 0 s ^ 2 ≤ 1 / 12) := by
    have h0 : law 0 = lawC (colOf n L 0) := hlaw 0
    rw [h0]
    by_cases hU : ColU n L 0
    · have := lawC_U_facts (colOf n L 0) hU (h3c 0) B C (hB 0) hBC
      exact ⟨this.1, fun _ => this.2, fun h => absurd hU h⟩
    · have hk : (⟨0, hn⟩ : Fin n).castSucc = 0 := rfl
      have := (hKf ⟨0, hn⟩).2.2.2.2.2.2 (by rw [hk]; exact hU)
      rw [hk] at this
      exact ⟨this.1, fun h => absurd h hU, fun _ => this.2⟩
  apply colConst_le_col_of_model n C L law K
  · -- nonnegativity of the laws
    intro k s
    simp only [law]
    split_ifs
    · exact lawC_nonneg _ _
    · exact le_refl _
  · exact hroot0.1
  · -- nonnegativity of the kernels
    intro k c s
    by_cases hk : k < n
    · rw [hK ⟨k, hk⟩]; exact (hKf ⟨k, hk⟩).1 c s
    · rw [hfall k (not_lt.1 hk)]; positivity
  · -- rows sum to one
    intro k c
    by_cases hk : k < n
    · rw [hK ⟨k, hk⟩]; exact (hKf ⟨k, hk⟩).2.1 c
    · rw [hfall k (not_lt.1 hk)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
  · -- the marginal step
    intro k hk s
    have e1 : law k = lawC (colOf n L (⟨k, hk⟩ : Fin n).castSucc) := hlaw (⟨k, hk⟩ : Fin n).castSucc
    have e2 : law (k + 1) = lawC (colOf n L (⟨k, hk⟩ : Fin n).succ) := hlaw (⟨k, hk⟩ : Fin n).succ
    have e3 : K k = Kf ⟨k, hk⟩ := hK ⟨k, hk⟩
    rw [e1, e2, e3]
    exact (hKf ⟨k, hk⟩).2.2.1 s
  · -- list membership on positive states
    intro j s hs i
    rw [hlaw j] at hs
    exact (isCol_of_lawC_pos _ s hs).1 i
  · -- adjacent rows differ
    intro j s hs i i' hii'
    rw [hlaw j] at hs
    obtain ⟨-, h01, h12⟩ := isCol_of_lawC_pos _ s hs
    rcases i with ⟨i, hi⟩; rcases i' with ⟨i', hi'⟩
    simp only at hii'
    rcases (by omega : i = 0 ∧ i' = 1 ∨ i = 1 ∧ i' = 2) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h01
    · exact h12
  · -- horizontal compatibility on positive transitions
    intro k hk c s hc hK'
    have e1 : law k = lawC (colOf n L (⟨k, hk⟩ : Fin n).castSucc) := hlaw (⟨k, hk⟩ : Fin n).castSucc
    have e3 : K k = Kf ⟨k, hk⟩ := hK ⟨k, hk⟩
    rw [e1] at hc
    rw [e3] at hK'
    exact (hKf ⟨k, hk⟩).2.2.2.1 c s hc hK'
  · -- the seam entropy bounds
    intro k hk
    have e1 : law k = lawC (colOf n L (⟨k, hk⟩ : Fin n).castSucc) := hlaw (⟨k, hk⟩ : Fin n).castSucc
    have e3 : K k = Kf ⟨k, hk⟩ := hK ⟨k, hk⟩
    rw [e1, e3]
    exact (hKf ⟨k, hk⟩).2.2.2.2.1
  · -- the root
    by_cases hU : ColU n L 0
    · right
      refine ⟨?_, ?_⟩
      · exact H_ge_log34_div3 (law 0) (fun s => by
            simp only [law]; split_ifs
            · exact lawC_nonneg _ _
            · exact le_refl _) hroot0.1 (le_of_eq (hroot0.2.1 hU))
      · -- the first nonuniform column pays the deficit
        have hP : ∃ j : ℕ, ∃ h : j < n + 1, ¬ ColU n L ⟨j, h⟩ := by
          obtain ⟨j, hj⟩ := hne; exact ⟨j.val, j.isLt, by simpa using hj⟩
        set j0 := Nat.find hP with hj0
        obtain ⟨hj0lt, hj0nu⟩ := Nat.find_spec hP
        have hj0pos : 0 < j0 := by
          rcases Nat.eq_zero_or_pos j0 with h0 | h0
          · exfalso
            apply hj0nu
            have : (⟨j0, hj0lt⟩ : Fin (n + 1)) = 0 := Fin.ext h0
            rw [this]; exact hU
          · exact h0
        have hprev : ColU n L ⟨j0 - 1, by omega⟩ := by
          by_contra hc
          have := Nat.find_min hP (show j0 - 1 < j0 by omega)
          exact this ⟨by omega, hc⟩
        refine ⟨⟨j0 - 1, by omega⟩, ?_⟩
        have hcs : (⟨j0 - 1, by omega⟩ : Fin n).castSucc = ⟨j0 - 1, by omega⟩ := rfl
        have hsu : (⟨j0 - 1, by omega⟩ : Fin n).succ = ⟨j0, hj0lt⟩ := Fin.ext (by simp; omega)
        have := (hKf ⟨j0 - 1, by omega⟩).2.2.2.2.2.1 (by rw [hcs]; exact hprev) (by rw [hsu]; exact hj0nu)
        rw [hcs] at this
        show Real.log rho + Real.log (18 / 17) ≤ ∑ c, law (j0 - 1) c * rowH (K (j0 - 1)) c
        have e1 : law (j0 - 1) = lawC (colOf n L (⟨j0 - 1, by omega⟩ : Fin n).castSucc) :=
          hlaw (⟨j0 - 1, by omega⟩ : Fin n).castSucc
        have e3 : K (j0 - 1) = Kf ⟨j0 - 1, by omega⟩ := hK ⟨j0 - 1, by omega⟩
        rw [e1, e3]
        exact this
    · left
      exact H_ge_log12 (law 0) (fun s => by
          simp only [law]; split_ifs
          · exact lawC_nonneg _ _
          · exact le_refl _) hroot0.1 (hroot0.2.2 hU)

/-! ### A single column is the path `P₃` -/

instance : Unique (PathV 0) := inferInstanceAs (Unique Unit)

/-- the `3 × 1` grid is the path on three vertices -/
def gridZeroIso : (pathG 2 □ pathG 0) ≃g pathG 2 where
  toEquiv := Equiv.prodUnique (PathV 2) (PathV 0)
  map_rel_iff' := by
    intro a b
    rw [boxProd_adj]
    simp only [Equiv.prodUnique_apply, pathG_zero, SimpleGraph.bot_adj, false_and, or_false,
      Subsingleton.elim a.2 b.2, and_true]

theorem ecc_grid3_three_zero : (pathG 2 □ pathG 0).ECCAt 3 :=
  (ecc_iso gridZeroIso 3).2 (ecc_pathG 2 3)

/-! ### The theorem -/

/-- **Height-three grids are `3`-ECC.** -/
theorem ecc_grid3_three (n : ℕ) : (pathG 2 □ pathG n).ECCAt 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ecc_grid3_three_zero
  intro L h3
  by_cases hall : ∀ j, ColU n L j
  · -- every column uniform: the gauge injection
    apply Grid3.AllU.colConst_le_col_of_allU n L h3
    intro r c
    set j := Model.pathEquiv n c with hj
    have hc : c = (Model.pathEquiv n).symm j := by rw [hj, Equiv.symm_apply_apply]
    have key : ∀ x : PathV 2, L (x, c) = colOf n L j 0 := by
      intro x
      have := hall j (Model.pathEquiv 2 x)
      rw [colOf, gridIso_symm_apply, Equiv.symm_apply_apply, ← hc] at this
      exact this
    rw [key r, key rowT]
  · rw [not_forall] at hall
    exact entropy_half_pos n L h3 hall hn

/-- **Height-three grids are `k`-ECC for every `k ≥ 3`**: `k = 3` here, `k ≥ 4` from
`ListColoring.ecc_boxProd_pathG_two_of_four`. -/
theorem ecc_boxProd_pathG_two_of_three {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    (pathG 2 □ pathG n).ECCAt k := by
  rcases Nat.lt_or_ge k 4 with h | h
  · have hk3 : k = 3 := by omega
    subst hk3
    exact ecc_grid3_three n
  · exact ListColoring.ecc_boxProd_pathG_two_of_four h n

end Grid3.Three

namespace ListColoring

/-- **Height-three grids are `k`-ECC for every `k ≥ 3`**, under the name the comparator surface
`comparator/Challenge.lean` states it by (next to `ecc_boxProd_pathG_two_of_four`). -/
theorem ecc_boxProd_pathG_two_of_three {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    (pathG 2 □ pathG n).ECCAt k :=
  Grid3.Three.ecc_boxProd_pathG_two_of_three hk n

end ListColoring

#print axioms Grid3.Three.ecc_grid3_three
#print axioms ListColoring.ecc_boxProd_pathG_two_of_three
