/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.PairC

/-!
# Height three at `k = 4`: exact per-colour identities

At `k = 4` the bounds of `Grid3.Pair` and `Grid3.PairC` are too lossy: the pair lemma of the
`k ≥ 5` proof is false, and the column inequality `(C1_r)` itself fails, by exactly one, in one
configuration. The `k = 4` proof therefore works with sharper quantities:

* `betaH`: a lower bound for `QH` obtained by fibring the successor count over the *next*
  column's middle colour, `∑ succ = ∑_{m ∈ M \ y} e₁(m) e₂(m)` with `e₁(m) = 2p + [m ∈ X] + g₁(m)`
  and `g₁ ≥ 0`, and dropping only the cross terms `g₁ [m ∈ Z] + g₂ [m ∈ X] + g₁ g₂`;
* `RC4`: the eq-part `RC` *exactly*, in closed form.

Both are expressed through the cardinalities of punctured sets, which `Grid3.Four.Pair` then
relates to the unpunctured lists.
-/

open Finset

namespace Grid3
namespace Four

/-! ### Punctured quantities -/

/-- `|X \ y|`. -/
def pc (X : Finset ℕ) (y : ℕ) : ℤ := (X.erase y).card

/-- `|(X \ y) \ T|`. -/
def out (X T : Finset ℕ) (y : ℕ) : ℤ := ((X.erase y).filter (· ∉ T)).card

/-- `|((X \ y) ∩ (Z \ y)) \ T|`. -/
def out2 (X Z T : Finset ℕ) (y : ℕ) : ℤ := (((X.erase y) ∩ (Z.erase y)).filter (· ∉ T)).card

/-- `|(X \ y) ∩ (Z \ y) ∩ W|`. -/
def in2 (X Z W : Finset ℕ) (y : ℕ) : ℤ := (((X.erase y) ∩ (Z.erase y)).filter (· ∈ W)).card

/-- `|{m ∈ M \ y : m ∉ T, m ∈ X \ y}|`. -/
def outIn (M T X : Finset ℕ) (y : ℕ) : ℤ :=
  (((M.erase y).filter (· ∉ T)).filter (· ∈ X.erase y)).card

/-- `ω = |T \ B|`. -/
def om (T B : Finset ℕ) : ℤ := (T.filter (· ∉ B)).card

/-- The `(H1)` per-colour lower bound at `k = 4`. -/
def betaH (X Z T M B : Finset ℕ) (y : ℕ) : ℤ :=
  4 * pc X y * pc Z y * (pc M y - 3) - 2 * pc X y * out Z M y - 2 * pc Z y * out X M y
    - out2 X Z M y
    + 2 * pc Z y * (pc M y * out X T y + pc X y * out M T y - outIn M T X y)
    + 2 * pc X y * (pc M y * out Z B y + pc Z y * out M B y - outIn M B Z y)

/-- The eq-part per-colour term at `k = 4`, in closed form. -/
def RC4 (X Z T M B : Finset ℕ) (y : ℕ) : ℤ :=
  pc X y * pc Z y * (pc M y - 3 + out M (T ∩ B) y - pc M y * om T B)
    + pc M y * pc Z y * out X (T ∩ B) y + pc M y * pc X y * out Z (T ∩ B) y
    - pc Z y * out X (T ∩ B ∩ M) y - pc X y * out Z (T ∩ B ∩ M) y
    + pc M y * in2 X Z (T ∩ B) y - in2 X Z (T ∩ B ∩ M) y
    - 2 * (((X.erase y) ∩ (Z.erase y)).card : ℤ)

/-! ### Indicator sums -/

theorem ind_and (p q : Prop) [Decidable p] [Decidable q] : ind (p ∧ q) = ind p * ind q := by
  unfold ind; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem sum_ind_ne (X : Finset ℕ) (c : ℕ) : ∑ a ∈ X, ind (a ≠ c) = (X.card : ℤ) - ind (c ∈ X) := by
  rw [sum_ind_filter, Finset.filter_ne', card_erase_int]

theorem sum_ind_mem (X W : Finset ℕ) : ∑ a ∈ X, ind (a ∈ W) = (X.card : ℤ) - (X.filter (· ∉ W)).card := by
  rw [sum_ind_filter]
  have := Finset.card_filter_add_card_filter_not (s := X) (p := (· ∈ W))
  simp only [Finset.filter_mem_eq_inter] at this ⊢
  omega

theorem sum_ind_eq (X Z : Finset ℕ) : ∑ a ∈ X, ∑ c ∈ Z, ind (a = c) = ((X ∩ Z).card : ℤ) := by
  have h : ∀ a ∈ X, ∑ c ∈ Z, ind (a = c) = ind (a ∈ Z) := by
    intro a _
    unfold ind
    rw [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl h, sum_ind_filter, Finset.filter_mem_eq_inter]

theorem sum_ind_ne_and (X : Finset ℕ) (c : ℕ) (P : Prop) [Decidable P] :
    ∑ a ∈ X, ind (a ≠ c ∧ P) = ind P * ((X.card : ℤ) - ind (c ∈ X)) := by
  rw [Finset.sum_congr rfl fun a _ => ind_and (a ≠ c) P, ← Finset.sum_mul, sum_ind_ne, mul_comm]

/-- A filter by membership in `W ∩ (M \ y)` over a set not containing `y`. -/
theorem filter_inter_erase (S W M : Finset ℕ) {y : ℕ} (hy : y ∉ S) :
    S.filter (· ∈ W ∩ M.erase y) = S.filter (· ∈ W ∩ M) := by
  apply Finset.filter_congr
  intro a ha
  have : a ≠ y := fun h => hy (h ▸ ha)
  simp [Finset.mem_inter, Finset.mem_erase, this]

theorem filter_not_inter_erase (S W M : Finset ℕ) {y : ℕ} (hy : y ∉ S) :
    S.filter (· ∉ W ∩ M.erase y) = S.filter (· ∉ W ∩ M) := by
  apply Finset.filter_congr
  intro a ha
  have : a ≠ y := fun h => hy (h ▸ ha)
  simp [Finset.mem_inter, Finset.mem_erase, this]

/-! ### The eq-part, exactly -/

/-- The eq-successor count of `(a, y, c)`, exactly. -/
theorem eqSucc_exact (T M B : Finset ℕ) (y a c : ℕ) :
    (eqSucc T M B (a, y, c) : ℤ)
      = ((M.erase y).card : ℤ)
          * (((T ∩ B).card : ℤ) - ind (a ∈ T ∩ B) - ind (a ≠ c ∧ c ∈ T ∩ B))
        - (((T ∩ B ∩ M.erase y).card : ℤ) - ind (a ∈ T ∩ B ∩ M.erase y)
            - ind (a ≠ c ∧ c ∈ T ∩ B ∩ M.erase y)) := by
  rw [eqSucc_eq_sum, inter_erase_erase]
  push_cast
  rw [Finset.sum_congr rfl fun x _ => card_erase_int (M.erase y) x, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, sum_ind_filter, card_filter_mem_erase_erase,
    card_erase_erase_int]
  ring

/-- A double sum of a constant. -/
theorem sum_sum_const (X Z : Finset ℕ) (C : ℤ) :
    ∑ _a ∈ X, ∑ _c ∈ Z, C = (X.card : ℤ) * Z.card * C := by
  simp [Finset.sum_const]; ring

theorem sum_sum_ind_left (X Z W : Finset ℕ) :
    ∑ a ∈ X, ∑ _c ∈ Z, ind (a ∈ W) = (Z.card : ℤ) * ((X.card : ℤ) - (X.filter (· ∉ W)).card) := by
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [sum_ind_mem]

theorem sum_sum_ind_right (X Z W : Finset ℕ) :
    ∑ a ∈ X, ∑ c ∈ Z, ind (a ≠ c ∧ c ∈ W)
      = (X.card : ℤ) * ((Z.card : ℤ) - (Z.filter (· ∉ W)).card) - ((X ∩ Z).filter (· ∈ W)).card := by
  rw [Finset.sum_comm]
  simp only [sum_ind_ne_and]
  rw [Finset.sum_congr rfl fun c _ => show ind (c ∈ W) * ((X.card : ℤ) - ind (c ∈ X))
      = (X.card : ℤ) * ind (c ∈ W) - ind (c ∈ X ∧ c ∈ W) by rw [ind_and]; ring]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind_mem, sum_ind_filter]
  have hset : Z.filter (fun c => c ∈ X ∧ c ∈ W) = (X ∩ Z).filter (· ∈ W) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
  rw [hset]

/-- **The eq-part of `QC`, exactly.** -/
theorem RC_eq_RC4 {T M B : Finset ℕ} (hT : T.card = 4) (X Z : Finset ℕ) (y : ℕ) :
    RC 4 X Z T M B y = RC4 X Z T M B y := by
  unfold RC rC
  have hg : (gam 4 : ℤ) = 5 := by norm_num [gam]
  have hd : (del 4 : ℤ) = 2 := by norm_num [del]
  have hpt : ∀ a ∈ X.erase y, ∀ c ∈ Z.erase y,
      (eqSucc T M B (a, y, c) : ℤ) - gam 4 - del 4 * eqInd (a, y, c)
        = ((M.erase y).card : ℤ) * ((T ∩ B).card : ℤ)
          - ((M.erase y).card : ℤ) * ind (a ∈ T ∩ B)
          - ((M.erase y).card : ℤ) * ind (a ≠ c ∧ c ∈ T ∩ B)
          - ((T ∩ B ∩ M.erase y).card : ℤ) + ind (a ∈ T ∩ B ∩ M.erase y)
          + ind (a ≠ c ∧ c ∈ T ∩ B ∩ M.erase y) - 5 - 2 * ind (a = c) := by
    intro a _ c _
    rw [eqSucc_exact, hg, hd, eqInd_eq_ind]
    ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => hpt a ha c hc]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_sum_const, sum_sum_const, sum_sum_const, sum_sum_ind_left, sum_sum_ind_right,
    sum_sum_ind_left, sum_sum_ind_right, sum_ind_eq]
  -- the `M \ y` filters reduce to `M` filters over sets not containing `y`
  have hy1 : y ∉ X.erase y := Finset.notMem_erase y X
  have hy2 : y ∉ Z.erase y := Finset.notMem_erase y Z
  have hy3 : y ∉ (X.erase y) ∩ (Z.erase y) := fun h => hy1 (Finset.mem_inter.mp h).1
  rw [filter_not_inter_erase _ _ _ hy1, filter_not_inter_erase _ _ _ hy2,
    filter_inter_erase _ _ _ hy3]
  -- `|T ∩ B ∩ (M \ y)| = |M \ y| - |(M \ y) \ (T ∩ B)|` and `|T ∩ B| = 4 - ω`
  have hW : ((T ∩ B ∩ M.erase y).card : ℤ) = ((M.erase y).card : ℤ) - out M (T ∩ B) y := by
    unfold out
    have := Finset.card_filter_add_card_filter_not (s := M.erase y) (p := (· ∈ T ∩ B))
    rw [Finset.filter_mem_eq_inter, Finset.inter_comm] at this
    omega
  have hTB : ((T ∩ B).card : ℤ) = 4 - om T B := by
    unfold om
    have := Finset.card_filter_add_card_filter_not (s := T) (p := (· ∈ B))
    rw [Finset.filter_mem_eq_inter, hT] at this
    omega
  rw [hW, hTB]
  unfold RC4 pc out in2
  ring


/-! ### The `(H1)` part -/

/-- `∑_{a ∈ X'} |T \ {a, m}|`, exactly. -/
theorem sum_card_erase_erase {T : Finset ℕ} (hT : T.card = 4) (X' : Finset ℕ) (m : ℕ) :
    ∑ a ∈ X', (((T.erase a).erase m).card : ℤ)
      = 3 * X'.card + (X'.filter (· ∉ T)).card - X'.card * ind (m ∈ T)
        + ind (m ∈ T) * ind (m ∈ X') := by
  rw [Finset.sum_congr rfl fun a _ => card_erase_erase_int T a m, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, sum_ind_mem, sum_ind_ne_and, hT]
  push_cast
  ring

/-- The gain of the next middle colour `m` at the top: nonnegative. -/
def gain (X' T : Finset ℕ) (m : ℕ) : ℤ :=
  (X'.filter (· ∉ T)).card + ind (m ∉ T) * ((X'.card : ℤ) - ind (m ∈ X'))

theorem gain_nonneg (X' T : Finset ℕ) (m : ℕ) : 0 ≤ gain X' T m := by
  unfold gain
  have h1 : ind (m ∈ X') ≤ (X'.card : ℤ) := by
    unfold ind; split_ifs with h
    · exact_mod_cast Finset.card_pos.mpr ⟨m, h⟩
    · positivity
  have := ind_nonneg (m ∉ T)
  nlinarith [this, h1, (Nat.cast_nonneg ((X'.filter (· ∉ T)).card) : (0 : ℤ) ≤ _)]

theorem sum_card_erase_erase_eq_gain {T : Finset ℕ} (hT : T.card = 4) (X' : Finset ℕ) (m : ℕ) :
    ∑ a ∈ X', (((T.erase a).erase m).card : ℤ) = 2 * X'.card + ind (m ∈ X') + gain X' T m := by
  rw [sum_card_erase_erase hT, gain, ind_not]
  ring

/-- The product of the two sides, bounded below by dropping the cross terms. -/
theorem prod_ge (p r iX iZ g₁ g₂ : ℤ) (hiX : 0 ≤ iX) (hiZ : 0 ≤ iZ) (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) :
    (2 * p + iX) * (2 * r + iZ) + 2 * r * g₁ + 2 * p * g₂
      ≤ (2 * p + iX + g₁) * (2 * r + iZ + g₂) := by
  nlinarith [mul_nonneg hg₁ hiZ, mul_nonneg hg₂ hiX, mul_nonneg hg₁ hg₂]

/-- The sum of gains over the next middle list. -/
theorem sum_gain (X' T M' : Finset ℕ) :
    ∑ m ∈ M', gain X' T m
      = (M'.card : ℤ) * (X'.filter (· ∉ T)).card + (X'.card : ℤ) * (M'.filter (· ∉ T)).card
        - ((M'.filter (· ∉ T)).filter (· ∈ X')).card := by
  unfold gain
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h : ∀ m ∈ M', ind (m ∉ T) * ((X'.card : ℤ) - ind (m ∈ X'))
      = (X'.card : ℤ) * ind (m ∉ T) - ind (m ∉ T ∧ m ∈ X') := by
    intro m _; rw [ind_and]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind_filter,
    sum_ind_filter, Finset.filter_filter]
  ring

/-- The uniform part of the product sum. -/
theorem sum_uniform_prod (X' Z' M' : Finset ℕ) :
    ∑ m ∈ M', (2 * (X'.card : ℤ) + ind (m ∈ X')) * (2 * (Z'.card : ℤ) + ind (m ∈ Z'))
      = 4 * (X'.card : ℤ) * Z'.card * M'.card + 2 * (X'.card : ℤ) * (M'.filter (· ∈ Z')).card
        + 2 * (Z'.card : ℤ) * (M'.filter (· ∈ X')).card
        + ((M'.filter (· ∈ X')).filter (· ∈ Z')).card := by
  have h : ∀ m ∈ M', (2 * (X'.card : ℤ) + ind (m ∈ X')) * (2 * (Z'.card : ℤ) + ind (m ∈ Z'))
      = 4 * (X'.card : ℤ) * Z'.card + 2 * (X'.card : ℤ) * ind (m ∈ Z')
        + 2 * (Z'.card : ℤ) * ind (m ∈ X') + ind (m ∈ X' ∧ m ∈ Z') := by
    intro m _; rw [ind_and]; ring
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [sum_ind_filter, sum_ind_filter, sum_ind_filter, Finset.filter_filter]
  ring

/-- Membership in the punctured lists agrees with the unpunctured ones away from `y`. -/
theorem card_filter_mem_erase (M' X : Finset ℕ) {y : ℕ} (hy : y ∉ M') :
    (M'.filter (· ∈ X.erase y)).card = (M'.filter (· ∈ X)).card := by
  congr 1
  apply Finset.filter_congr
  intro m hm
  have : m ≠ y := fun h => hy (h ▸ hm)
  simp [Finset.mem_erase, this]

/-- `|M' ∩ X'| = |X'| - |X' \ M|` when `y ∉ X'`, `M' = M \ y`. -/
theorem card_filter_mem_comm (X' M : Finset ℕ) {y : ℕ} (hy : y ∉ X') :
    (((M.erase y).filter (· ∈ X')).card : ℤ) = X'.card - (X'.filter (· ∉ M)).card := by
  have h1 : (M.erase y).filter (· ∈ X') = X'.filter (· ∈ M) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hM⟩, hX⟩; exact ⟨hX, hM⟩
    · rintro ⟨hX, hM⟩; exact ⟨⟨fun h => hy (h ▸ hX), hM⟩, hX⟩
  rw [h1]
  have := Finset.card_filter_add_card_filter_not (s := X') (p := (· ∈ M))
  omega

/-- **The `(H1)` per-colour bound at `k = 4`.** -/
theorem betaH_le_QH {T M B : Finset ℕ} (hT : T.card = 4) (hB : B.card = 4) (X Z : Finset ℕ)
    (y : ℕ) : betaH X Z T M B y ≤ QH 4 X Z T M B y := by
  unfold QH dH
  have hene : (ene 4 : ℤ) = 16 := by norm_num [ene]
  -- the successor count, fibred over the next middle colour
  have hsucc : ∀ a ∈ X.erase y, ∀ c ∈ Z.erase y, (succ T M B (a, y, c) : ℤ)
      = ∑ m ∈ M.erase y, (((T.erase a).erase m).card : ℤ) * (((B.erase c).erase m).card : ℤ) := by
    intro a _ c _
    rw [succ_eq_sum]; push_cast; rfl
  have hpt : ∀ a ∈ X.erase y, ∀ c ∈ Z.erase y,
      (succ T M B (a, y, c) : ℤ) - ene 4 - eqInd (a, y, c)
        = (∑ m ∈ M.erase y, (((T.erase a).erase m).card : ℤ) * (((B.erase c).erase m).card : ℤ))
          - 16 - ind (a = c) := by
    intro a ha c hc
    rw [hsucc a ha c hc, hene, eqInd_eq_ind]
  have hrw : ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y,
        ((succ T M B (a, y, c) : ℤ) - ene 4 - eqInd (a, y, c))
      = ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y,
        ((∑ m ∈ M.erase y, (((T.erase a).erase m).card : ℤ) * (((B.erase c).erase m).card : ℤ))
          - 16 - ind (a = c)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro c hc
    exact hpt a ha c hc
  rw [hrw]
  simp only [Finset.sum_sub_distrib]
  rw [sum_sum_const, sum_ind_eq]
  -- exchange the sums: `∑_a ∑_c ∑_m f a m * g c m = ∑_m (∑_a f a m) (∑_c g c m)`
  have hex : ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, ∑ m ∈ M.erase y,
        (((T.erase a).erase m).card : ℤ) * (((B.erase c).erase m).card : ℤ)
      = ∑ m ∈ M.erase y, (∑ a ∈ X.erase y, (((T.erase a).erase m).card : ℤ))
          * (∑ c ∈ Z.erase y, (((B.erase c).erase m).card : ℤ)) := by
    have h1 : ∀ a ∈ X.erase y, ∑ c ∈ Z.erase y, ∑ m ∈ M.erase y,
          (((T.erase a).erase m).card : ℤ) * (((B.erase c).erase m).card : ℤ)
        = ∑ m ∈ M.erase y, ∑ c ∈ Z.erase y,
          (((T.erase a).erase m).card : ℤ) * (((B.erase c).erase m).card : ℤ) :=
      fun a _ => Finset.sum_comm
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul_sum]
  rw [hex]
  set X' := X.erase y with hX'
  set Z' := Z.erase y with hZ'
  set M' := M.erase y with hM'
  have hyX : y ∉ X' := Finset.notMem_erase y X
  have hyZ : y ∉ Z' := Finset.notMem_erase y Z
  have hyM : y ∉ M' := Finset.notMem_erase y M
  -- each product is at least the linearised one
  have hterm : ∀ m ∈ M',
      (2 * (X'.card : ℤ) + ind (m ∈ X')) * (2 * (Z'.card : ℤ) + ind (m ∈ Z'))
        + 2 * (Z'.card : ℤ) * gain X' T m + 2 * (X'.card : ℤ) * gain Z' B m
      ≤ (∑ a ∈ X', (((T.erase a).erase m).card : ℤ))
          * (∑ c ∈ Z', (((B.erase c).erase m).card : ℤ)) := by
    intro m _
    rw [sum_card_erase_erase_eq_gain hT, sum_card_erase_erase_eq_gain hB]
    exact prod_ge _ _ _ _ _ _ (ind_nonneg _) (ind_nonneg _) (gain_nonneg _ _ _) (gain_nonneg _ _ _)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_uniform_prod, sum_gain, sum_gain] at hsum
  -- rewrite the mixed cardinalities
  rw [card_filter_mem_comm X' M hyX, card_filter_mem_comm Z' M hyZ] at hsum
  have hXZ : (((M'.filter (· ∈ X')).filter (· ∈ Z')).card : ℤ)
      = ((X' ∩ Z').card : ℤ) - ((X' ∩ Z').filter (· ∉ M)).card := by
    rw [Finset.filter_filter]
    have h1 : M'.filter (fun m => m ∈ X' ∧ m ∈ Z') = (X' ∩ Z').filter (· ∈ M) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_inter, hM', Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hM⟩, hX, hZ⟩; exact ⟨⟨hX, hZ⟩, hM⟩
      · rintro ⟨⟨hX, hZ⟩, hM⟩; exact ⟨⟨fun h => hyX (h ▸ hX), hM⟩, hX, hZ⟩
    rw [h1]
    have := Finset.card_filter_add_card_filter_not (s := X' ∩ Z') (p := (· ∈ M))
    omega
  rw [hXZ] at hsum
  unfold betaH pc out out2 outIn
  rw [← hX', ← hZ', ← hM']
  linarith
