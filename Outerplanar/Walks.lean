/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Kernel
import Outerplanar.SixFamily

/-!
# Walks on three colours

After the lists along a path have been enumerated so that equal colours get equal indices, the
colourings of the path that use only good pairs are the walks on the triangle `Fin 3`: sequences
of indices with consecutive entries different. This file treats them for a list `Ms` of
`3 × 3` tables (one per edge, read at pairs of different indices), and proves the ball
inequalities of the whole path from those of the tables.

* `dN k`, `sN k` — the numbers of walks of length `k` between two different indices and from an
  index to itself; `cnt k a b` is the one that applies;
* `pw Ms a b` — the sum over the walks from `a` to `b` of the products of the table entries;
* `wgp Ms a b` — the product over those walks of the same products;
* `pw_ub` — the arithmetic–geometric mean inequality over the walks:
  `cnt ^ cnt * wgp ≤ pw ^ cnt`; `pw_ub_alt` — the same without the walk that alternates between
  two indices;
* `Og_eq`, `Dg_eq`, `alt_bal` — how often the walks of a family of cells use each pair;
* `OffBall M A` — the ball inequalities of one table; `offBall_prod` — their product along the
  path, with the largest entries losing weight and the smallest gaining it;
* **`walks_ball`** — for a path of `h + h` steps, `h ≥ 2`, and any bijection `σ` of the indices,
  the six cells `(a, σ b)`, `a ≠ b`, satisfy the ball inequalities with the constant
  `dN (h + h)` times the product of the constants of the tables.

The proof of `walks_ball` chooses walks in every cell so that every pair of different indices
is used equally often at every step. There are three cases.

* `σ` the identity (`walks_ball_id`): all walks of the six cells.
* `σ` a transposition (`walks_ball_tr`): all walks, except the alternating walk in each of the
  two closed cells of the family; these are exactly the walks that over-use the two exchanged
  pairs.
* `σ` a rotation (`walks_ball_rot1`, `walks_ball_rot2`): all walks of the three closed cells,
  which have one walk more than the constant, and in the other three cells the walks through a
  midpoint chosen uniformly among the three indices. The second choice loses a little
  (`walk_num`), the first gains more.

For a path with an odd number of steps (a face of even length) the closed cells have one walk
*fewer* than the constant, and the statement is false.

This is part of the formalization of the ball invariant, a result of this repository's 2026-11
AI research collaboration.
-/

namespace Outerplanar

open Finset

/-! ### Counting walks -/

/-- The numbers of walks of length `k` between different indices and from an index to itself. -/
def wN : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | (k + 1) => ((wN k).1 + (wN k).2, 2 * (wN k).1)

/-- The number of walks of length `k` between two different indices. -/
def dN (k : ℕ) : ℕ := (wN k).1

/-- The number of walks of length `k` from an index to itself. -/
def sN (k : ℕ) : ℕ := (wN k).2

theorem dN_zero : dN 0 = 0 := rfl

theorem sN_zero : sN 0 = 1 := rfl

theorem dN_succ (k : ℕ) : dN (k + 1) = dN k + sN k := rfl

theorem sN_succ (k : ℕ) : sN (k + 1) = 2 * dN k := rfl

theorem dN_add_two (k : ℕ) : dN (k + 2) = dN (k + 1) + 2 * dN k := by
  rw [dN_succ (k + 1), sN_succ]

theorem sN_dN_parity : ∀ k, (Even k → sN k = dN k + 1) ∧ (Odd k → dN k = sN k + 1)
  | 0 => ⟨fun _ => rfl, fun h => absurd h (by decide)⟩
  | (k + 1) => by
    obtain ⟨he, ho⟩ := sN_dN_parity k
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hk : Odd k := by
        rcases Nat.even_or_odd k with h' | h'
        · exact absurd h (by simpa [Nat.even_add_one] using h')
        · exact h'
      have := ho hk
      rw [sN_succ, dN_succ]
      omega
    · have hk : Even k := by
        rcases Nat.even_or_odd k with h' | h'
        · exact h'
        · exact absurd h (by simpa [Nat.odd_add_one] using h')
      have := he hk
      rw [sN_succ, dN_succ]
      omega

theorem two_pow_eq (k : ℕ) : 2 ^ k = 2 * dN k + sN k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, dN_succ, sN_succ]; ring

/-- The number of walks of length `k` from `a` to `b`. -/
def cnt (k : ℕ) (a b : Fin 3) : ℕ := if a = b then sN k else dN k

theorem cnt_succ (k : ℕ) (a b : Fin 3) :
    cnt (k + 1) a b = cnt k (a + 1) b + cnt k (a + 2) b := by
  fin_cases a <;> fin_cases b <;> simp [cnt, dN_succ, sN_succ] <;> omega

/-! ### Sums and products over walks -/

/-- The sum over the walks from `a` to `b` of the product of the table entries along the walk. -/
noncomputable def pw : List (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ
  | [], a, b => if a = b then 1 else 0
  | M :: Ms, a, b => M a (a + 1) * pw Ms (a + 1) b + M a (a + 2) * pw Ms (a + 2) b

/-- The product over the walks from `a` to `b` of the product of the table entries along the
walk. -/
noncomputable def wgp : List (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ
  | [], _, _ => 1
  | M :: Ms, a, b => M a (a + 1) ^ cnt Ms.length (a + 1) b * wgp Ms (a + 1) b
      * (M a (a + 2) ^ cnt Ms.length (a + 2) b * wgp Ms (a + 2) b)

theorem pw_nonneg : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a b, 0 ≤ pw Ms a b
  | [], _, a, b => by
    rw [pw]
    split_ifs <;> norm_num
  | M :: Ms, h, a, b => by
    have ih := pw_nonneg Ms fun M' hM' => h M' (List.mem_cons_of_mem _ hM')
    have hM := h M List.mem_cons_self
    rw [pw]
    exact add_nonneg (mul_nonneg (hM _ _) (ih _ _)) (mul_nonneg (hM _ _) (ih _ _))

theorem wgp_nonneg : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a b, 0 ≤ wgp Ms a b
  | [], _, a, b => by rw [wgp]; exact zero_le_one
  | M :: Ms, h, a, b => by
    have ih := wgp_nonneg Ms fun M' hM' => h M' (List.mem_cons_of_mem _ hM')
    have hM := h M List.mem_cons_self
    rw [wgp]
    exact mul_nonneg (mul_nonneg (pow_nonneg (hM _ _) _) (ih _ _))
      (mul_nonneg (pow_nonneg (hM _ _) _) (ih _ _))

theorem pow_self_pos (p : ℕ) : (0 : ℝ) < (p : ℝ) ^ p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · exact pow_pos (by exact_mod_cast hp) _

/-- Weighted AM–GM for two terms, cleared of denominators. -/
theorem amgm2 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (p q : ℕ) :
    ((p + q : ℕ) : ℝ) ^ (p + q) * (x ^ p * y ^ q)
      ≤ (p : ℝ) ^ p * (q : ℝ) ^ q * (x + y) ^ (p + q) := by
  have h := amgm_real (univ : Finset (Fin 2)) ![x, y] ![p, q]
    (by intro i _; fin_cases i <;> simp [hx, hy])
  simpa [Fin.sum_univ_two, Fin.prod_univ_two] using h

/-- **AM–GM over the walks.** -/
theorem pw_ub : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a b, ((cnt Ms.length a b : ℕ) : ℝ) ^ cnt Ms.length a b * wgp Ms a b
      ≤ pw Ms a b ^ cnt Ms.length a b
  | [], _, a, b => by
    by_cases hab : a = b
    · simp [cnt, sN_zero, pw, wgp, hab]
    · simp [cnt, dN_zero, pw, wgp, hab]
  | M :: Ms, h, a, b => by
    have hMs : ∀ M' ∈ Ms, ∀ a b, 0 ≤ M' a b := fun M' hM' => h M' (List.mem_cons_of_mem _ hM')
    have hM := h M List.mem_cons_self
    have ih1 := pw_ub Ms hMs (a + 1) b
    have ih2 := pw_ub Ms hMs (a + 2) b
    have hp1 := pw_nonneg Ms hMs (a + 1) b
    have hp2 := pw_nonneg Ms hMs (a + 2) b
    have hg1 := wgp_nonneg Ms hMs (a + 1) b
    have hg2 := wgp_nonneg Ms hMs (a + 2) b
    set p := cnt Ms.length (a + 1) b with hp
    set q := cnt Ms.length (a + 2) b with hq
    have hcnt : cnt (M :: Ms).length a b = p + q := cnt_succ _ a b
    have key := amgm2 (mul_nonneg (hM a (a + 1)) hp1) (mul_nonneg (hM a (a + 2)) hp2) p q
    rw [hcnt]
    show ((p + q : ℕ) : ℝ) ^ (p + q) * (M a (a + 1) ^ p * wgp Ms (a + 1) b
        * (M a (a + 2) ^ q * wgp Ms (a + 2) b))
      ≤ (M a (a + 1) * pw Ms (a + 1) b + M a (a + 2) * pw Ms (a + 2) b) ^ (p + q)
    have hpp := pow_self_pos p
    have hqq := pow_self_pos q
    have h1 : M a (a + 1) ^ p * ((p : ℝ) ^ p * wgp Ms (a + 1) b)
        ≤ (M a (a + 1) * pw Ms (a + 1) b) ^ p := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left ih1 (pow_nonneg (hM _ _) _)
    have h2 : M a (a + 2) ^ q * ((q : ℝ) ^ q * wgp Ms (a + 2) b)
        ≤ (M a (a + 2) * pw Ms (a + 2) b) ^ q := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left ih2 (pow_nonneg (hM _ _) _)
    have h12 := mul_le_mul h1 h2
      (mul_nonneg (pow_nonneg (hM _ _) _) (mul_nonneg hqq.le hg2))
      (pow_nonneg (mul_nonneg (hM _ _) hp1) _)
    have hN : (0 : ℝ) ≤ ((p + q : ℕ) : ℝ) ^ (p + q) := (pow_self_pos _).le
    have h3 := (mul_le_mul_of_nonneg_left h12 hN).trans key
    have hpq : (0 : ℝ) < (p : ℝ) ^ p * (q : ℝ) ^ q := mul_pos hpp hqq
    refine le_of_mul_le_mul_left ?_ hpq
    calc (p : ℝ) ^ p * (q : ℝ) ^ q * (((p + q : ℕ) : ℝ) ^ (p + q)
          * (M a (a + 1) ^ p * wgp Ms (a + 1) b * (M a (a + 2) ^ q * wgp Ms (a + 2) b)))
        = ((p + q : ℕ) : ℝ) ^ (p + q) * (M a (a + 1) ^ p * ((p : ℝ) ^ p * wgp Ms (a + 1) b)
          * (M a (a + 2) ^ q * ((q : ℝ) ^ q * wgp Ms (a + 2) b))) := by ring
      _ ≤ _ := h3

/-! ### Bounds by the smallest and the largest entry -/

/-- The smallest entry of a table at pairs of different indices. -/
noncomputable def mn (M : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (univ : Finset (Fin 6)).inf' univ_nonempty fun k => M (offPair k).1 (offPair k).2

/-- The largest entry of a table at pairs of different indices. -/
noncomputable def mx (M : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (univ : Finset (Fin 6)).sup' univ_nonempty fun k => M (offPair k).1 (offPair k).2

theorem mn_le (M : Fin 3 → Fin 3 → ℝ) {a b : Fin 3} (hab : a ≠ b) : mn M ≤ M a b := by
  obtain ⟨k, hk⟩ := offPair_surj a b hab
  have := Finset.inf'_le (fun k => M (offPair k).1 (offPair k).2) (mem_univ k)
  rwa [hk] at this

theorem le_mx (M : Fin 3 → Fin 3 → ℝ) {a b : Fin 3} (hab : a ≠ b) : M a b ≤ mx M := by
  obtain ⟨k, hk⟩ := offPair_surj a b hab
  have := Finset.le_sup' (fun k => M (offPair k).1 (offPair k).2) (mem_univ k)
  rwa [hk] at this

theorem mn_nonneg {M : Fin 3 → Fin 3 → ℝ} (hM : ∀ a b, 0 ≤ M a b) : 0 ≤ mn M :=
  (Finset.le_inf'_iff _ _).mpr fun _ _ => hM _ _

theorem mx_nonneg {M : Fin 3 → Fin 3 → ℝ} (hM : ∀ a b, 0 ≤ M a b) : 0 ≤ mx M :=
  (hM 0 1).trans (le_mx M (by decide))

/-- The products of the smallest and of the largest entries along the path. -/
noncomputable def mnP (Ms : List (Fin 3 → Fin 3 → ℝ)) : ℝ := (Ms.map mn).prod

noncomputable def mxP (Ms : List (Fin 3 → Fin 3 → ℝ)) : ℝ := (Ms.map mx).prod

theorem mnP_cons (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ)) :
    mnP (M :: Ms) = mn M * mnP Ms := by simp [mnP]

theorem mxP_cons (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ)) :
    mxP (M :: Ms) = mx M * mxP Ms := by simp [mxP]

theorem mnP_nonneg : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    0 ≤ mnP Ms
  | [], _ => by simp [mnP]
  | M :: Ms, h => by
    rw [mnP_cons]
    exact mul_nonneg (mn_nonneg (h M List.mem_cons_self))
      (mnP_nonneg Ms fun M' hM' => h M' (List.mem_cons_of_mem _ hM'))

theorem mxP_nonneg : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    0 ≤ mxP Ms
  | [], _ => by simp [mxP]
  | M :: Ms, h => by
    rw [mxP_cons]
    exact mul_nonneg (mx_nonneg (h M List.mem_cons_self))
      (mxP_nonneg Ms fun M' hM' => h M' (List.mem_cons_of_mem _ hM'))

theorem add_one_ne (a : Fin 3) : a ≠ a + 1 := by fin_cases a <;> decide

theorem add_two_ne (a : Fin 3) : a ≠ a + 2 := by fin_cases a <;> decide

/-- Every walk weighs at least the product of the smallest entries. -/
theorem pw_ge : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a b, (cnt Ms.length a b : ℝ) * mnP Ms ≤ pw Ms a b
  | [], _, a, b => by
    by_cases hab : a = b
    · simp [cnt, sN_zero, pw, mnP, hab]
    · simp [cnt, dN_zero, pw, mnP, hab]
  | M :: Ms, h, a, b => by
    have hMs : ∀ M' ∈ Ms, ∀ a b, 0 ≤ M' a b := fun M' hM' => h M' (List.mem_cons_of_mem _ hM')
    have hM := h M List.mem_cons_self
    have ih1 := pw_ge Ms hMs (a + 1) b
    have ih2 := pw_ge Ms hMs (a + 2) b
    have h0 := mn_nonneg hM
    have hP := mnP_nonneg Ms hMs
    have e : cnt (M :: Ms).length a b = cnt Ms.length (a + 1) b + cnt Ms.length (a + 2) b :=
      cnt_succ _ a b
    rw [e, mnP_cons, pw]
    push_cast
    have h1 : mn M * ((cnt Ms.length (a + 1) b : ℝ) * mnP Ms) ≤ M a (a + 1) * pw Ms (a + 1) b :=
      mul_le_mul (mn_le M (add_one_ne a)) ih1 (mul_nonneg (Nat.cast_nonneg _) hP) (hM _ _)
    have h2 : mn M * ((cnt Ms.length (a + 2) b : ℝ) * mnP Ms) ≤ M a (a + 2) * pw Ms (a + 2) b :=
      mul_le_mul (mn_le M (add_two_ne a)) ih2 (mul_nonneg (Nat.cast_nonneg _) hP) (hM _ _)
    linarith

/-- Every walk weighs at most the product of the largest entries. -/
theorem pw_le : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a b, pw Ms a b ≤ (cnt Ms.length a b : ℝ) * mxP Ms
  | [], _, a, b => by
    by_cases hab : a = b
    · simp [cnt, sN_zero, pw, mxP, hab]
    · simp [cnt, dN_zero, pw, mxP, hab]
  | M :: Ms, h, a, b => by
    have hMs : ∀ M' ∈ Ms, ∀ a b, 0 ≤ M' a b := fun M' hM' => h M' (List.mem_cons_of_mem _ hM')
    have hM := h M List.mem_cons_self
    have ih1 := pw_le Ms hMs (a + 1) b
    have ih2 := pw_le Ms hMs (a + 2) b
    have h0 := mx_nonneg hM
    have hP := mxP_nonneg Ms hMs
    have e : cnt (M :: Ms).length a b = cnt Ms.length (a + 1) b + cnt Ms.length (a + 2) b :=
      cnt_succ _ a b
    rw [e, mxP_cons, pw]
    push_cast
    have h1 : M a (a + 1) * pw Ms (a + 1) b ≤ mx M * ((cnt Ms.length (a + 1) b : ℝ) * mxP Ms) :=
      mul_le_mul (le_mx M (add_one_ne a)) ih1 (pw_nonneg Ms hMs _ _) h0
    have h2 : M a (a + 2) * pw Ms (a + 2) b ≤ mx M * ((cnt Ms.length (a + 2) b : ℝ) * mxP Ms) :=
      mul_le_mul (le_mx M (add_two_ne a)) ih2 (pw_nonneg Ms hMs _ _) h0
    linarith

theorem wgp_le : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a b, wgp Ms a b ≤ mxP Ms ^ cnt Ms.length a b
  | [], _, a, b => by simp [wgp, mxP]
  | M :: Ms, h, a, b => by
    have hMs : ∀ M' ∈ Ms, ∀ a b, 0 ≤ M' a b := fun M' hM' => h M' (List.mem_cons_of_mem _ hM')
    have hM := h M List.mem_cons_self
    have ih1 := wgp_le Ms hMs (a + 1) b
    have ih2 := wgp_le Ms hMs (a + 2) b
    have h0 := mx_nonneg hM
    have hP := mxP_nonneg Ms hMs
    have e : cnt (M :: Ms).length a b = cnt Ms.length (a + 1) b + cnt Ms.length (a + 2) b :=
      cnt_succ _ a b
    rw [e, mxP_cons, wgp, pow_add, mul_pow, mul_pow]
    have h1 : M a (a + 1) ^ cnt Ms.length (a + 1) b * wgp Ms (a + 1) b
        ≤ mx M ^ cnt Ms.length (a + 1) b * mxP Ms ^ cnt Ms.length (a + 1) b :=
      mul_le_mul (pow_le_pow_left₀ (hM _ _) (le_mx M (add_one_ne a)) _) ih1
        (wgp_nonneg Ms hMs _ _) (pow_nonneg h0 _)
    have h2 : M a (a + 2) ^ cnt Ms.length (a + 2) b * wgp Ms (a + 2) b
        ≤ mx M ^ cnt Ms.length (a + 2) b * mxP Ms ^ cnt Ms.length (a + 2) b :=
      mul_le_mul (pow_le_pow_left₀ (hM _ _) (le_mx M (add_two_ne a)) _) ih2
        (wgp_nonneg Ms hMs _ _) (pow_nonneg h0 _)
    exact mul_le_mul h1 h2 (mul_nonneg (pow_nonneg (hM _ _) _) (wgp_nonneg Ms hMs _ _))
      (mul_nonneg (pow_nonneg h0 _) (pow_nonneg hP _))

/-! ### Every pair is used equally often -/

/-- The product of the entries of a table at the six pairs of different indices. -/
noncomputable def u (M : Fin 3 → Fin 3 → ℝ) : ℝ := ∏ k : Fin 6, M (offPair k).1 (offPair k).2

/-- The product along the path of the `e`-th powers of these products. -/
noncomputable def up : List (Fin 3 → Fin 3 → ℝ) → ℕ → ℝ
  | [], _ => 1
  | M :: Ms, e => u M ^ e * up Ms e

theorem up_cons (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ)) (e : ℕ) :
    up (M :: Ms) e = u M ^ e * up Ms e := rfl

theorem up_add : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)) (e e' : ℕ), up Ms (e + e') = up Ms e * up Ms e'
  | [], _, _ => by simp [up]
  | M :: Ms, e, e' => by rw [up, up, up, up_add Ms, pow_add]; ring

theorem up_mul : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)) (e f : ℕ), up Ms (e * f) = up Ms e ^ f
  | [], _, _ => by simp [up]
  | M :: Ms, e, f => by rw [up, up, up_mul Ms, pow_mul, mul_pow]

/-- The product of `wgp` over the three closed cells. -/
noncomputable def Dg (Ms : List (Fin 3 → Fin 3 → ℝ)) : ℝ := wgp Ms 0 0 * wgp Ms 1 1 * wgp Ms 2 2

/-- The product of `wgp` over the six cells with different ends. -/
noncomputable def Og (Ms : List (Fin 3 → Fin 3 → ℝ)) : ℝ :=
  ∏ k : Fin 6, wgp Ms (offPair k).1 (offPair k).2

theorem Dg_cons (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ)) :
    Dg (M :: Ms) = u M ^ dN Ms.length * Og Ms := by
  simp [Dg, Og, u, wgp, cnt, Fin.prod_univ_six, offPair]
  ring

theorem Og_cons (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ)) :
    Og (M :: Ms) = u M ^ dN (Ms.length + 1) * Dg Ms ^ 2 * Og Ms := by
  simp [Dg, Og, u, wgp, cnt, Fin.prod_univ_six, offPair, dN_succ, pow_add]
  ring

theorem Og_Dg_eq : ∀ Ms : List (Fin 3 → Fin 3 → ℝ),
    Og Ms = up Ms (dN Ms.length) ∧
      Dg Ms ^ 2 * up Ms (dN Ms.length) = up Ms (dN (Ms.length + 1))
  | [] => by simp [Og, Dg, up, wgp]
  | M :: Ms => by
    obtain ⟨ih1, ih2⟩ := Og_Dg_eq Ms
    have hO : Og (M :: Ms) = up (M :: Ms) (dN (Ms.length + 1)) := by
      rw [Og_cons, up_cons, mul_assoc, ih1, ih2]
    refine ⟨hO, ?_⟩
    have e2 : up Ms (2 * dN Ms.length) = up Ms (dN Ms.length) ^ 2 := by
      rw [mul_comm, up_mul]
    show Dg (M :: Ms) ^ 2 * up (M :: Ms) (dN (Ms.length + 1)) = up (M :: Ms) (dN (Ms.length + 2))
    rw [Dg_cons, ih1, dN_add_two, up_cons, up_cons, up_add, e2]
    ring

/-- The walks between different indices use every pair of different indices `dN k` times. -/
theorem Og_eq (Ms : List (Fin 3 → Fin 3 → ℝ)) : Og Ms = up Ms (dN Ms.length) := (Og_Dg_eq Ms).1

/-- The closed walks of length `k + 1` use every pair of different indices `dN k` times. -/
theorem Dg_eq (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ)) :
    Dg (M :: Ms) = up (M :: Ms) (dN Ms.length) := by
  rw [Dg_cons, Og_eq, up_cons]

/-! ### The ball inequalities of the tables -/

/-- The ball inequalities of one table for the six pairs of different indices, weight being
moved to a pair of different indices. -/
def OffBall (M : Fin 3 → Fin 3 → ℝ) (A : ℝ) : Prop :=
  ∀ j : Fin 6, ∀ c d : Fin 3, c ≠ d →
    A ^ 600 ≤ (∏ k ∈ univ.erase j, M (offPair k).1 (offPair k).2) ^ 100
      * M (offPair j).1 (offPair j).2 ^ 91 * M c d ^ 9

theorem OffBall.mx_pos {M : Fin 3 → Fin 3 → ℝ} {A : ℝ} (hA : 0 < A) (hM : ∀ a b, 0 ≤ M a b)
    (h : OffBall M A) : 0 < mx M := by
  have h0 := h 0 0 1 (by decide)
  have hpos : 0 < M 0 1 := by
    rcases (hM 0 1).eq_or_lt with h' | h'
    · rw [← h'] at h0
      have : (0 : ℝ) < A ^ 600 := pow_pos hA _
      norm_num at h0
      linarith
    · exact h'
  exact hpos.trans_le (le_mx M (by decide))

/-- The inequality with the largest entry losing weight and the smallest gaining it. -/
theorem OffBall.minmax {M : Fin 3 → Fin 3 → ℝ} {A : ℝ} (hM : ∀ a b, 0 ≤ M a b)
    (h : OffBall M A) : A ^ 600 * mx M ^ 9 ≤ u M ^ 100 * mn M ^ 9 := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 6))
    fun k => M (offPair k).1 (offPair k).2
  obtain ⟨k', -, hk'⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := Fin 6))
    fun k => M (offPair k).1 (offPair k).2
  have h0 := h j (offPair k').1 (offPair k').2 (offPair_ne k')
  have hmx : mx M = M (offPair j).1 (offPair j).2 := hj
  have hmn : mn M = M (offPair k').1 (offPair k').2 := hk'
  rw [← hmx, ← hmn] at h0
  have hu : u M = mx M * ∏ k ∈ univ.erase j, M (offPair k).1 (offPair k).2 := by
    rw [hmx]
    exact (Finset.mul_prod_erase univ (fun k => M (offPair k).1 (offPair k).2) (mem_univ j)).symm
  have hx := mx_nonneg hM
  calc A ^ 600 * mx M ^ 9
      ≤ ((∏ k ∈ univ.erase j, M (offPair k).1 (offPair k).2) ^ 100 * mx M ^ 91 * mn M ^ 9)
        * mx M ^ 9 := mul_le_mul_of_nonneg_right h0 (pow_nonneg hx _)
    _ = u M ^ 100 * mn M ^ 9 := by rw [hu]; ring

/-- The product of the inequalities along the path. -/
theorem offBall_prod : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ),
    (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) → (∀ A ∈ As, 0 < A) → List.Forall₂ OffBall Ms As →
    As.prod ^ 600 * mxP Ms ^ 9 ≤ up Ms 100 * mnP Ms ^ 9 ∧ 0 < mxP Ms
  | [], [], _, _, _ => by simp [mxP, mnP, up]
  | M :: Ms, A :: As, hM, hA, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    have hMs : ∀ M' ∈ Ms, ∀ a b, 0 ≤ M' a b := fun M' hM' => hM M' (List.mem_cons_of_mem _ hM')
    have hM0 := hM M List.mem_cons_self
    have hA0 := hA A List.mem_cons_self
    obtain ⟨ih, ihpos⟩ := offBall_prod Ms As hMs (fun A' hA' => hA A' (List.mem_cons_of_mem _ hA')) h2
    have hmm := h1.minmax hM0
    have hpos := h1.mx_pos hA0 hM0
    refine ⟨?_, by rw [mxP_cons]; exact mul_pos hpos ihpos⟩
    rw [List.prod_cons, mxP_cons, mnP_cons, up_cons]
    calc (A * As.prod) ^ 600 * (mx M * mxP Ms) ^ 9
        = (A ^ 600 * mx M ^ 9) * (As.prod ^ 600 * mxP Ms ^ 9) := by ring
      _ ≤ (u M ^ 100 * mn M ^ 9) * (up Ms 100 * mnP Ms ^ 9) :=
          mul_le_mul hmm ih (mul_nonneg (pow_nonneg (List.prod_nonneg fun A' hA' =>
            (hA A' (List.mem_cons_of_mem _ hA')).le) _) (pow_nonneg ihpos.le _))
            (mul_nonneg (pow_nonneg (prod_nonneg fun k _ => hM0 _ _) _)
              (pow_nonneg (mn_nonneg hM0) _))
      _ = _ := by ring

/-! ### Assembling the inequality of the face -/

/-- **Assembly for a uniform choice of `α` walks in each cell.** `p k` are the six entries of the
face on the root family, `Γ k` the products over the chosen walks, `pmv` the entry that receives
weight. -/
theorem sel_assembly {α : ℕ} (hα : 0 < α) {p Γ : Fin 6 → ℝ} {pmv AP Uα U100 mnp mxp : ℝ}
    (hp : ∀ k, 0 ≤ p k) (hΓ : ∀ k, 0 ≤ Γ k) (hub : ∀ k, (α : ℝ) ^ α * Γ k ≤ p k ^ α)
    (hbal : ∏ k, Γ k = Uα) (hΓle : ∀ k, Γ k ≤ mxp ^ α) (hmv : (α : ℝ) * mnp ≤ pmv)
    (hchild : AP ^ 600 * mxp ^ 9 ≤ U100 * mnp ^ 9) (hU : Uα ^ 100 = U100 ^ α)
    (hmxp : 0 < mxp) (hmnp : 0 ≤ mnp) (hAP : 0 ≤ AP) (j : Fin 6) :
    ((α : ℝ) * AP) ^ 600 ≤ (∏ k ∈ univ.erase j, p k) ^ 100 * p j ^ 91 * pmv ^ 9 := by
  have hαr : (0 : ℝ) < α := by exact_mod_cast hα
  set G' := ∏ k ∈ univ.erase j, Γ k with hG'
  have hG'0 : 0 ≤ G' := prod_nonneg fun k _ => hΓ k
  have hsplit : Γ j * G' = Uα := by
    rw [← hbal]
    exact Finset.mul_prod_erase univ Γ (mem_univ j)
  have hpmv : 0 ≤ pmv := (mul_nonneg hαr.le hmnp).trans hmv
  -- the children
  have h1 : AP ^ (600 * α) * mxp ^ (9 * α) ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * α) * mxp ^ (9 * α) :=
    calc AP ^ (600 * α) * mxp ^ (9 * α) = (AP ^ 600 * mxp ^ 9) ^ α := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ (U100 * mnp ^ 9) ^ α :=
          pow_le_pow_left₀ (mul_nonneg (pow_nonneg hAP _) (pow_nonneg hmxp.le _)) hchild α
      _ = Uα ^ 100 * mnp ^ (9 * α) := by rw [mul_pow, ← hU, ← pow_mul]
      _ = G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * α) * Γ j ^ 9 := by rw [← hsplit]; ring
      _ ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * α) * mxp ^ (9 * α) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (pow_nonneg hG'0 _)
            (pow_nonneg (hΓ j) _)) (pow_nonneg hmnp _))
          calc Γ j ^ 9 ≤ (mxp ^ α) ^ 9 := pow_le_pow_left₀ (hΓ j) (hΓle j) 9
            _ = mxp ^ (9 * α) := by rw [← pow_mul, mul_comm]
  have h2 : AP ^ (600 * α) ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * α) :=
    le_of_mul_le_mul_right h1 (pow_pos hmxp _)
  -- the cells
  have h3 : (α : ℝ) ^ (5 * α) * G' ≤ (∏ k ∈ univ.erase j, p k) ^ α := by
    rw [← Finset.prod_pow]
    have hc : (univ.erase j : Finset (Fin 6)).card = 5 := by
      rw [Finset.card_erase_of_mem (mem_univ j), Finset.card_univ, Fintype.card_fin]
    calc (α : ℝ) ^ (5 * α) * G' = ∏ k ∈ univ.erase j, (α : ℝ) ^ α * Γ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hc, ← pow_mul, mul_comm α 5]
      _ ≤ _ := Finset.prod_le_prod₀ (fun k _ => mul_nonneg (pow_nonneg hαr.le _) (hΓ k))
          fun k _ => hub k
  have h4 : ((α : ℝ) * mnp) ^ α ≤ pmv ^ α := pow_le_pow_left₀ (mul_nonneg hαr.le hmnp) hmv α
  have hX : (((α : ℝ) * AP) ^ 600) ^ α
      ≤ ((∏ k ∈ univ.erase j, p k) ^ 100 * p j ^ 91 * pmv ^ 9) ^ α :=
    calc (((α : ℝ) * AP) ^ 600) ^ α = (α : ℝ) ^ (600 * α) * AP ^ (600 * α) := by
          rw [← pow_mul, mul_pow]
      _ ≤ (α : ℝ) ^ (600 * α) * (G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * α)) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hαr.le _)
      _ = ((α : ℝ) ^ (5 * α) * G') ^ 100 * ((α : ℝ) ^ α * Γ j) ^ 91 * (((α : ℝ) * mnp) ^ α) ^ 9 := by
          ring
      _ ≤ ((∏ k ∈ univ.erase j, p k) ^ α) ^ 100 * (p j ^ α) ^ 91 * (pmv ^ α) ^ 9 := by
          refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hαr.le _) hG'0)
            h3 _) (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hαr.le _) (hΓ j)) (hub j) _)
            (pow_nonneg (mul_nonneg (pow_nonneg hαr.le _) (hΓ j)) _)
            (pow_nonneg (pow_nonneg (prod_nonneg fun k _ => hp k) _) _))
            (pow_le_pow_left₀ (pow_nonneg (mul_nonneg hαr.le hmnp) _) h4 _)
            (pow_nonneg (pow_nonneg (mul_nonneg hαr.le hmnp) _) _)
            (mul_nonneg (pow_nonneg (pow_nonneg (prod_nonneg fun k _ => hp k) _) _)
              (pow_nonneg (pow_nonneg (hp j) _) _))
      _ = _ := by ring
  exact le_of_pow_le_pow_left₀ hα.ne' (mul_nonneg (mul_nonneg (pow_nonneg
    (prod_nonneg fun k _ => hp k) _) (pow_nonneg (hp j) _)) (pow_nonneg hpmv _)) hX

/-! ### More on the numbers of walks -/

theorem dN_pos : ∀ k, 0 < dN (k + 1)
  | 0 => by decide
  | (k + 1) => by
    have := dN_pos k
    rw [dN_succ]
    omega

theorem dN_sN_add (i : ℕ) : ∀ j, dN (i + j) = sN i * dN j + dN i * sN j + dN i * dN j ∧
    sN (i + j) = sN i * sN j + 2 * (dN i * dN j)
  | 0 => by simp [dN_zero, sN_zero]
  | (j + 1) => by
    obtain ⟨h1, h2⟩ := dN_sN_add i j
    refine ⟨?_, ?_⟩
    · rw [← add_assoc, dN_succ, h1, h2, dN_succ, sN_succ]
      ring
    · rw [← add_assoc, sN_succ, h1, dN_succ, sN_succ]
      ring

theorem cnt_ge (k : ℕ) (hk : Even k) (a b : Fin 3) : dN k ≤ cnt k a b := by
  unfold cnt
  split_ifs
  · have := (sN_dN_parity k).1 hk
    omega
  · exact le_rfl

theorem cnt_le (k : ℕ) (hk : Even k) (a b : Fin 3) : cnt k a b ≤ sN k := by
  unfold cnt
  split_ifs
  · exact le_rfl
  · have := (sN_dN_parity k).1 hk
    omega

/-! ### The untwisted family -/

/-- **The ball inequality of the path for the untwisted family**: the six cells with different
ends, an even number of steps. -/
theorem walks_ball_id (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (hlen : Even Ms.length)
    (hpos : 0 < Ms.length) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) (j : Fin 6) (c d : Fin 3) :
    ((dN Ms.length : ℝ) * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (offPair k).2) ^ 100
        * pw Ms (offPair j).1 (offPair j).2 ^ 91 * pw Ms c d ^ 9 := by
  obtain ⟨hchild, hmxp⟩ := offBall_prod Ms As hM hA hball
  have hα : 0 < dN Ms.length := by
    obtain ⟨k, hk⟩ : ∃ k, Ms.length = k + 1 := ⟨Ms.length - 1, by omega⟩
    rw [hk]
    exact dN_pos k
  have hc : ∀ k : Fin 6, cnt Ms.length (offPair k).1 (offPair k).2 = dN Ms.length := fun k => by
    simp [cnt, offPair_ne k]
  refine sel_assembly hα (p := fun k => pw Ms (offPair k).1 (offPair k).2)
    (Γ := fun k => wgp Ms (offPair k).1 (offPair k).2) (Uα := up Ms (dN Ms.length))
    (U100 := up Ms 100) (mnp := mnP Ms) (mxp := mxP Ms)
    (fun k => pw_nonneg Ms hM _ _) (fun k => wgp_nonneg Ms hM _ _) (fun k => ?_) (Og_eq Ms)
    (fun k => ?_) ?_ hchild ?_ hmxp (mnP_nonneg Ms hM)
    (List.prod_nonneg fun A hA' => (hA A hA').le) j
  · have := pw_ub Ms hM (offPair k).1 (offPair k).2
    rwa [hc k] at this
  · have := wgp_le Ms hM (offPair k).1 (offPair k).2
    rwa [hc k] at this
  · refine le_trans ?_ (pw_ge Ms hM c d)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast cnt_ge _ hlen c d) (mnP_nonneg Ms hM)
  · rw [← up_mul, ← up_mul, mul_comm]

/-! ### A cruder assembly, for families with room to spare -/

theorem crude_assembly {p : Fin 6 → ℝ} (hp : ∀ k, 0 ≤ p k) {K pmv : ℝ}
    (hpos : 0 < ∏ k, p k) (h : ∀ j, K * p j ^ 9 ≤ (∏ k, p k) ^ 100 * pmv ^ 9) (j : Fin 6) :
    K ≤ (∏ k ∈ univ.erase j, p k) ^ 100 * p j ^ 91 * pmv ^ 9 := by
  have hj : 0 < p j := by
    rcases (hp j).eq_or_lt with h0 | h0
    · exact absurd (Finset.prod_eq_zero (mem_univ j) h0.symm) hpos.ne'
    · exact h0
  have hsplit : ∏ k, p k = p j * ∏ k ∈ univ.erase j, p k :=
    (Finset.mul_prod_erase univ p (mem_univ j)).symm
  have h1 := h j
  rw [hsplit] at h1
  refine le_of_mul_le_mul_right ?_ (pow_pos hj 9)
  calc K * p j ^ 9 ≤ (p j * ∏ k ∈ univ.erase j, p k) ^ 100 * pmv ^ 9 := h1
    _ = (∏ k ∈ univ.erase j, p k) ^ 100 * p j ^ 91 * pmv ^ 9 * p j ^ 9 := by ring

/-! ### Splitting a path -/

theorem up_append : ∀ (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (e : ℕ),
    up (L₁ ++ L₂) e = up L₁ e * up L₂ e
  | [], L₂, e => by simp [up]
  | M :: L₁, L₂, e => by
    rw [List.cons_append, up_cons, up_cons, up_append L₁ L₂ e, mul_assoc]

theorem pw_append : ∀ (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (a b : Fin 3),
    pw (L₁ ++ L₂) a b = pw L₁ a 0 * pw L₂ 0 b + pw L₁ a 1 * pw L₂ 1 b + pw L₁ a 2 * pw L₂ 2 b
  | [], L₂, a, b => by
    fin_cases a <;> simp [pw]
  | M :: L₁, L₂, a, b => by
    rw [List.cons_append, pw, pw_append L₁ L₂ (a + 1) b, pw_append L₁ L₂ (a + 2) b, pw, pw, pw]
    ring

/-- AM–GM for three terms. -/
theorem amgm3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
  have h := amgm_real (univ : Finset (Fin 3)) ![x, y, z] ![1, 1, 1]
    (by intro i _; fin_cases i <;> simp [hx, hy, hz])
  simp [Fin.sum_univ_three, Fin.prod_univ_three] at h
  linarith

/-! ### Products of the sums over the cells -/

theorem up_nonneg : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ e, 0 ≤ up Ms e
  | [], _, _ => zero_le_one
  | M :: Ms, h, e => by
    rw [up_cons]
    exact mul_nonneg (pow_nonneg (prod_nonneg fun k _ => h M List.mem_cons_self _ _) _)
      (up_nonneg Ms (fun M' hM' => h M' (List.mem_cons_of_mem _ hM')) e)

/-- The product of `pw` over the three closed cells. -/
noncomputable def Dp (Ms : List (Fin 3 → Fin 3 → ℝ)) : ℝ := pw Ms 0 0 * pw Ms 1 1 * pw Ms 2 2

/-- The product of `pw` over the six cells with different ends. -/
noncomputable def Op (Ms : List (Fin 3 → Fin 3 → ℝ)) : ℝ :=
  ∏ k : Fin 6, pw Ms (offPair k).1 (offPair k).2

theorem Dp_nonneg (Ms : List (Fin 3 → Fin 3 → ℝ)) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) :
    0 ≤ Dp Ms :=
  mul_nonneg (mul_nonneg (pw_nonneg Ms hM _ _) (pw_nonneg Ms hM _ _)) (pw_nonneg Ms hM _ _)

theorem Op_nonneg (Ms : List (Fin 3 → Fin 3 → ℝ)) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) :
    0 ≤ Op Ms := prod_nonneg fun _ _ => pw_nonneg Ms hM _ _

/-- The closed cells: `sN ^ 6 * up 1 ≤ Dp ^ 2`. -/
theorem Dp_sq (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ))
    (hM : ∀ M' ∈ M :: Ms, ∀ a b, 0 ≤ M' a b) :
    (sN (Ms.length + 1) : ℝ) ^ 6 * up (M :: Ms) 1 ≤ Dp (M :: Ms) ^ 2 := by
  set w := dN Ms.length with hw
  have hs : sN (Ms.length + 1) = 2 * w := sN_succ _
  rcases Nat.eq_zero_or_pos w with h0 | hpos
  · rw [hs, h0]
    simp
    positivity
  have hc : ∀ a : Fin 3, cnt (M :: Ms).length a a = 2 * w := fun a => by
    simp [cnt, hs]
  have hub : ∀ a : Fin 3, ((2 * w : ℕ) : ℝ) ^ (2 * w) * wgp (M :: Ms) a a
      ≤ pw (M :: Ms) a a ^ (2 * w) := fun a => by
    have := pw_ub (M :: Ms) hM a a
    rwa [hc a] at this
  have hg : ∀ a b, 0 ≤ wgp (M :: Ms) a b := wgp_nonneg _ hM
  have hp : ∀ a b, 0 ≤ pw (M :: Ms) a b := pw_nonneg _ hM
  have hN : (0 : ℝ) ≤ ((2 * w : ℕ) : ℝ) ^ (2 * w) := pow_nonneg (Nat.cast_nonneg _) _
  have h3 := mul_le_mul (mul_le_mul (hub 0) (hub 1) (mul_nonneg hN (hg _ _))
    (pow_nonneg (hp _ _) _)) (hub 2) (mul_nonneg hN (hg _ _))
    (mul_nonneg (pow_nonneg (hp _ _) _) (pow_nonneg (hp _ _) _))
  have hD : Dg (M :: Ms) = up (M :: Ms) w := Dg_eq M Ms
  have key : (((2 * w : ℕ) : ℝ) ^ 6 * up (M :: Ms) 1) ^ w ≤ (Dp (M :: Ms) ^ 2) ^ w := by
    calc (((2 * w : ℕ) : ℝ) ^ 6 * up (M :: Ms) 1) ^ w
        = ((2 * w : ℕ) : ℝ) ^ (2 * w) * wgp (M :: Ms) 0 0
          * (((2 * w : ℕ) : ℝ) ^ (2 * w) * wgp (M :: Ms) 1 1)
          * (((2 * w : ℕ) : ℝ) ^ (2 * w) * wgp (M :: Ms) 2 2) := by
          have e : up (M :: Ms) 1 ^ w = wgp (M :: Ms) 0 0 * wgp (M :: Ms) 1 1 * wgp (M :: Ms) 2 2 := by
            rw [← up_mul, one_mul, ← hD, Dg]
          rw [mul_pow, e]
          ring
      _ ≤ _ := h3
      _ = (Dp (M :: Ms) ^ 2) ^ w := by rw [Dp]; ring
  rw [hs]
  exact le_of_pow_le_pow_left₀ hpos.ne' (sq_nonneg _) key

/-- The cells with different ends: `dN ^ 6 * up 1 ≤ Op`. -/
theorem Op_ge (Ms : List (Fin 3 → Fin 3 → ℝ)) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) :
    (dN Ms.length : ℝ) ^ 6 * up Ms 1 ≤ Op Ms := by
  set a := dN Ms.length with ha
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [h0]
    simpa using Op_nonneg Ms hM
  have hc : ∀ k : Fin 6, cnt Ms.length (offPair k).1 (offPair k).2 = a := fun k => by
    simp [cnt, offPair_ne k, ha]
  have hub : ∀ k : Fin 6, (a : ℝ) ^ a * wgp Ms (offPair k).1 (offPair k).2
      ≤ pw Ms (offPair k).1 (offPair k).2 ^ a := fun k => by
    have := pw_ub Ms hM (offPair k).1 (offPair k).2
    rwa [hc k] at this
  have key : ((a : ℝ) ^ 6 * up Ms 1) ^ a ≤ Op Ms ^ a := by
    calc ((a : ℝ) ^ 6 * up Ms 1) ^ a
        = ∏ k : Fin 6, (a : ℝ) ^ a * wgp Ms (offPair k).1 (offPair k).2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            mul_pow, ← up_mul, one_mul, ← pow_mul, ← pow_mul, mul_comm a 6]
          congr 1
          exact (Og_eq Ms).symm
      _ ≤ ∏ k : Fin 6, pw Ms (offPair k).1 (offPair k).2 ^ a :=
          Finset.prod_le_prod₀ (fun k _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
            (wgp_nonneg Ms hM _ _)) fun k _ => hub k
      _ = Op Ms ^ a := by rw [Op, Finset.prod_pow]
  exact le_of_pow_le_pow_left₀ hpos.ne' (Op_nonneg Ms hM) key

/-- All nine cells of a path with at least one step. -/
theorem DpOp_sq (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ))
    (hM : ∀ M' ∈ M :: Ms, ∀ a b, 0 ≤ M' a b) :
    ((sN (Ms.length + 1) : ℝ) ^ 3 * (dN (Ms.length + 1) : ℝ) ^ 6) ^ 2 * up (M :: Ms) 3
      ≤ (Dp (M :: Ms) * Op (M :: Ms)) ^ 2 := by
  have h1 := Dp_sq M Ms hM
  have h2 := Op_ge (M :: Ms) hM
  have hu := up_nonneg (M :: Ms) hM 1
  have hO := Op_nonneg (M :: Ms) hM
  have h2' : ((dN (Ms.length + 1) : ℝ) ^ 6 * up (M :: Ms) 1) ^ 2 ≤ Op (M :: Ms) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hu) h2 2
  have e3 : up (M :: Ms) 3 = up (M :: Ms) 1 * up (M :: Ms) 1 ^ 2 :=
    calc up (M :: Ms) 3 = up (M :: Ms) 1 * up (M :: Ms) 2 := up_add (M :: Ms) 1 2
      _ = _ := by rw [show up (M :: Ms) 2 = up (M :: Ms) 1 ^ 2 from up_mul (M :: Ms) 1 2]
  calc ((sN (Ms.length + 1) : ℝ) ^ 3 * (dN (Ms.length + 1) : ℝ) ^ 6) ^ 2 * up (M :: Ms) 3
      = ((sN (Ms.length + 1) : ℝ) ^ 6 * up (M :: Ms) 1)
        * ((dN (Ms.length + 1) : ℝ) ^ 6 * up (M :: Ms) 1) ^ 2 := by rw [e3]; ring
    _ ≤ Dp (M :: Ms) ^ 2 * Op (M :: Ms) ^ 2 :=
        mul_le_mul h1 h2' (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

/-! ### The families twisted by a rotation -/

/-- The product of `pw` over the cells `(a, a + 1)`. -/
noncomputable def T₁ (Ms : List (Fin 3 → Fin 3 → ℝ)) : ℝ := pw Ms 0 1 * pw Ms 1 2 * pw Ms 2 0

/-- The product of `pw` over the cells `(a, a + 2)`. -/
noncomputable def T₂ (Ms : List (Fin 3 → Fin 3 → ℝ)) : ℝ := pw Ms 0 2 * pw Ms 1 0 * pw Ms 2 1

theorem cell_cube (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) (a b : Fin 3) :
    27 * (pw L₁ a 0 * pw L₂ 0 b * (pw L₁ a 1 * pw L₂ 1 b) * (pw L₁ a 2 * pw L₂ 2 b))
      ≤ pw (L₁ ++ L₂) a b ^ 3 := by
  rw [pw_append]
  exact amgm3 (mul_nonneg (pw_nonneg L₁ h₁ _ _) (pw_nonneg L₂ h₂ _ _))
    (mul_nonneg (pw_nonneg L₁ h₁ _ _) (pw_nonneg L₂ h₂ _ _))
    (mul_nonneg (pw_nonneg L₁ h₁ _ _) (pw_nonneg L₂ h₂ _ _))

/-- Three cells forming a bijection, with the midpoint of the path uniform on the three
indices. -/
theorem tri_cube (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) :
    27 ^ 3 * (Dp L₁ * Op L₁ * (Dp L₂ * Op L₂)) ≤ T₁ (L₁ ++ L₂) ^ 3 ∧
      27 ^ 3 * (Dp L₁ * Op L₁ * (Dp L₂ * Op L₂)) ≤ T₂ (L₁ ++ L₂) ^ 3 := by
  have hp₁ := pw_nonneg L₁ h₁
  have hp₂ := pw_nonneg L₂ h₂
  have hc := cell_cube L₁ L₂ h₁ h₂
  have h0 : ∀ a b : Fin 3, 0 ≤ 27 * (pw L₁ a 0 * pw L₂ 0 b * (pw L₁ a 1 * pw L₂ 1 b)
      * (pw L₁ a 2 * pw L₂ 2 b)) := fun a b =>
    mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg (hp₁ _ _) (hp₂ _ _))
      (mul_nonneg (hp₁ _ _) (hp₂ _ _))) (mul_nonneg (hp₁ _ _) (hp₂ _ _)))
  have hq : ∀ a b : Fin 3, 0 ≤ pw (L₁ ++ L₂) a b ^ 3 := fun a b => (h0 a b).trans (hc a b)
  constructor
  · have h3 := mul_le_mul (mul_le_mul (hc 0 1) (hc 1 2) (h0 _ _) (hq _ _)) (hc 2 0) (h0 _ _)
      (mul_nonneg (hq _ _) (hq _ _))
    calc (27 : ℝ) ^ 3 * (Dp L₁ * Op L₁ * (Dp L₂ * Op L₂)) = _ := by
          simp only [Dp, Op, Fin.prod_univ_six, offPair]
          simp
          ring
      _ ≤ _ := h3
      _ = T₁ (L₁ ++ L₂) ^ 3 := by rw [T₁]; ring
  · have h3 := mul_le_mul (mul_le_mul (hc 0 2) (hc 1 0) (h0 _ _) (hq _ _)) (hc 2 1) (h0 _ _)
      (mul_nonneg (hq _ _) (hq _ _))
    calc (27 : ℝ) ^ 3 * (Dp L₁ * Op L₁ * (Dp L₂ * Op L₂)) = _ := by
          simp only [Dp, Op, Fin.prod_univ_six, offPair]
          simp
          ring
      _ ≤ _ := h3
      _ = T₂ (L₁ ++ L₂) ^ 3 := by rw [T₂]; ring

/-- A bijection triple of a path made of two halves of `h ≥ 1` steps each. -/
theorem tri_sq (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h : ℕ) (hh : 0 < h) (hl₁ : L₁.length = h)
    (hl₂ : L₂.length = h) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b) (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) :
    ((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up (L₁ ++ L₂) 1 ≤ T₁ (L₁ ++ L₂) ^ 2 ∧
      ((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up (L₁ ++ L₂) 1 ≤ T₂ (L₁ ++ L₂) ^ 2 := by
  obtain ⟨M₁, L₁', rfl⟩ : ∃ M₁ L₁', L₁ = M₁ :: L₁' := by
    cases L₁ with
    | nil => simp at hl₁; omega
    | cons M L => exact ⟨M, L, rfl⟩
  obtain ⟨M₂, L₂', rfl⟩ : ∃ M₂ L₂', L₂ = M₂ :: L₂' := by
    cases L₂ with
    | nil => simp at hl₂; omega
    | cons M L => exact ⟨M, L, rfl⟩
  have e₁ : L₁'.length + 1 = h := by simpa using hl₁
  have e₂ : L₂'.length + 1 = h := by simpa using hl₂
  have q₁ := DpOp_sq M₁ L₁' h₁
  have q₂ := DpOp_sq M₂ L₂' h₂
  rw [e₁] at q₁
  rw [e₂] at q₂
  obtain ⟨c₁, c₂⟩ := tri_cube (M₁ :: L₁') (M₂ :: L₂') h₁ h₂
  set Q₁ := Dp (M₁ :: L₁') * Op (M₁ :: L₁') with hQ₁
  set Q₂ := Dp (M₂ :: L₂') * Op (M₂ :: L₂') with hQ₂
  have hQ₁0 : 0 ≤ Q₁ := mul_nonneg (Dp_nonneg _ h₁) (Op_nonneg _ h₁)
  have hQ₂0 : 0 ≤ Q₂ := mul_nonneg (Dp_nonneg _ h₂) (Op_nonneg _ h₂)
  have hu₁ := up_nonneg (M₁ :: L₁') h₁ 3
  have hu₂ := up_nonneg (M₂ :: L₂') h₂ 3
  set B : ℝ := (sN h : ℝ) ^ 3 * (dN h : ℝ) ^ 6 with hB
  have e3 : up (M₁ :: L₁' ++ M₂ :: L₂') 1 ^ 3 = up (M₁ :: L₁') 3 * up (M₂ :: L₂') 3 := by
    rw [← up_append]
    exact (up_mul _ 1 3).symm
  -- both triples have the same bound
  have key : ∀ T : ℝ, (27 : ℝ) ^ 3 * (Q₁ * Q₂) ≤ T ^ 3 →
      ((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up (M₁ :: L₁' ++ M₂ :: L₂') 1 ≤ T ^ 2 := by
    intro T hT
    have h6 : (((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up (M₁ :: L₁' ++ M₂ :: L₂') 1) ^ 3
        ≤ (T ^ 2) ^ 3 :=
      calc (((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up (M₁ :: L₁' ++ M₂ :: L₂') 1) ^ 3
          = (27 : ℝ) ^ 6 * ((B ^ 2 * up (M₁ :: L₁') 3) * (B ^ 2 * up (M₂ :: L₂') 3)) := by
            rw [mul_pow, e3, hB]
            ring
        _ ≤ (27 : ℝ) ^ 6 * (Q₁ ^ 2 * Q₂ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul q₁ q₂
              (mul_nonneg (sq_nonneg _) hu₂) (sq_nonneg _)) (by norm_num)
        _ = ((27 : ℝ) ^ 3 * (Q₁ * Q₂)) ^ 2 := by ring
        _ ≤ (T ^ 3) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (by norm_num) (mul_nonneg hQ₁0 hQ₂0)) hT 2
        _ = (T ^ 2) ^ 3 := by ring
    exact le_of_pow_le_pow_left₀ (by norm_num) (sq_nonneg _) h6
  exact ⟨key _ c₁, key _ c₂⟩

/-! ### The numbers of walks of a path made of two halves -/

theorem walk_num (h : ℕ) (hh : 2 ≤ h) :
    dN (h + h) ^ 5 ≤ sN (h + h) ^ 2 * (27 * sN h ^ 2 * dN h ^ 4) := by
  obtain ⟨hd, hs⟩ := dN_sN_add h h
  rw [hd, hs]
  obtain ⟨he, ho⟩ := sN_dN_parity h
  rcases Nat.even_or_odd h with hev | hodd
  · have e := he hev
    generalize dN h = a at *
    rw [e]
    have : ((a + 1) * (a + 1) + 2 * (a * a)) ^ 2 * (27 * (a + 1) ^ 2 * a ^ 4)
        = ((a + 1) * a + a * (a + 1) + a * a) ^ 5
          + a ^ 4 * (81 * a ^ 4 + 252 * a ^ 3 + 273 * a ^ 2 + 130 * a + 27) := by ring
    exact Nat.le.intro this.symm
  · have e := ho hodd
    have hs1 : 1 ≤ sN h := by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
      have := dN_pos k
      rw [show k + 2 = (k + 1) + 1 from rfl, sN_succ]
      omega
    generalize sN h = s at *
    rw [e]
    have hid : (s * s + 2 * ((s + 1) * (s + 1))) ^ 2 * (27 * s ^ 2 * (s + 1) ^ 4)
          + (s + 1) ^ 4 * (16 * s + 1)
        = (s * (s + 1) + (s + 1) * s + (s + 1) * (s + 1)) ^ 5
          + (s + 1) ^ 4 * (81 * s ^ 4 + 72 * s ^ 3 + 3 * s ^ 2) := by ring
    have h3 : s ≤ s ^ 3 := Nat.le_self_pow (by norm_num) s
    have h4 : 1 ≤ s ^ 4 := Nat.one_le_pow _ _ hs1
    have hXY : (s + 1) ^ 4 * (16 * s + 1) ≤ (s + 1) ^ 4 * (81 * s ^ 4 + 72 * s ^ 3 + 3 * s ^ 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-- The numeric inequality behind the rotated families. -/
theorem walk_num' (h : ℕ) (hh : 2 ≤ h) :
    dN (h + h) ^ 600 * sN (h + h) ^ 9
      ≤ (sN (h + h) ^ 3 * (27 * sN h ^ 2 * dN h ^ 4)) ^ 100 * dN (h + h) ^ 9 := by
  have h1 := walk_num h hh
  have hev : Even (h + h) := ⟨h, rfl⟩
  have hs : dN (h + h) ≤ sN (h + h) := by
    have := (sN_dN_parity (h + h)).1 hev
    omega
  set α := dN (h + h) with hα
  set S := sN (h + h) with hS
  set B := 27 * sN h ^ 2 * dN h ^ 4 with hB
  calc α ^ 600 * S ^ 9 = (α ^ 5) ^ 100 * α ^ 91 * S ^ 9 * α ^ 9 := by ring
    _ ≤ (S ^ 2 * B) ^ 100 * S ^ 91 * S ^ 9 * α ^ 9 := by
        gcongr
    _ = (S ^ 3 * B) ^ 100 * α ^ 9 := by ring

set_option exponentiation.threshold 600 in
/-- **Assembly for a family made of the closed cells and one bijection triple.** The closed
cells take all their walks, the triple the walks through a uniform midpoint. -/
theorem rot_assembly (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (h : ℕ) (hh : 2 ≤ h)
    (hlen : Ms.length = h + h) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) (cell : Fin 6 → Fin 3 × Fin 3) (T : ℝ) (hT0 : 0 ≤ T)
    (hfam : ∏ k, pw Ms (cell k).1 (cell k).2 = Dp Ms * T)
    (hT : ((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up Ms 1 ≤ T ^ 2)
    (j : Fin 6) (c d : Fin 3) :
    ((dN Ms.length : ℝ) * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (cell k).1 (cell k).2) ^ 100
        * pw Ms (cell j).1 (cell j).2 ^ 91 * pw Ms c d ^ 9 := by
  obtain ⟨hchild, hmxp⟩ := offBall_prod Ms As hM hA hball
  have hev : Even Ms.length := ⟨h, hlen⟩
  obtain ⟨M, Ms', rfl⟩ : ∃ M Ms', Ms = M :: Ms' := by
    cases Ms with
    | nil => simp at hlen; omega
    | cons M L => exact ⟨M, L, rfl⟩
  have hn : Ms'.length + 1 = h + h := by simpa using hlen
  have hD := Dp_sq M Ms' hM
  rw [hn] at hD
  rw [hlen]
  rw [hlen] at hev
  have hS1 : 1 ≤ sN (h + h) := by
    have := (sN_dN_parity (h + h)).1 hev
    omega
  have hsh : 0 < sN h := by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
    have := dN_pos k
    rw [show k + 2 = (k + 1) + 1 from rfl, sN_succ]
    omega
  have hdh : 0 < dN h := by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    exact dN_pos k
  set α := dN (h + h) with hα
  set S := sN (h + h) with hS
  set B := 27 * sN h ^ 2 * dN h ^ 4 with hB
  have hBr : (B : ℝ) = (27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4 := by
    rw [hB]
    push_cast
    ring
  rw [← hBr] at hT
  have hCpos : (0 : ℝ) < (S : ℝ) ^ 3 * (B : ℝ) := by
    have h1 : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS1
    have h2 : (0 : ℝ) < (B : ℝ) := by
      rw [hBr]
      have h3 : (0 : ℝ) < (sN h : ℝ) := by exact_mod_cast hsh
      have h4 : (0 : ℝ) < (dN h : ℝ) := by exact_mod_cast hdh
      positivity
    positivity
  set U1 := up (M :: Ms') 1 with hU1
  have hU10 : 0 ≤ U1 := up_nonneg _ hM 1
  have hU100 : up (M :: Ms') 100 = U1 ^ 100 := up_mul (M :: Ms') 1 100
  have hAP : 0 < As.prod := List.prod_pos hA
  have hmnp := mnP_nonneg (M :: Ms') hM
  have hU1pos : 0 < U1 := by
    rcases hU10.eq_or_lt with h0 | h0
    · rw [hU100, ← h0] at hchild
      have : 0 < As.prod ^ 600 * mxP (M :: Ms') ^ 9 := mul_pos (pow_pos hAP _) (pow_pos hmxp _)
      norm_num at hchild
      linarith
    · exact h0
  set Fam := Dp (M :: Ms') * T with hFam
  have hFam0 : 0 ≤ Fam := mul_nonneg (Dp_nonneg _ hM) hT0
  have hF1 : ((S : ℝ) ^ 3 * (B : ℝ) * U1) ^ 2 ≤ Fam ^ 2 :=
    calc ((S : ℝ) ^ 3 * (B : ℝ) * U1) ^ 2 = ((S : ℝ) ^ 6 * U1) * ((B : ℝ) ^ 2 * U1) := by ring
      _ ≤ Dp (M :: Ms') ^ 2 * T ^ 2 :=
          mul_le_mul hD hT (mul_nonneg (sq_nonneg _) hU10) (sq_nonneg _)
      _ = Fam ^ 2 := by rw [hFam]; ring
  have hF : (S : ℝ) ^ 3 * (B : ℝ) * U1 ≤ Fam := le_of_pow_le_pow_left₀ two_ne_zero hFam0 hF1
  have hFampos : 0 < Fam := (mul_pos hCpos hU1pos).trans_le hF
  have hNI : (α : ℝ) ^ 600 * (S : ℝ) ^ 9 ≤ ((S : ℝ) ^ 3 * (B : ℝ)) ^ 100 * (α : ℝ) ^ 9 := by
    have h' : ((α ^ 600 * S ^ 9 : ℕ) : ℝ) ≤ (((S ^ 3 * B) ^ 100 * α ^ 9 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (walk_num' h hh)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_pow] at h'
    exact h'
  have hαr : (0 : ℝ) ≤ (α : ℝ) := Nat.cast_nonneg _
  have hmv : (α : ℝ) * mnP (M :: Ms') ≤ pw (M :: Ms') c d := by
    refine le_trans ?_ (pw_ge (M :: Ms') hM c d)
    refine mul_le_mul_of_nonneg_right ?_ hmnp
    have := cnt_ge (M :: Ms').length (by rw [hlen]; exact hev) c d
    rw [show dN (M :: Ms').length = α by rw [hlen]] at this
    exact_mod_cast this
  have hpj : ∀ a b : Fin 3, pw (M :: Ms') a b ≤ (S : ℝ) * mxP (M :: Ms') := fun a b => by
    refine le_trans (pw_le (M :: Ms') hM a b) ?_
    refine mul_le_mul_of_nonneg_right ?_ hmxp.le
    have := cnt_le (M :: Ms').length (by rw [hlen]; exact hev) a b
    rw [show sN (M :: Ms').length = S by rw [hlen]] at this
    exact_mod_cast this
  have hp0 : ∀ k : Fin 6, 0 ≤ pw (M :: Ms') (cell k).1 (cell k).2 := fun k => pw_nonneg _ hM _ _
  refine crude_assembly hp0 (by rw [hfam]; exact hFampos) (fun j' => ?_) j
  rw [hfam]
  calc ((α : ℝ) * As.prod) ^ 600 * pw (M :: Ms') (cell j').1 (cell j').2 ^ 9
      ≤ ((α : ℝ) * As.prod) ^ 600 * ((S : ℝ) * mxP (M :: Ms')) ^ 9 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hp0 j') (hpj _ _) 9)
          (pow_nonneg (mul_nonneg hαr hAP.le) _)
    _ = ((α : ℝ) ^ 600 * (S : ℝ) ^ 9) * (As.prod ^ 600 * mxP (M :: Ms') ^ 9) := by ring
    _ ≤ (((S : ℝ) ^ 3 * (B : ℝ)) ^ 100 * (α : ℝ) ^ 9) * (up (M :: Ms') 100 * mnP (M :: Ms') ^ 9) :=
        mul_le_mul hNI hchild (mul_nonneg (pow_nonneg hAP.le _) (pow_nonneg hmxp.le _))
          (mul_nonneg (pow_nonneg hCpos.le _) (pow_nonneg hαr _))
    _ = ((S : ℝ) ^ 3 * (B : ℝ) * U1) ^ 100 * ((α : ℝ) * mnP (M :: Ms')) ^ 9 := by
        rw [hU100]
        ring
    _ ≤ Fam ^ 100 * pw (M :: Ms') c d ^ 9 :=
        mul_le_mul (pow_le_pow_left₀ (mul_nonneg hCpos.le hU10) hF 100)
          (pow_le_pow_left₀ (mul_nonneg hαr hmnp) hmv 9)
          (pow_nonneg (mul_nonneg hαr hmnp) _) (pow_nonneg hFam0 _)

/-- The halves of a path of `h + h` steps. -/
theorem halves (Ms : List (Fin 3 → Fin 3 → ℝ)) (h : ℕ) (hh : 2 ≤ h) (hlen : Ms.length = h + h)
    (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) :
    ((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up Ms 1 ≤ T₁ Ms ^ 2 ∧
      ((27 : ℝ) * (sN h : ℝ) ^ 2 * (dN h : ℝ) ^ 4) ^ 2 * up Ms 1 ≤ T₂ Ms ^ 2 := by
  have e : Ms.take h ++ Ms.drop h = Ms := List.take_append_drop h Ms
  have key := tri_sq (Ms.take h) (Ms.drop h) h (by omega) (by simp [hlen])
    (by simp [hlen]) (fun M hM' => hM M (List.mem_of_mem_take hM'))
    (fun M hM' => hM M (List.mem_of_mem_drop hM'))
  rwa [e] at key

/-- **The ball inequality of the path for the family twisted by the rotation `+ 1`.** -/
theorem walks_ball_rot1 (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (h : ℕ) (hh : 2 ≤ h)
    (hlen : Ms.length = h + h) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) (j : Fin 6) (c d : Fin 3) :
    ((dN Ms.length : ℝ) * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 ((offPair k).2 + 1)) ^ 100
        * pw Ms (offPair j).1 ((offPair j).2 + 1) ^ 91 * pw Ms c d ^ 9 := by
  have hp := pw_nonneg Ms hM
  refine rot_assembly Ms As h hh hlen hM hA hball (fun k => ((offPair k).1, (offPair k).2 + 1))
    (T₂ Ms) (mul_nonneg (mul_nonneg (hp _ _) (hp _ _)) (hp _ _)) ?_
    (halves Ms h hh hlen hM).2 j c d
  simp [Fin.prod_univ_six, offPair, Dp, T₂]
  ring

/-- **The ball inequality of the path for the family twisted by the rotation `+ 2`.** -/
theorem walks_ball_rot2 (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (h : ℕ) (hh : 2 ≤ h)
    (hlen : Ms.length = h + h) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) (j : Fin 6) (c d : Fin 3) :
    ((dN Ms.length : ℝ) * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 ((offPair k).2 + 2)) ^ 100
        * pw Ms (offPair j).1 ((offPair j).2 + 2) ^ 91 * pw Ms c d ^ 9 := by
  have hp := pw_nonneg Ms hM
  refine rot_assembly Ms As h hh hlen hM hA hball (fun k => ((offPair k).1, (offPair k).2 + 2))
    (T₁ Ms) (mul_nonneg (mul_nonneg (hp _ _) (hp _ _)) (hp _ _)) ?_
    (halves Ms h hh hlen hM).1 j c d
  simp [Fin.prod_univ_six, offPair, Dp, T₁]
  ring

/-! ### The alternating walks -/

/-- The weight of the walk that alternates between two indices: from `a` to `a + 1` and back
(`s = true`), or from `a` to `a + 2` and back (`s = false`). -/
noncomputable def alt : Bool → List (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ
  | _, [], _ => 1
  | true, M :: Ms, a => M a (a + 1) * alt false Ms (a + 1)
  | false, M :: Ms, a => M a (a + 2) * alt true Ms (a + 2)

/-- The end of the alternating walk. -/
def altEnd : Bool → ℕ → Fin 3 → Fin 3
  | _, 0, a => a
  | true, k + 1, a => altEnd false k (a + 1)
  | false, k + 1, a => altEnd true k (a + 2)

theorem altEnd_even : ∀ (k : ℕ) (s : Bool) (a : Fin 3), Even k → altEnd s k a = a
  | 0, s, a, _ => by cases s <;> rfl
  | 1, _, _, h => absurd h (by decide)
  | k + 2, s, a, h => by
    have hk : Even k := by
      obtain ⟨r, hr⟩ := h
      exact ⟨r - 1, by omega⟩
    have e1 : a + 1 + 2 = a := by fin_cases a <;> rfl
    have e2 : a + 2 + 1 = a := by fin_cases a <;> rfl
    cases s
    · show altEnd true (k + 1) (a + 2) = a
      show altEnd false k (a + 2 + 1) = a
      rw [e2]
      exact altEnd_even k false a hk
    · show altEnd false (k + 1) (a + 1) = a
      show altEnd true k (a + 1 + 2) = a
      rw [e1]
      exact altEnd_even k true a hk

theorem alt_nonneg : ∀ (s : Bool) (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a, 0 ≤ alt s Ms a
  | s, [], _, a => by cases s <;> simp [alt]
  | true, M :: Ms, h, a => by
    rw [alt]
    exact mul_nonneg (h M List.mem_cons_self _ _)
      (alt_nonneg false Ms (fun M' hM' => h M' (List.mem_cons_of_mem _ hM')) _)
  | false, M :: Ms, h, a => by
    rw [alt]
    exact mul_nonneg (h M List.mem_cons_self _ _)
      (alt_nonneg true Ms (fun M' hM' => h M' (List.mem_cons_of_mem _ hM')) _)

theorem alt_pos : ∀ (s : Bool) (Ms : List (Fin 3 → Fin 3 → ℝ)),
    (∀ M ∈ Ms, ∀ a b, a ≠ b → 0 < M a b) → ∀ a, 0 < alt s Ms a
  | s, [], _, a => by cases s <;> simp [alt]
  | true, M :: Ms, h, a => by
    rw [alt]
    exact mul_pos (h M List.mem_cons_self _ _ (add_one_ne a))
      (alt_pos false Ms (fun M' hM' => h M' (List.mem_cons_of_mem _ hM')) _)
  | false, M :: Ms, h, a => by
    rw [alt]
    exact mul_pos (h M List.mem_cons_self _ _ (add_two_ne a))
      (alt_pos true Ms (fun M' hM' => h M' (List.mem_cons_of_mem _ hM')) _)

/-- **AM–GM over the walks of a cell other than the alternating walk.** -/
theorem pw_ub_alt : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ (s : Bool) (a : Fin 3),
    1 ≤ cnt Ms.length a (altEnd s Ms.length a) ∧
    alt s Ms a ≤ pw Ms a (altEnd s Ms.length a) ∧
    ((cnt Ms.length a (altEnd s Ms.length a) - 1 : ℕ) : ℝ)
        ^ (cnt Ms.length a (altEnd s Ms.length a) - 1) * wgp Ms a (altEnd s Ms.length a)
      ≤ (pw Ms a (altEnd s Ms.length a) - alt s Ms a)
        ^ (cnt Ms.length a (altEnd s Ms.length a) - 1) * alt s Ms a ∧
    wgp Ms a (altEnd s Ms.length a)
      ≤ mxP Ms ^ (cnt Ms.length a (altEnd s Ms.length a) - 1) * alt s Ms a
  | [], _, s, a => by
    cases s <;> simp [cnt, sN_zero, altEnd, alt, pw, wgp, mxP]
  | M :: Ms, h, s, a => by
    have hMs : ∀ M' ∈ Ms, ∀ a b, 0 ≤ M' a b := fun M' hM' => h M' (List.mem_cons_of_mem _ hM')
    have hM := h M List.mem_cons_self
    have hx := mx_nonneg hM
    have hP := mxP_nonneg Ms hMs
    -- the two cases are the same up to the roles of `a + 1` and `a + 2`
    have main : ∀ (a₁ a₂ : Fin 3) (s' : Bool), a ≠ a₁ → a ≠ a₂ →
        cnt (Ms.length + 1) a (altEnd s' Ms.length a₁)
          = cnt Ms.length a₁ (altEnd s' Ms.length a₁) + cnt Ms.length a₂ (altEnd s' Ms.length a₁) →
        pw (M :: Ms) a (altEnd s' Ms.length a₁)
          = M a a₁ * pw Ms a₁ (altEnd s' Ms.length a₁) + M a a₂ * pw Ms a₂ (altEnd s' Ms.length a₁) →
        wgp (M :: Ms) a (altEnd s' Ms.length a₁)
          = M a a₁ ^ cnt Ms.length a₁ (altEnd s' Ms.length a₁) * wgp Ms a₁ (altEnd s' Ms.length a₁)
            * (M a a₂ ^ cnt Ms.length a₂ (altEnd s' Ms.length a₁)
              * wgp Ms a₂ (altEnd s' Ms.length a₁)) →
        1 ≤ cnt (Ms.length + 1) a (altEnd s' Ms.length a₁) ∧
        M a a₁ * alt s' Ms a₁ ≤ pw (M :: Ms) a (altEnd s' Ms.length a₁) ∧
        ((cnt (Ms.length + 1) a (altEnd s' Ms.length a₁) - 1 : ℕ) : ℝ)
            ^ (cnt (Ms.length + 1) a (altEnd s' Ms.length a₁) - 1)
            * wgp (M :: Ms) a (altEnd s' Ms.length a₁)
          ≤ (pw (M :: Ms) a (altEnd s' Ms.length a₁) - M a a₁ * alt s' Ms a₁)
            ^ (cnt (Ms.length + 1) a (altEnd s' Ms.length a₁) - 1) * (M a a₁ * alt s' Ms a₁) ∧
        wgp (M :: Ms) a (altEnd s' Ms.length a₁)
          ≤ (mx M * mxP Ms) ^ (cnt (Ms.length + 1) a (altEnd s' Ms.length a₁) - 1)
            * (M a a₁ * alt s' Ms a₁) := by
      intro a₁ a₂ s' hne₁ hne₂ hcnt hpw hwgp
      obtain ⟨i1, i2, i3, i4⟩ := pw_ub_alt Ms hMs s' a₁
      set b := altEnd s' Ms.length a₁ with hb
      set N₁ := cnt Ms.length a₁ b with hN₁
      set N₂ := cnt Ms.length a₂ b with hN₂
      have hal := alt_nonneg s' Ms hMs a₁
      have hp₁ := pw_nonneg Ms hMs a₁ b
      have hp₂ := pw_nonneg Ms hMs a₂ b
      have hg₁ := wgp_nonneg Ms hMs a₁ b
      have hg₂ := wgp_nonneg Ms hMs a₂ b
      have hd : 0 ≤ pw Ms a₁ b - alt s' Ms a₁ := sub_nonneg.mpr i2
      have hub₂ := pw_ub Ms hMs a₂ b
      have hle₂ := wgp_le Ms hMs a₂ b
      rw [hcnt, hpw, hwgp]
      have e : N₁ + N₂ - 1 = (N₁ - 1) + N₂ := by omega
      have eN : M a a₁ ^ N₁ = M a a₁ ^ (N₁ - 1) * M a a₁ := by
        rw [← pow_succ]
        congr 1
        omega
      refine ⟨by omega, ?_, ?_, ?_⟩
      · have := mul_le_mul_of_nonneg_left i2 (hM a a₁)
        have := mul_nonneg (hM a a₂) hp₂
        linarith
      · set x := M a a₁ * (pw Ms a₁ b - alt s' Ms a₁) with hxdef
        set y := M a a₂ * pw Ms a₂ b with hydef
        have hx0 : 0 ≤ x := mul_nonneg (hM _ _) hd
        have hy0 : 0 ≤ y := mul_nonneg (hM _ _) hp₂
        have key := amgm2 hx0 hy0 (N₁ - 1) N₂
        have hxy : M a a₁ * pw Ms a₁ b + M a a₂ * pw Ms a₂ b - M a a₁ * alt s' Ms a₁ = x + y := by
          rw [hxdef, hydef]
          ring
        rw [hxy, e]
        have h1 : M a a₁ ^ (N₁ - 1) * (((N₁ - 1 : ℕ) : ℝ) ^ (N₁ - 1) * wgp Ms a₁ b)
            ≤ x ^ (N₁ - 1) * alt s' Ms a₁ := by
          rw [hxdef, mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left i3 (pow_nonneg (hM _ _) _)
        have h2 : M a a₂ ^ N₂ * ((N₂ : ℝ) ^ N₂ * wgp Ms a₂ b) ≤ y ^ N₂ := by
          rw [hydef, mul_pow]
          exact mul_le_mul_of_nonneg_left hub₂ (pow_nonneg (hM _ _) _)
        have hpp := pow_self_pos (N₁ - 1)
        have hqq := pow_self_pos N₂
        have h12 := mul_le_mul h1 h2 (mul_nonneg (pow_nonneg (hM _ _) _) (mul_nonneg hqq.le hg₂))
          (mul_nonneg (pow_nonneg hx0 _) hal)
        have hN : (0 : ℝ) ≤ ((N₁ - 1 + N₂ : ℕ) : ℝ) ^ (N₁ - 1 + N₂) := (pow_self_pos _).le
        have hMa : 0 ≤ M a a₁ := hM _ _
        have hpq : (0 : ℝ) < ((N₁ - 1 : ℕ) : ℝ) ^ (N₁ - 1) * (N₂ : ℝ) ^ N₂ := mul_pos hpp hqq
        refine le_of_mul_le_mul_left ?_ hpq
        calc ((N₁ - 1 : ℕ) : ℝ) ^ (N₁ - 1) * (N₂ : ℝ) ^ N₂ * (((N₁ - 1 + N₂ : ℕ) : ℝ) ^ (N₁ - 1 + N₂)
              * (M a a₁ ^ N₁ * wgp Ms a₁ b * (M a a₂ ^ N₂ * wgp Ms a₂ b)))
            = ((N₁ - 1 + N₂ : ℕ) : ℝ) ^ (N₁ - 1 + N₂)
              * ((M a a₁ ^ (N₁ - 1) * (((N₁ - 1 : ℕ) : ℝ) ^ (N₁ - 1) * wgp Ms a₁ b))
                * (M a a₂ ^ N₂ * ((N₂ : ℝ) ^ N₂ * wgp Ms a₂ b))) * M a a₁ := by
              rw [eN]
              ring
          _ ≤ ((N₁ - 1 + N₂ : ℕ) : ℝ) ^ (N₁ - 1 + N₂)
              * ((x ^ (N₁ - 1) * alt s' Ms a₁) * y ^ N₂) * M a a₁ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h12 hN) hMa
          _ = (((N₁ - 1 + N₂ : ℕ) : ℝ) ^ (N₁ - 1 + N₂) * (x ^ (N₁ - 1) * y ^ N₂))
              * (M a a₁ * alt s' Ms a₁) := by ring
          _ ≤ (((N₁ - 1 : ℕ) : ℝ) ^ (N₁ - 1) * (N₂ : ℝ) ^ N₂ * (x + y) ^ (N₁ - 1 + N₂))
              * (M a a₁ * alt s' Ms a₁) :=
              mul_le_mul_of_nonneg_right key (mul_nonneg hMa hal)
          _ = _ := by ring
      · rw [e, eN, pow_add, mul_pow, mul_pow]
        have h1 : M a a₁ ^ (N₁ - 1) * wgp Ms a₁ b
            ≤ mx M ^ (N₁ - 1) * (mxP Ms ^ (N₁ - 1) * alt s' Ms a₁) :=
          mul_le_mul (pow_le_pow_left₀ (hM _ _) (le_mx M hne₁) _) i4 hg₁ (pow_nonneg hx _)
        have h2 : M a a₂ ^ N₂ * wgp Ms a₂ b ≤ mx M ^ N₂ * mxP Ms ^ N₂ :=
          mul_le_mul (pow_le_pow_left₀ (hM _ _) (le_mx M hne₂) _) hle₂ hg₂ (pow_nonneg hx _)
        have hMa : 0 ≤ M a a₁ := hM _ _
        calc M a a₁ ^ (N₁ - 1) * M a a₁ * wgp Ms a₁ b * (M a a₂ ^ N₂ * wgp Ms a₂ b)
            = (M a a₁ ^ (N₁ - 1) * wgp Ms a₁ b) * (M a a₂ ^ N₂ * wgp Ms a₂ b) * M a a₁ := by ring
          _ ≤ (mx M ^ (N₁ - 1) * (mxP Ms ^ (N₁ - 1) * alt s' Ms a₁)) * (mx M ^ N₂ * mxP Ms ^ N₂)
              * M a a₁ :=
              mul_le_mul_of_nonneg_right (mul_le_mul h1 h2
                (mul_nonneg (pow_nonneg (hM _ _) _) hg₂)
                (mul_nonneg (pow_nonneg hx _) (mul_nonneg (pow_nonneg hP _) hal))) hMa
          _ = _ := by ring
    rw [mxP_cons]
    cases s
    · have := main (a + 2) (a + 1) true (add_two_ne a) (add_one_ne a)
        (by rw [cnt_succ, add_comm]) (by rw [pw, add_comm]) (by rw [wgp, mul_comm])
      exact this
    · have := main (a + 1) (a + 2) false (add_one_ne a) (add_two_ne a)
        (by rw [cnt_succ]) (by rw [pw]) (by rw [wgp])
      exact this

/-- The two alternating walks between `a` and `a + 1` use the pairs `(a, a + 1)` and
`(a + 1, a)` once each at every step; this is the difference between the closed walks at these
two indices and the walks between them. -/
theorem alt_bal : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)) (a : Fin 3),
    (Even Ms.length → wgp Ms a a * wgp Ms (a + 1) (a + 1)
        = wgp Ms a (a + 1) * wgp Ms (a + 1) a * (alt true Ms a * alt false Ms (a + 1))) ∧
    (Odd Ms.length → wgp Ms a (a + 1) * wgp Ms (a + 1) a
        = wgp Ms a a * wgp Ms (a + 1) (a + 1) * (alt true Ms a * alt false Ms (a + 1)))
  | [], a => by
    refine ⟨fun _ => by simp [wgp, alt], fun h => absurd h (by decide)⟩
  | M :: Ms, a => by
    obtain ⟨ihe, iho⟩ := alt_bal Ms a
    obtain ⟨pe, po⟩ := sN_dN_parity Ms.length
    have w_aa : wgp (M :: Ms) a a = M a (a + 1) ^ dN Ms.length * wgp Ms (a + 1) a
        * (M a (a + 2) ^ dN Ms.length * wgp Ms (a + 2) a) := by
      fin_cases a <;> simp [wgp, cnt]
    have w_bb : wgp (M :: Ms) (a + 1) (a + 1) = M (a + 1) (a + 2) ^ dN Ms.length
        * wgp Ms (a + 2) (a + 1) * (M (a + 1) a ^ dN Ms.length * wgp Ms a (a + 1)) := by
      fin_cases a <;> simp [wgp, cnt]
    have w_ab : wgp (M :: Ms) a (a + 1) = M a (a + 1) ^ sN Ms.length * wgp Ms (a + 1) (a + 1)
        * (M a (a + 2) ^ dN Ms.length * wgp Ms (a + 2) (a + 1)) := by
      fin_cases a <;> simp [wgp, cnt]
    have w_ba : wgp (M :: Ms) (a + 1) a = M (a + 1) (a + 2) ^ dN Ms.length * wgp Ms (a + 2) a
        * (M (a + 1) a ^ sN Ms.length * wgp Ms a a) := by
      fin_cases a <;> simp [wgp, cnt]
    have al_a : alt true (M :: Ms) a = M a (a + 1) * alt false Ms (a + 1) := rfl
    have al_b : alt false (M :: Ms) (a + 1) = M (a + 1) a * alt true Ms a := by
      fin_cases a <;> simp [alt]
    rw [w_aa, w_bb, w_ab, w_ba, al_a, al_b]
    constructor
    · intro hev
      have hk : Odd Ms.length := by
        rw [List.length_cons, Nat.even_add_one] at hev
        exact Nat.not_even_iff_odd.mp hev
      have e := po hk
      have i := iho hk
      rw [e]
      linear_combination ((M a (a + 1) * M (a + 1) a) ^ (sN Ms.length + 1)
        * (M a (a + 2) * M (a + 1) (a + 2)) ^ (sN Ms.length + 1)
        * wgp Ms (a + 2) a * wgp Ms (a + 2) (a + 1)) * i
    · intro hodd
      have hk : Even Ms.length := by
        rw [List.length_cons, Nat.odd_add_one] at hodd
        exact Nat.not_odd_iff_even.mp hodd
      have e := pe hk
      have i := ihe hk
      rw [e]
      linear_combination ((M a (a + 1) * M (a + 1) a) ^ (dN Ms.length + 1)
        * (M a (a + 2) * M (a + 1) (a + 2)) ^ dN Ms.length
        * wgp Ms (a + 2) a * wgp Ms (a + 2) (a + 1)) * i

/-! ### The families twisted by a transposition -/

/-- The transposition of `Fin 3` that exchanges `a` and `a + 1`. -/
def tr (a x : Fin 3) : Fin 3 := -(x + a + 2)

theorem prod_tr (a : Fin 3) (F : Fin 3 → Fin 3 → ℝ) :
    ∏ k : Fin 6, F (offPair k).1 (tr a (offPair k).2)
      = F a a * F (a + 1) (a + 1) * F (a + 2) a * F (a + 2) (a + 1) * F a (a + 2)
        * F (a + 1) (a + 2) := by
  fin_cases a <;>
    simp [Fin.prod_univ_six, offPair, tr, show (-2 : Fin 3) = 1 from rfl,
      show (-1 : Fin 3) = 2 from rfl] <;> ring

theorem Og_tr (Ms : List (Fin 3 → Fin 3 → ℝ)) (a : Fin 3) :
    Og Ms = wgp Ms a (a + 1) * wgp Ms (a + 1) a * wgp Ms (a + 2) a * wgp Ms (a + 2) (a + 1)
      * wgp Ms a (a + 2) * wgp Ms (a + 1) (a + 2) := by
  fin_cases a <;> simp [Og, Fin.prod_univ_six, offPair] <;> ring

theorem tr_diag : ∀ a x b : Fin 3, b ≠ x → tr a b = x → x = a ∨ x = a + 1 := by decide

theorem OffBall.pos {M : Fin 3 → Fin 3 → ℝ} {A : ℝ} (hA : 0 < A) (hM : ∀ a b, 0 ≤ M a b)
    (h : OffBall M A) {c d : Fin 3} (hcd : c ≠ d) : 0 < M c d := by
  have h0 := h 0 c d hcd
  rcases (hM c d).eq_or_lt with h' | h'
  · rw [← h'] at h0
    have : (0 : ℝ) < A ^ 600 := pow_pos hA _
    norm_num at h0
    linarith
  · exact h'

theorem offBall_pos : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ),
    (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) → (∀ A ∈ As, 0 < A) → List.Forall₂ OffBall Ms As →
    ∀ M ∈ Ms, ∀ a b, a ≠ b → 0 < M a b
  | [], [], _, _, _ => by simp
  | M :: Ms, A :: As, hM, hA, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    intro M' hM' a b hab
    rcases List.mem_cons.mp hM' with rfl | hmem
    · exact h1.pos (hA A List.mem_cons_self) (hM M' List.mem_cons_self) hab
    · exact offBall_pos Ms As (fun M'' h'' => hM M'' (List.mem_cons_of_mem _ h''))
        (fun A' h'' => hA A' (List.mem_cons_of_mem _ h'')) h2 M' hmem a b hab

/-- The product over the chosen walks of a cell of the family twisted by `tr a`: all walks,
except the alternating walk in the two closed cells. -/
noncomputable def gcell (Ms : List (Fin 3 → Fin 3 → ℝ)) (a x w : Fin 3) : ℝ :=
  if x = w then (if x = a then wgp Ms a a / alt true Ms a else wgp Ms x x / alt false Ms x)
  else wgp Ms x w

/-- **The ball inequality of the path for the family twisted by a transposition.** -/
theorem walks_ball_tr (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (hlen : Even Ms.length)
    (hpos : 0 < Ms.length) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) (a : Fin 3) (j : Fin 6) (c d : Fin 3) :
    ((dN Ms.length : ℝ) * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (tr a (offPair k).2)) ^ 100
        * pw Ms (offPair j).1 (tr a (offPair j).2) ^ 91 * pw Ms c d ^ 9 := by
  obtain ⟨hchild, hmxp⟩ := offBall_prod Ms As hM hA hball
  have hMpos := offBall_pos Ms As hM hA hball
  have hα : 0 < dN Ms.length := by
    obtain ⟨k, hk⟩ : ∃ k, Ms.length = k + 1 := ⟨Ms.length - 1, by omega⟩
    rw [hk]
    exact dN_pos k
  have hs : sN Ms.length = dN Ms.length + 1 := (sN_dN_parity _).1 hlen
  set α := dN Ms.length with hαdef
  have hαr : (0 : ℝ) ≤ (α : ℝ) := Nat.cast_nonneg _
  have hp := pw_nonneg Ms hM
  have hg := wgp_nonneg Ms hM
  -- the two closed cells
  have big : ∀ (s : Bool) (x : Fin 3), (α : ℝ) ^ α * (wgp Ms x x / alt s Ms x) ≤ pw Ms x x ^ α ∧
      wgp Ms x x / alt s Ms x ≤ mxP Ms ^ α := by
    intro s x
    obtain ⟨-, i2, i3, i4⟩ := pw_ub_alt Ms hM s x
    rw [altEnd_even _ s x hlen] at i2 i3 i4
    have hc : cnt Ms.length x x - 1 = α := by
      simp [cnt, hs]
    rw [hc] at i3 i4
    have hal := alt_pos s Ms hMpos x
    constructor
    · rw [← mul_div_assoc, div_le_iff₀ hal]
      refine i3.trans (mul_le_mul_of_nonneg_right ?_ hal.le)
      exact pow_le_pow_left₀ (sub_nonneg.mpr i2) (by linarith) _
    · rw [div_le_iff₀ hal]
      exact i4
  have small : ∀ x w : Fin 3, x ≠ w → (α : ℝ) ^ α * wgp Ms x w ≤ pw Ms x w ^ α ∧
      wgp Ms x w ≤ mxP Ms ^ α := by
    intro x w hxw
    have hc : cnt Ms.length x w = α := by simp [cnt, hxw, hαdef]
    have h1 := pw_ub Ms hM x w
    have h2 := wgp_le Ms hM x w
    rw [hc] at h1 h2
    exact ⟨h1, h2⟩
  have cellb : ∀ k : Fin 6,
      (α : ℝ) ^ α * gcell Ms a (offPair k).1 (tr a (offPair k).2)
        ≤ pw Ms (offPair k).1 (tr a (offPair k).2) ^ α ∧
      gcell Ms a (offPair k).1 (tr a (offPair k).2) ≤ mxP Ms ^ α ∧
      0 ≤ gcell Ms a (offPair k).1 (tr a (offPair k).2) := by
    intro k
    by_cases hxw : (offPair k).1 = tr a (offPair k).2
    · rw [← hxw]
      rcases tr_diag a _ _ (offPair_ne k).symm hxw.symm with hx | hx
      · have e : gcell Ms a (offPair k).1 (offPair k).1
            = wgp Ms (offPair k).1 (offPair k).1 / alt true Ms (offPair k).1 := by
          simp [gcell, hx]
        rw [e]
        exact ⟨(big true _).1, (big true _).2,
          div_nonneg (hg _ _) (alt_nonneg true Ms hM _)⟩
      · have hne : (offPair k).1 ≠ a := by
          rw [hx]
          exact (add_one_ne a).symm
        have e : gcell Ms a (offPair k).1 (offPair k).1
            = wgp Ms (offPair k).1 (offPair k).1 / alt false Ms (offPair k).1 := by
          simp [gcell, hne]
        rw [e]
        exact ⟨(big false _).1, (big false _).2,
          div_nonneg (hg _ _) (alt_nonneg false Ms hM _)⟩
    · have e : gcell Ms a (offPair k).1 (tr a (offPair k).2)
          = wgp Ms (offPair k).1 (tr a (offPair k).2) := by
        simp [gcell, hxw]
      rw [e]
      exact ⟨(small _ _ hxw).1, (small _ _ hxw).2, hg _ _⟩
  -- the chosen walks use every pair equally often
  have hbal : ∏ k : Fin 6, gcell Ms a (offPair k).1 (tr a (offPair k).2) = up Ms α := by
    rw [prod_tr a (gcell Ms a), ← Og_eq Ms, Og_tr Ms a]
    have hA1 := alt_pos true Ms hMpos a
    have hA2 := alt_pos false Ms hMpos (a + 1)
    have i := (alt_bal Ms a).1 hlen
    have e1 : gcell Ms a a a = wgp Ms a a / alt true Ms a := by simp [gcell]
    have e2 : gcell Ms a (a + 1) (a + 1) = wgp Ms (a + 1) (a + 1) / alt false Ms (a + 1) := by
      simp [gcell, (add_one_ne a).symm]
    have e3 : gcell Ms a (a + 2) a = wgp Ms (a + 2) a := by
      simp [gcell, (add_two_ne a).symm]
    have e4 : gcell Ms a (a + 2) (a + 1) = wgp Ms (a + 2) (a + 1) := by
      have : a + 2 ≠ a + 1 := by fin_cases a <;> decide
      simp [gcell, this]
    have e5 : gcell Ms a a (a + 2) = wgp Ms a (a + 2) := by simp [gcell, add_two_ne a]
    have e6 : gcell Ms a (a + 1) (a + 2) = wgp Ms (a + 1) (a + 2) := by
      have : a + 1 ≠ a + 2 := by fin_cases a <;> decide
      simp [gcell, this]
    rw [e1, e2, e3, e4, e5, e6]
    field_simp
    linear_combination (wgp Ms (a + 2) a * wgp Ms (a + 2) (a + 1) * wgp Ms a (a + 2)
      * wgp Ms (a + 1) (a + 2)) * i
  refine sel_assembly hα (p := fun k => pw Ms (offPair k).1 (tr a (offPair k).2))
    (Γ := fun k => gcell Ms a (offPair k).1 (tr a (offPair k).2)) (Uα := up Ms α)
    (U100 := up Ms 100) (mnp := mnP Ms) (mxp := mxP Ms)
    (fun k => hp _ _) (fun k => (cellb k).2.2) (fun k => (cellb k).1) hbal
    (fun k => (cellb k).2.1) ?_ hchild ?_ hmxp (mnP_nonneg Ms hM)
    (List.prod_nonneg fun A hA' => (hA A hA').le) j
  · refine le_trans ?_ (pw_ge Ms hM c d)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast cnt_ge _ hlen c d) (mnP_nonneg Ms hM)
  · rw [← up_mul, ← up_mul, mul_comm]

/-! ### All families -/

theorem inj_cases : ∀ σ : Fin 3 → Fin 3, Function.Injective σ →
    σ = id ∨ σ = (· + 1) ∨ σ = (· + 2) ∨ ∃ a, σ = tr a := by decide

/-- **The ball inequalities of a path of `h + h` steps, `h ≥ 2`**, for the six cells
`(a, σ b)`, `a ≠ b`, of any bijection `σ`, weight being moved to any cell. -/
theorem walks_ball (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (h : ℕ) (hh : 2 ≤ h)
    (hlen : Ms.length = h + h) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ)
    (j : Fin 6) (c d : Fin 3) :
    ((dN Ms.length : ℝ) * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (σ (offPair k).2)) ^ 100
        * pw Ms (offPair j).1 (σ (offPair j).2) ^ 91 * pw Ms c d ^ 9 := by
  have hev : Even Ms.length := ⟨h, hlen⟩
  have hpos : 0 < Ms.length := by omega
  rcases inj_cases σ hσ with rfl | rfl | rfl | ⟨a, rfl⟩
  · exact walks_ball_id Ms As hev hpos hM hA hball j c d
  · exact walks_ball_rot1 Ms As h hh hlen hM hA hball j c d
  · exact walks_ball_rot2 Ms As h hh hlen hM hA hball j c d
  · exact walks_ball_tr Ms As hev hpos hM hA hball a j c d

end Outerplanar
