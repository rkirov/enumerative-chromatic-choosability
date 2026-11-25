/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.LongDesign8

/-!
# Walk designs with integer multiplicities

A general form of the assembly of `Outerplanar/Walks.lean`. Each of the six cells `(a, σ b)`,
`a ≠ b`, of a root family receives integer multiplicities on its walks (`dfam`). They all have the
same total `e`, and every pair of different indices is used `e` times at every step (`Balanced`, a
decidable statement about the multiplicities only). Then:

* `pw_eq_cw` — the walk sum `pw` is the sum over the explicit list of walks `cw n a b`;
* `amgm_list` — weighted AM–GM over a list: the cell `k` gets the constant
  `N_k = e / (∏ c^c)^(1/e)`;
* `famProd_up` — balance: the product over all cells of the walk products to the powers of the
  multiplicities is `up Ms e`;
* `design_assembly` — the assembly with one constant per cell. The weight `9/600` that moves to an
  arbitrary cell is charged crudely, as in `mid_assembly`, at the walk count `γ` of the receiving
  cell;
* **`walks_ball_design`** — the resulting ball inequalities of the path, with the constant `T`,
  under `T^600 ≤ (∏_{k ≠ j} N_k)^100 N_j^91 γ^9` for every `j`.

`Outerplanar/LongDesign6.lean` applies this to faces of length six with certificates found by a
maximum-entropy program. Part of the formalization of the long-face designs of the research note
`ai_research_notes/OUTERPLANAR_BRANCHING_SQUARES_2026-11-23.md` (another AI session of this
repository's collaboration); formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### Walks as lists -/

/-- The walks of `n` steps from `a`: the lists of the indices after `a`. -/
def wlk : ℕ → Fin 3 → List (List (Fin 3))
  | 0, _ => [[]]
  | n + 1, a => (wlk n (a + 1)).map (List.cons (a + 1)) ++ (wlk n (a + 2)).map (List.cons (a + 2))

/-- The end of a walk. -/
def wEnd : Fin 3 → List (Fin 3) → Fin 3
  | a, [] => a
  | _, x :: xs => wEnd x xs

/-- The walks of `n` steps from `a` to `b`. -/
def cw (n : ℕ) (a b : Fin 3) : List (List (Fin 3)) := (wlk n a).filter fun w => wEnd a w = b

/-- The product of the table entries along a walk. -/
noncomputable def wpr : List (Fin 3 → Fin 3 → ℝ) → Fin 3 → List (Fin 3) → ℝ
  | M :: Ms, a, x :: xs => M a x * wpr Ms x xs
  | _, _, _ => 1

theorem wpr_nil (a : Fin 3) (w : List (Fin 3)) : wpr [] a w = 1 := by
  cases w <;> rfl

theorem sum_cons_walks (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ)) (a x b : Fin 3)
    (l : List (List (Fin 3))) :
    (((l.map (List.cons x)).filter fun w => wEnd a w = b).map (wpr (M :: Ms) a)).sum
      = M a x * ((l.filter fun w => wEnd x w = b).map (wpr Ms x)).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    by_cases h : wEnd x w = b
    · simp only [List.map_cons, List.filter_cons, show wEnd a (x :: w) = b from h, decide_true,
        ite_true, List.map_cons, List.sum_cons, h] at ih ⊢
      rw [ih, wpr]
      ring
    · simp only [List.map_cons, List.filter_cons, show ¬ wEnd a (x :: w) = b from h,
        decide_false, h] at ih ⊢
      simpa using ih

/-- **The walk sum is the sum over the list of walks.** -/
theorem pw_eq_cw : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)) (a b : Fin 3),
    pw Ms a b = ((cw Ms.length a b).map (wpr Ms a)).sum
  | [], a, b => by
    by_cases h : a = b
    · subst h; simp [pw, cw, wlk, wEnd, wpr]
    · simp [pw, cw, wlk, wEnd, wpr, h]
  | M :: Ms, a, b => by
    rw [pw, pw_eq_cw Ms (a + 1) b, pw_eq_cw Ms (a + 2) b, List.length_cons]
    simp only [cw, wlk, List.filter_append, List.map_append, List.sum_append]
    rw [sum_cons_walks, sum_cons_walks]

/-- A walk whose steps change the index. -/
def wValid : Fin 3 → List (Fin 3) → Prop
  | _, [] => True
  | a, x :: xs => x ≠ a ∧ wValid x xs

theorem mem_wlk : ∀ (n : ℕ) (a : Fin 3) (w : List (Fin 3)), w ∈ wlk n a → w.length = n ∧ wValid a w
  | 0, a, w, h => by
    simp only [wlk, List.mem_singleton] at h
    subst h
    exact ⟨rfl, trivial⟩
  | n + 1, a, w, h => by
    simp only [wlk, List.mem_append, List.mem_map] at h
    rcases h with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
    · obtain ⟨h1, h2⟩ := mem_wlk n _ w' hw'
      exact ⟨by simp [h1], (add_one_ne a).symm, h2⟩
    · obtain ⟨h1, h2⟩ := mem_wlk n _ w' hw'
      exact ⟨by simp [h1], (add_two_ne a).symm, h2⟩

theorem mem_cw {n : ℕ} {a b : Fin 3} {w : List (Fin 3)} (h : w ∈ cw n a b) :
    w.length = n ∧ wValid a w :=
  mem_wlk n a w (List.mem_filter.mp h).1

theorem wpr_nonneg : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a w, 0 ≤ wpr Ms a w
  | [], _, a, w => by rw [wpr_nil]; exact zero_le_one
  | M :: Ms, h, a, [] => zero_le_one
  | M :: Ms, h, a, x :: xs => by
    rw [wpr]
    exact mul_nonneg (h M List.mem_cons_self _ _)
      (wpr_nonneg Ms (fun M' hM' => h M' (List.mem_cons_of_mem _ hM')) x xs)

theorem wpr_le : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) →
    ∀ a w, w.length = Ms.length → wValid a w → wpr Ms a w ≤ mxP Ms
  | [], _, a, w, _, _ => by rw [wpr_nil]; simp [mxP]
  | M :: Ms, _, a, [], h, _ => by simp at h
  | M :: Ms, h, a, x :: xs, hl, hv => by
    have hMs : ∀ M' ∈ Ms, ∀ a b, 0 ≤ M' a b := fun M' hM' => h M' (List.mem_cons_of_mem _ hM')
    have hM := h M List.mem_cons_self
    rw [wpr, mxP_cons]
    exact mul_le_mul (le_mx M (Ne.symm hv.1)) (wpr_le Ms hMs x xs (by simpa using hl) hv.2)
      (wpr_nonneg Ms hMs x xs) (mx_nonneg hM)

/-! ### Weighted AM–GM over a list -/

theorem mem_zipWith' {α β γ : Type*} (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β) (z : γ), z ∈ List.zipWith f l₁ l₂ →
      ∃ a ∈ l₁, ∃ b ∈ l₂, z = f a b
  | [], _, z, h => by simp at h
  | _ :: _, [], z, h => by simp at h
  | a :: l₁, b :: l₂, z, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, b, List.mem_cons_self, rfl⟩
    · obtain ⟨a', ha', b', hb', rfl⟩ := mem_zipWith' f l₁ l₂ z h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', rfl⟩

theorem zipWith_pow_nonneg {α : Type*} (f : α → ℝ) (ws : List α) (cs : List ℕ)
    (hf : ∀ w ∈ ws, 0 ≤ f w) : 0 ≤ (List.zipWith (fun w c => f w ^ c) ws cs).prod :=
  List.prod_nonneg fun y hy => by
    obtain ⟨z, hz, c', -, rfl⟩ := mem_zipWith' _ ws cs y hy
    exact pow_nonneg (hf z hz) _

theorem prod_pow_self_nonneg (cs : List ℕ) : 0 ≤ (cs.map fun c : ℕ => (c : ℝ) ^ c).prod :=
  List.prod_nonneg fun y hy => by
    obtain ⟨c', -, rfl⟩ := List.mem_map.mp hy
    exact (pow_self_pos c').le

/-- **Weighted AM–GM over a list**, cleared of denominators. -/
theorem amgm_list : ∀ (xs : List ℝ) (cs : List ℕ), xs.length = cs.length → (∀ x ∈ xs, 0 ≤ x) →
    ((cs.sum : ℕ) : ℝ) ^ cs.sum * (List.zipWith (fun x c => x ^ c) xs cs).prod
      ≤ (cs.map fun c : ℕ => (c : ℝ) ^ c).prod * xs.sum ^ cs.sum
  | [], [], _, _ => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, c :: cs, h, h0 => by
    have ih := amgm_list xs cs (by simpa using h) fun y hy => h0 y (List.mem_cons_of_mem _ hy)
    have hx := h0 x List.mem_cons_self
    have hX : 0 ≤ xs.sum := List.sum_nonneg fun y hy => h0 y (List.mem_cons_of_mem _ hy)
    have h2 := amgm2 hx hX c cs.sum
    simp only [List.sum_cons, List.zipWith_cons_cons, List.prod_cons, List.map_cons]
    set C := cs.sum
    set P := (List.zipWith (fun x c => x ^ c) xs cs).prod
    set Q := (cs.map fun c : ℕ => (c : ℝ) ^ c).prod
    have hP : 0 ≤ P := zipWith_pow_nonneg id xs cs fun y hy => h0 y (List.mem_cons_of_mem _ hy)
    have hQ : 0 ≤ Q := prod_pow_self_nonneg cs
    have hCC := pow_self_pos C
    have hcC : (0 : ℝ) ≤ ((c + C : ℕ) : ℝ) ^ (c + C) := (pow_self_pos _).le
    refine le_of_mul_le_mul_right ?_ hCC
    calc ((c + C : ℕ) : ℝ) ^ (c + C) * (x ^ c * P) * (C : ℝ) ^ C
        = ((c + C : ℕ) : ℝ) ^ (c + C) * x ^ c * ((C : ℝ) ^ C * P) := by ring
      _ ≤ ((c + C : ℕ) : ℝ) ^ (c + C) * x ^ c * (Q * xs.sum ^ C) :=
          mul_le_mul_of_nonneg_left ih (mul_nonneg hcC (pow_nonneg hx _))
      _ = Q * (((c + C : ℕ) : ℝ) ^ (c + C) * (x ^ c * xs.sum ^ C)) := by ring
      _ ≤ Q * ((c : ℝ) ^ c * (C : ℝ) ^ C * (x + xs.sum) ^ (c + C)) :=
          mul_le_mul_of_nonneg_left h2 hQ
      _ = (c : ℝ) ^ c * Q * (x + xs.sum) ^ (c + C) * (C : ℝ) ^ C := by ring

theorem zip_pow_le (f : List (Fin 3) → ℝ) {X : ℝ} (hX : 0 ≤ X) :
    ∀ (ws : List (List (Fin 3))) (cs : List ℕ), ws.length = cs.length →
      (∀ w ∈ ws, 0 ≤ f w ∧ f w ≤ X) →
      (List.zipWith (fun w c => f w ^ c) ws cs).prod ≤ X ^ cs.sum
  | [], [], _, _ => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | w :: ws, c :: cs, h, hf => by
    have ih := zip_pow_le f hX ws cs (by simpa using h) fun w' hw' =>
      hf w' (List.mem_cons_of_mem _ hw')
    obtain ⟨h0, h1⟩ := hf w List.mem_cons_self
    simp only [List.zipWith_cons_cons, List.prod_cons, List.sum_cons, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ h0 h1 c) ih
      (zipWith_pow_nonneg f ws cs fun z hz => (hf z (List.mem_cons_of_mem _ hz)).1)
      (pow_nonneg hX _)

theorem cast_prod_pow (cs : List ℕ) :
    (((cs.map fun c => c ^ c).prod : ℕ) : ℝ) = (cs.map fun c : ℕ => (c : ℝ) ^ c).prod := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

/-! ### Balance -/

/-- A family of walks with multiplicities: start, walk, multiplicity. -/
abbrev Fam := List (Fin 3 × List (Fin 3) × ℕ)

/-- The product over a family of the walk products to the powers of the multiplicities. -/
noncomputable def famProd (Ms : List (Fin 3 → Fin 3 → ℝ)) (F : Fam) : ℝ :=
  (F.map fun t => wpr Ms t.1 t.2.1 ^ t.2.2).prod

/-- How often the first step of a family uses the pair `(x, y)`. -/
def use0 (F : Fam) (x y : Fin 3) : ℕ :=
  (F.map fun t => if t.1 = x ∧ t.2.1.head? = some y then t.2.2 else 0).sum

/-- The family after its first step. -/
def fshift (F : Fam) : Fam := F.map fun t => (t.2.1.headD t.1, t.2.1.tail, t.2.2)

/-- **Balance**: at every step every pair of different indices is used `e` times. -/
def Balanced (F : Fam) (n e : ℕ) : Prop :=
  ∀ t < n, ∀ k : Fin 6, use0 (fshift^[t] F) (offPair k).1 (offPair k).2 = e

instance (F : Fam) (n e : ℕ) : Decidable (Balanced F n e) := by
  unfold Balanced; infer_instance

/-- All walks of a family have `n` steps and change the index at every step. -/
def FamOK (F : Fam) (n : ℕ) : Prop := ∀ t ∈ F, t.2.1.length = n ∧ wValid t.1 t.2.1

theorem prod_offPair_single (g : Fin 3 → Fin 3 → ℝ) {a y : Fin 3} (hay : y ≠ a) (c : ℕ) :
    ∏ k : Fin 6, g (offPair k).1 (offPair k).2 ^
        (if a = (offPair k).1 ∧ some y = some (offPair k).2 then c else 0) = g a y ^ c := by
  fin_cases a <;> fin_cases y <;> first | exact absurd rfl hay | simp [Fin.prod_univ_six, offPair]

theorem famProd_cons (M : Fin 3 → Fin 3 → ℝ) (Ms : List (Fin 3 → Fin 3 → ℝ)) :
    ∀ F : Fam, (∀ t ∈ F, ∃ y ys, t.2.1 = y :: ys ∧ y ≠ t.1) →
      famProd (M :: Ms) F = (∏ k : Fin 6, M (offPair k).1 (offPair k).2 ^
        use0 F (offPair k).1 (offPair k).2) * famProd Ms (fshift F)
  | [], _ => by simp [famProd, use0, fshift]
  | t :: F, h => by
    obtain ⟨y, ys, hw, hy⟩ := h t List.mem_cons_self
    have ih := famProd_cons M Ms F fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    obtain ⟨a, w, c⟩ := t
    simp only at hw hy
    subst hw
    have e1 : famProd (M :: Ms) ((a, y :: ys, c) :: F)
        = (M a y * wpr Ms y ys) ^ c * famProd (M :: Ms) F := by
      simp [famProd, wpr]
    have e2 : famProd Ms (fshift ((a, y :: ys, c) :: F)) = wpr Ms y ys ^ c * famProd Ms (fshift F) := by
      simp [famProd, fshift]
    have e3 : ∀ k : Fin 6, use0 ((a, y :: ys, c) :: F) (offPair k).1 (offPair k).2
        = (if a = (offPair k).1 ∧ some y = some (offPair k).2 then c else 0)
          + use0 F (offPair k).1 (offPair k).2 := fun k => by
      simp [use0]
    rw [e1, e2, ih]
    simp only [e3, pow_add, Finset.prod_mul_distrib, prod_offPair_single M hy c]
    ring

theorem famOK_shift {F : Fam} {n : ℕ} (h : FamOK F (n + 1)) : FamOK (fshift F) n := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  obtain ⟨hl, hv⟩ := h t' ht'
  obtain ⟨a, w, c⟩ := t'
  cases w with
  | nil => simp at hl
  | cons y ys => exact ⟨by simpa using hl, hv.2⟩

/-- **A balanced family uses every pair `e` times at every step.** -/
theorem famProd_up (e : ℕ) : ∀ (Ms : List (Fin 3 → Fin 3 → ℝ)) (F : Fam), FamOK F Ms.length →
    Balanced F Ms.length e → famProd Ms F = up Ms e
  | [], F, _, _ => by
    simp [famProd, up, wpr_nil]
  | M :: Ms, F, hok, hbal => by
    have hstep : ∀ t ∈ F, ∃ y ys, t.2.1 = y :: ys ∧ y ≠ t.1 := fun t ht => by
      obtain ⟨hl, hv⟩ := hok t ht
      obtain ⟨a, w, c⟩ := t
      cases w with
      | nil => simp at hl
      | cons y ys => exact ⟨y, ys, rfl, hv.1⟩
    rw [famProd_cons M Ms F hstep, up_cons]
    have h0 : ∀ k : Fin 6, use0 F (offPair k).1 (offPair k).2 = e := fun k =>
      hbal 0 (by simp) k
    simp only [h0]
    rw [Finset.prod_pow, famProd_up e Ms (fshift F) (famOK_shift hok) fun t ht k => by
      have := hbal (t + 1) (by simp at ht ⊢; omega) k
      rwa [Function.iterate_succ_apply] at this]
    rfl

/-! ### The design of a root family -/

/-- The family of a design: the walks of the cell `k` with the multiplicities `ns k`. -/
def dfam (n : ℕ) (σ : Fin 3 → Fin 3) (ns : Fin 6 → List ℕ) : Fam :=
  (List.finRange 6).flatMap fun k =>
    List.zipWith (fun w c => ((offPair k).1, w, c)) (cw n (offPair k).1 (σ (offPair k).2)) (ns k)

/-- The product over the walks of the cell `k`. -/
noncomputable def dΓ (Ms : List (Fin 3 → Fin 3 → ℝ)) (σ : Fin 3 → Fin 3) (ns : Fin 6 → List ℕ)
    (k : Fin 6) : ℝ :=
  (List.zipWith (fun w c => wpr Ms (offPair k).1 w ^ c)
    (cw Ms.length (offPair k).1 (σ (offPair k).2)) (ns k)).prod

theorem famProd_dfam (Ms : List (Fin 3 → Fin 3 → ℝ)) (σ : Fin 3 → Fin 3) (ns : Fin 6 → List ℕ) :
    famProd Ms (dfam Ms.length σ ns) = ∏ k, dΓ Ms σ ns k := by
  rw [Fin.prod_univ_def, famProd, dfam, List.flatMap_def, List.map_flatten, List.prod_flatten,
    List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, List.map_zipWith]
  rfl

theorem famOK_dfam (n : ℕ) (σ : Fin 3 → Fin 3) (ns : Fin 6 → List ℕ) : FamOK (dfam n σ ns) n := by
  intro t ht
  simp only [dfam, List.mem_flatMap] at ht
  obtain ⟨k, -, hk⟩ := ht
  obtain ⟨w, hw, c, -, rfl⟩ := mem_zipWith' _ _ _ t hk
  exact mem_cw hw

/-! ### Assembly with one constant per cell -/

/-- **Assembly for a design with one constant per cell.** -/
theorem design_assembly {e : ℕ} (he : 0 < e) {N : Fin 6 → ℝ} (hN : ∀ k, 0 ≤ N k) {T γ : ℝ}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) {p Γ : Fin 6 → ℝ} {pmv AP Uα U100 mnp mxp : ℝ}
    (hp : ∀ k, 0 ≤ p k) (hΓ : ∀ k, 0 ≤ Γ k) (hub : ∀ k, N k ^ e * Γ k ≤ p k ^ e)
    (hbal : ∏ k, Γ k = Uα) (hΓle : ∀ k, Γ k ≤ mxp ^ e) (hmv : γ * mnp ≤ pmv)
    (hchild : AP ^ 600 * mxp ^ 9 ≤ U100 * mnp ^ 9) (hU : Uα ^ 100 = U100 ^ e)
    (hmxp : 0 < mxp) (hmnp : 0 ≤ mnp) (hAP : 0 ≤ AP) (j : Fin 6)
    (hfin : T ^ 600 ≤ (∏ k ∈ univ.erase j, N k) ^ 100 * N j ^ 91 * γ ^ 9) :
    (T * AP) ^ 600 ≤ (∏ k ∈ univ.erase j, p k) ^ 100 * p j ^ 91 * pmv ^ 9 := by
  set G' := ∏ k ∈ univ.erase j, Γ k with hG'
  set NP := ∏ k ∈ univ.erase j, N k with hNP
  have hNP0 : 0 ≤ NP := prod_nonneg fun k _ => hN k
  have hG'0 : 0 ≤ G' := prod_nonneg fun k _ => hΓ k
  have hsplit : Γ j * G' = Uα := by
    rw [← hbal]
    exact Finset.mul_prod_erase univ Γ (mem_univ j)
  have hpmv : 0 ≤ pmv := (mul_nonneg hγ hmnp).trans hmv
  have h1 : AP ^ (600 * e) * mxp ^ (9 * e)
      ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e) * mxp ^ (9 * e) :=
    calc AP ^ (600 * e) * mxp ^ (9 * e) = (AP ^ 600 * mxp ^ 9) ^ e := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ (U100 * mnp ^ 9) ^ e :=
          pow_le_pow_left₀ (mul_nonneg (pow_nonneg hAP _) (pow_nonneg hmxp.le _)) hchild e
      _ = Uα ^ 100 * mnp ^ (9 * e) := by rw [mul_pow, ← hU, ← pow_mul]
      _ = G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e) * Γ j ^ 9 := by rw [← hsplit]; ring
      _ ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e) * mxp ^ (9 * e) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (pow_nonneg hG'0 _)
            (pow_nonneg (hΓ j) _)) (pow_nonneg hmnp _))
          calc Γ j ^ 9 ≤ (mxp ^ e) ^ 9 := pow_le_pow_left₀ (hΓ j) (hΓle j) 9
            _ = mxp ^ (9 * e) := by rw [← pow_mul, mul_comm]
  have h2 : AP ^ (600 * e) ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e) :=
    le_of_mul_le_mul_right h1 (pow_pos hmxp _)
  have h3 : NP ^ e * G' ≤ (∏ k ∈ univ.erase j, p k) ^ e := by
    rw [hNP, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun k _ => mul_nonneg (pow_nonneg (hN k) _) (hΓ k))
      fun k _ => hub k
  have h4 : (γ * mnp) ^ e ≤ pmv ^ e := pow_le_pow_left₀ (mul_nonneg hγ hmnp) hmv e
  have hX : ((T * AP) ^ 600) ^ e
      ≤ ((∏ k ∈ univ.erase j, p k) ^ 100 * p j ^ 91 * pmv ^ 9) ^ e :=
    calc ((T * AP) ^ 600) ^ e = (T ^ 600) ^ e * AP ^ (600 * e) := by
          ring
      _ ≤ (NP ^ 100 * N j ^ 91 * γ ^ 9) ^ e * (G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e)) :=
          mul_le_mul (pow_le_pow_left₀ (pow_nonneg hT _) hfin e) h2 (pow_nonneg hAP _)
            (pow_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hNP0 _) (pow_nonneg (hN j) _))
              (pow_nonneg hγ _)) _)
      _ = (NP ^ e * G') ^ 100 * (N j ^ e * Γ j) ^ 91 * ((γ * mnp) ^ e) ^ 9 := by
          ring
      _ ≤ ((∏ k ∈ univ.erase j, p k) ^ e) ^ 100 * (p j ^ e) ^ 91 * (pmv ^ e) ^ 9 := by
          refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hNP0 _) hG'0)
            h3 _) (pow_le_pow_left₀ (mul_nonneg (pow_nonneg (hN j) _) (hΓ j)) (hub j) _)
            (pow_nonneg (mul_nonneg (pow_nonneg (hN j) _) (hΓ j)) _)
            (pow_nonneg (pow_nonneg (prod_nonneg fun k _ => hp k) _) _))
            (pow_le_pow_left₀ (pow_nonneg (mul_nonneg hγ hmnp) _) h4 _)
            (pow_nonneg (pow_nonneg (mul_nonneg hγ hmnp) _) _)
            (mul_nonneg (pow_nonneg (pow_nonneg (prod_nonneg fun k _ => hp k) _) _)
              (pow_nonneg (pow_nonneg (hp j) _) _))
      _ = _ := by ring
  exact le_of_pow_le_pow_left₀ he.ne' (mul_nonneg (mul_nonneg (pow_nonneg
    (prod_nonneg fun k _ => hp k) _) (pow_nonneg (hp j) _)) (pow_nonneg hpmv _)) hX

/-! ### The ball inequalities from a design -/

/-- **The ball inequalities of a path from a balanced design.** The cell `k` gets the constant
`num k / D`, certified by `num k ^ e · ∏ c^c ≤ e^e D^e`. -/
theorem walks_ball_design (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ)
    (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) (σ : Fin 3 → Fin 3) (ns : Fin 6 → List ℕ) (e : ℕ)
    (he : 0 < e) (num : Fin 6 → ℕ) (D : ℕ) (hD : 0 < D) {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 ≤ γ)
    (hlen : ∀ k, (cw Ms.length (offPair k).1 (σ (offPair k).2)).length = (ns k).length)
    (hsum : ∀ k, (ns k).sum = e) (hbal : Balanced (dfam Ms.length σ ns) Ms.length e)
    (hhub : ∀ k, num k ^ e * ((ns k).map fun c => c ^ c).prod ≤ e ^ e * D ^ e)
    (hfin : ∀ j, T ^ 600 ≤ (∏ k ∈ univ.erase j, ((num k : ℝ) / D)) ^ 100
      * ((num j : ℝ) / D) ^ 91 * γ ^ 9)
    (hγc : ∀ c d, γ ≤ cnt Ms.length c d) (j : Fin 6) (c d : Fin 3) :
    (T * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (σ (offPair k).2)) ^ 100
        * pw Ms (offPair j).1 (σ (offPair j).2) ^ 91 * pw Ms c d ^ 9 := by
  obtain ⟨hchild, hmxp⟩ := offBall_prod Ms As hM hA hball
  have hp := pw_nonneg Ms hM
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hw0 := wpr_nonneg Ms hM
  have hΓ0 : ∀ k, 0 ≤ dΓ Ms σ ns k := fun k => zipWith_pow_nonneg _ _ _ fun w _ => hw0 _ w
  refine design_assembly (e := e) he (N := fun k => (num k : ℝ) / D) (fun k => by positivity)
    hT hγ (p := fun k => pw Ms (offPair k).1 (σ (offPair k).2)) (Γ := dΓ Ms σ ns)
    (Uα := up Ms e) (U100 := up Ms 100) (mnp := mnP Ms) (mxp := mxP Ms) (fun k => hp _ _) hΓ0
    (fun k => ?_) ?_ (fun k => ?_) ?_ hchild ?_ hmxp (mnP_nonneg _ hM)
    (List.prod_nonneg fun A hA' => (hA A hA').le) j (hfin j)
  · -- AM–GM in the cell
    set l := cw Ms.length (offPair k).1 (σ (offPair k).2)
    have key := amgm_list (l.map (wpr Ms (offPair k).1)) (ns k) (by rw [List.length_map, hlen k])
      fun x hx => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
        exact hw0 _ w
    rw [List.zipWith_map_left, hsum k, ← pw_eq_cw] at key
    set Q := ((ns k).map fun c : ℕ => (c : ℝ) ^ c).prod
    have hQ : 0 ≤ Q := prod_pow_self_nonneg _
    have hh : ((num k : ℝ) / D) ^ e * Q ≤ (e : ℝ) ^ e := by
      have := hhub k
      have hcast : ((((ns k).map fun c => c ^ c).prod : ℕ) : ℝ) = Q := cast_prod_pow _
      have h' : (num k : ℝ) ^ e * Q ≤ (e : ℝ) ^ e * (D : ℝ) ^ e := by
        rw [← hcast]; exact_mod_cast this
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hDr e)]
      exact h'
    have hee : (0 : ℝ) < (e : ℝ) ^ e := pow_pos (by exact_mod_cast he) e
    refine le_of_mul_le_mul_left ?_ hee
    calc (e : ℝ) ^ e * (((num k : ℝ) / D) ^ e * dΓ Ms σ ns k)
        = ((num k : ℝ) / D) ^ e * ((e : ℝ) ^ e * dΓ Ms σ ns k) := by ring
      _ ≤ ((num k : ℝ) / D) ^ e * (Q * pw Ms (offPair k).1 (σ (offPair k).2) ^ e) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = (((num k : ℝ) / D) ^ e * Q) * pw Ms (offPair k).1 (σ (offPair k).2) ^ e := by ring
      _ ≤ (e : ℝ) ^ e * pw Ms (offPair k).1 (σ (offPair k).2) ^ e :=
          mul_le_mul_of_nonneg_right hh (pow_nonneg (hp _ _) _)
  · -- balance
    rw [← famProd_dfam]
    exact famProd_up e Ms _ (famOK_dfam _ σ ns) hbal
  · -- a cell weighs at most the product of the largest entries
    rw [← hsum k]
    exact zip_pow_le _ (mxP_nonneg Ms hM) _ _ (hlen k) fun w hw =>
      ⟨hw0 _ w, wpr_le Ms hM _ w (mem_cw hw).1 (mem_cw hw).2⟩
  · exact (mul_le_mul_of_nonneg_right (hγc c d) (mnP_nonneg _ hM)).trans (pw_ge _ hM c d)
  · rw [← up_mul, ← up_mul, mul_comm]

end Outerplanar
