import GridGen.PolymerWalkTree

/-!
# Parity-sensitive walk-tree budgets from a numeric certificate

Even and odd masses are the half-sum and half-difference at `x` and `-x`. A `ParityCert`
packages the only numerical facts the polymer argument uses: a branch majorant `(e, o)`
stable under `D - 1` child ports, a root odd-mass bound `r` for `D` ports, and `2eo < 1`.
Every concrete threshold (degree four at `20`, subcubic at `15`, the uniform `5.67Δ`)
is an instance.
-/

namespace GridGen.Polymer

open Finset

noncomputable def parityProductEven {ι : Type*} (s : Finset ι) (e o : ι → ℝ) : ℝ :=
  ((∏ i ∈ s, (e i + o i)) + ∏ i ∈ s, (e i - o i)) / 2

noncomputable def parityProductOdd {ι : Type*} (s : Finset ι) (e o : ι → ℝ) : ℝ :=
  ((∏ i ∈ s, (e i + o i)) - ∏ i ∈ s, (e i - o i)) / 2

def parityPower (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => (a * (parityPower a b n).1 + b * (parityPower a b n).2,
      b * (parityPower a b n).1 + a * (parityPower a b n).2)

theorem parityProduct_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (e o : ι → ℝ) {i : ι} (hi : i ∉ s) :
    parityProductEven (insert i s) e o =
      e i * parityProductEven s e o + o i * parityProductOdd s e o ∧
    parityProductOdd (insert i s) e o =
      o i * parityProductEven s e o + e i * parityProductOdd s e o := by
  simp only [parityProductEven, parityProductOdd, prod_insert hi]
  constructor <;> ring

theorem parityProduct_bounds {ι : Type*} (s : Finset ι) (e o : ι → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : ∀ i ∈ s, 0 ≤ e i ∧ e i ≤ a)
    (ho : ∀ i ∈ s, 0 ≤ o i ∧ o i ≤ b) :
    (0 ≤ parityProductEven s e o ∧
      parityProductEven s e o ≤ (parityPower a b s.card).1) ∧
    (0 ≤ parityProductOdd s e o ∧
      parityProductOdd s e o ≤ (parityPower a b s.card).2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [parityProductEven, parityProductOdd, parityPower]
  | @insert i s hi ih =>
    have hh := ih (fun j hj => he j (mem_insert_of_mem hj))
      (fun j hj => ho j (mem_insert_of_mem hj))
    have hei := he i (mem_insert_self _ _)
    have hoi := ho i (mem_insert_self _ _)
    rw [(parityProduct_insert s e o hi).1, (parityProduct_insert s e o hi).2,
      card_insert_of_notMem hi]
    dsimp only [parityPower]
    exact ⟨⟨add_nonneg (mul_nonneg hei.1 hh.1.1) (mul_nonneg hoi.1 hh.2.1),
      add_le_add (mul_le_mul hei.2 hh.1.2 hh.1.1 ha)
        (mul_le_mul hoi.2 hh.2.2 hh.2.1 hb)⟩,
      ⟨add_nonneg (mul_nonneg hoi.1 hh.1.1) (mul_nonneg hei.1 hh.2.1),
      add_le_add (mul_le_mul hoi.2 hh.1.2 hh.1.1 hb)
        (mul_le_mul hei.2 hh.2.2 hh.2.1 ha)⟩⟩

theorem parityPower_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ (parityPower a b n).1 ∧ 0 ≤ (parityPower a b n).2 := by
  induction n with
  | zero => norm_num [parityPower]
  | succ n ih =>
    exact ⟨add_nonneg (mul_nonneg ha ih.1) (mul_nonneg hb ih.2),
      add_nonneg (mul_nonneg hb ih.1) (mul_nonneg ha ih.2)⟩

/-- Once an optional child always contributes at least `1`, more ports only add mass. -/
theorem parityPower_mono {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) {m n : ℕ} (hmn : m ≤ n) :
    (parityPower a b m).1 ≤ (parityPower a b n).1 ∧
      (parityPower a b m).2 ≤ (parityPower a b n).2 := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ n _ ih =>
    have h := parityPower_nonneg (a := a) (by linarith) hb n
    have h₁ := mul_le_mul_of_nonneg_right ha h.1
    have h₂ := mul_le_mul_of_nonneg_right ha h.2
    exact ⟨by dsimp only [parityPower]; nlinarith [mul_nonneg hb h.2],
      by dsimp only [parityPower]; nlinarith [mul_nonneg hb h.1]⟩

/-- Numerical data certifying the parity polymer argument for maximum degree `D` and every
activity `x ≤ x₀`: branches (at most `D - 1` child ports) have even and odd masses at most
`e` and `o`, a root (at most `D` ports) has odd mass at most `r`, and `2eo < 1` bounds the
odd mass on either side of an anchor edge, strictly, so that a slack `1 - 2eo` survives. -/
structure ParityCert (D : ℕ) (x₀ e o r : ℝ) : Prop where
  x₀_nonneg : 0 ≤ x₀
  e_nonneg : 0 ≤ e
  o_nonneg : 0 ≤ o
  branch : (parityPower (1 + x₀ * o) (x₀ * e) (D - 1)).1 ≤ e ∧
    (parityPower (1 + x₀ * o) (x₀ * e) (D - 1)).2 ≤ o
  root : (parityPower (1 + x₀ * o) (x₀ * e) D).2 ≤ r
  edge : 2 * e * o < 1

/-- The parity product over at most `n` optional children whose masses are dominated by the
certificate's child factors. -/
theorem parityProduct_cert_bounds {ι : Type*} (s : Finset ι) (ev od : ι → ℝ)
    {x₀ e o : ℝ} (hx₀ : 0 ≤ x₀) (he : 0 ≤ e) (ho : 0 ≤ o) {n : ℕ} (hs : s.card ≤ n)
    (hev : ∀ i ∈ s, 0 ≤ ev i ∧ ev i ≤ 1 + x₀ * o)
    (hod : ∀ i ∈ s, 0 ≤ od i ∧ od i ≤ x₀ * e) :
    (0 ≤ parityProductEven s ev od ∧
      parityProductEven s ev od ≤ (parityPower (1 + x₀ * o) (x₀ * e) n).1) ∧
    (0 ≤ parityProductOdd s ev od ∧
      parityProductOdd s ev od ≤ (parityPower (1 + x₀ * o) (x₀ * e) n).2) := by
  have hA : 1 ≤ 1 + x₀ * o := le_add_of_nonneg_right (mul_nonneg hx₀ ho)
  have hB : 0 ≤ x₀ * e := mul_nonneg hx₀ he
  have hh := parityProduct_bounds s ev od (by linarith) hB hev hod
  have hm := parityPower_mono hA hB hs
  exact ⟨⟨hh.1.1, hh.1.2.trans hm.1⟩, ⟨hh.2.1, hh.2.2.trans hm.2⟩⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def walkTreeEvenMass (x : ℝ) (h : ℕ) (p : Option V) (v : V) : ℝ :=
  (walkTreeMass G x h p v + walkTreeMass G (-x) h p v) / 2

noncomputable def walkTreeOddMass (x : ℝ) (h : ℕ) (p : Option V) (v : V) : ℝ :=
  (walkTreeMass G x h p v - walkTreeMass G (-x) h p v) / 2

theorem walkTreeParity_succ (x : ℝ) (h : ℕ) (p : Option V) (v : V) :
    walkTreeEvenMass G x (h + 1) p v = parityProductEven univ
      (fun w : childPorts G p v => 1 + x * walkTreeOddMass G x h (some v) w.val)
      (fun w : childPorts G p v => x * walkTreeEvenMass G x h (some v) w.val) ∧
    walkTreeOddMass G x (h + 1) p v = parityProductOdd univ
      (fun w : childPorts G p v => 1 + x * walkTreeOddMass G x h (some v) w.val)
      (fun w : childPorts G p v => x * walkTreeEvenMass G x h (some v) w.val) := by
  have hp : ∀ w : childPorts G p v,
      (1 + x * walkTreeOddMass G x h (some v) w.val) +
        x * walkTreeEvenMass G x h (some v) w.val =
      1 + x * walkTreeMass G x h (some v) w.val := by
    intro w
    unfold walkTreeOddMass walkTreeEvenMass
    ring
  have hm : ∀ w : childPorts G p v,
      (1 + x * walkTreeOddMass G x h (some v) w.val) -
        x * walkTreeEvenMass G x h (some v) w.val =
      1 + (-x) * walkTreeMass G (-x) h (some v) w.val := by
    intro w
    unfold walkTreeOddMass walkTreeEvenMass
    ring
  simp only [walkTreeEvenMass, walkTreeOddMass, walkTreeMass_succ,
    parityProductEven, parityProductOdd] at hp hm ⊢
  simp_rw [hp, hm]
  trivial

theorem card_childPorts_le_pred {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {p v : V} (hp : G.Adj v p) : (childPorts G (some p) v).card ≤ D - 1 := by
  rw [card_childPorts_some G hp]
  have := hdeg v
  omega

/-- Child factors of a branch whose own children obey the certificate's majorant. -/
theorem childFactor_cert_bounds {x x₀ e o : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    {ev od : ℝ} (hev : 0 ≤ ev ∧ ev ≤ e) (hod : 0 ≤ od ∧ od ≤ o) :
    (0 ≤ 1 + x * od ∧ 1 + x * od ≤ 1 + x₀ * o) ∧ (0 ≤ x * ev ∧ x * ev ≤ x₀ * e) :=
  ⟨⟨add_nonneg zero_le_one (mul_nonneg hx hod.1),
      add_le_add_right (mul_le_mul hxx hod.2 hod.1 (hx.trans hxx)) 1⟩,
    ⟨mul_nonneg hx hev.1, mul_le_mul hxx hev.2 hev.1 (hx.trans hxx)⟩⟩

/-- Branch masses stay inside the certificate's majorant at every depth. -/
theorem walkTreeParity_cert_branch_bounds {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (h : ℕ) {p v : V} (hp : G.Adj v p) :
    (0 ≤ walkTreeEvenMass G x h (some p) v ∧ walkTreeEvenMass G x h (some p) v ≤ e) ∧
    (0 ≤ walkTreeOddMass G x h (some p) v ∧ walkTreeOddMass G x h (some p) v ≤ o) := by
  have he1 : 1 ≤ e := by
    have := (parityPower_mono (a := 1 + x₀ * o) (b := x₀ * e)
      (le_add_of_nonneg_right (mul_nonneg hc.x₀_nonneg hc.o_nonneg))
      (mul_nonneg hc.x₀_nonneg hc.e_nonneg) (Nat.zero_le (D - 1))).1
    simp only [parityPower] at this
    linarith [hc.branch.1]
  induction h generalizing p v with
  | zero => norm_num [walkTreeEvenMass, walkTreeOddMass]; exact ⟨he1, hc.o_nonneg⟩
  | succ h ih =>
    have hw : ∀ w : childPorts G (some p) v, _ := fun w =>
      childFactor_cert_bounds hx hxx (ih ((mem_childPorts G).mp w.2).1.symm).1
        (ih ((mem_childPorts G).mp w.2).1.symm).2
    have hh := parityProduct_cert_bounds Finset.univ _ _ hc.x₀_nonneg hc.e_nonneg hc.o_nonneg
      (by simpa using card_childPorts_le_pred G hdeg hp) (fun w _ => (hw w).1)
      (fun w _ => (hw w).2)
    rw [(walkTreeParity_succ G x h (some p) v).1, (walkTreeParity_succ G x h (some p) v).2]
    exact ⟨⟨hh.1.1, hh.1.2.trans hc.branch.1⟩, ⟨hh.2.1, hh.2.2.trans hc.branch.2⟩⟩

/-- The odd mass at a root with no predecessor is at most the certificate's `r`. -/
theorem walkTreeOddMass_cert_root_le {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (h : ℕ) (v : V) : walkTreeOddMass G x h none v ≤ r := by
  cases h with
  | zero =>
    have := (parityPower_nonneg (a := 1 + x₀ * o) (b := x₀ * e)
      (by have := mul_nonneg hc.x₀_nonneg hc.o_nonneg; linarith)
      (mul_nonneg hc.x₀_nonneg hc.e_nonneg) D).2
    norm_num [walkTreeOddMass]
    linarith [hc.root]
  | succ h =>
    have hw : ∀ w : childPorts G none v, _ := fun w =>
      have hb := walkTreeParity_cert_branch_bounds G hdeg hc hx hxx h
        ((mem_childPorts G).mp w.2).1.symm
      childFactor_cert_bounds hx hxx hb.1 hb.2
    have hh := parityProduct_cert_bounds Finset.univ _ _ hc.x₀_nonneg hc.e_nonneg hc.o_nonneg
      (by simpa using hdeg v) (fun w _ => (hw w).1) (fun w _ => (hw w).2)
    rw [(walkTreeParity_succ G x h none v).2]
    exact hh.2.2.trans hc.root

theorem sum_odd_powers {ι : Type*} (s : Finset ι) (n : ι → ℕ) (x : ℝ) :
    (∑ i ∈ s.filter (fun i => Odd (n i)), x ^ n i) =
      ((∑ i ∈ s, x ^ n i) - ∑ i ∈ s, (-x) ^ n i) / 2 := by
  classical
  rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rcases Nat.even_or_odd (n i) with he | ho
  · have hno : ¬ Odd (n i) := by
      rintro ⟨m, hm⟩
      obtain ⟨j, hj⟩ := he
      omega
    simp [hno, neg_pow, he.neg_one_pow]
  · simp [ho, neg_pow, ho.neg_one_pow]
    ring

theorem sum_odd_walkTreeCodes (x : ℝ) (h : ℕ) (p : Option V) (v : V) :
    (∑ c ∈ Finset.univ.filter (fun c : WalkTreeCode G h p v =>
      Odd (walkTreeSize G c)), x ^ walkTreeSize G c) = walkTreeOddMass G x h p v :=
  sum_odd_powers _ _ _

end GridGen.Polymer
