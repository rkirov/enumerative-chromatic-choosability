/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Ball
import Outerplanar.Face

/-!
# Three colours when every even face has at most one loaded edge: the graph induction

The graphs of this file are built from an edge by *ears on edges* (`IsEar`: a path of new
vertices joined to two adjacent old vertices), with every edge carrying one of two tags.

* An **active** edge may carry anything that is built later.
* A **tame** edge may only carry faces of odd length (triangles, pentagons, …), on tame edges
  again; what hangs on a tame edge behaves like a plain edge.

A face of odd length on an active edge may make any of its new edges active. A face of even
length on an active edge makes at most one of its new edges active. So call an edge *loaded* when
the part of the graph beyond it contains a face of even length: below every face of even length
there is at most one loaded edge, and faces of odd length are unrestricted. Every 2-connected
outerplanar graph in which no even face has three sides leading to other even faces is built this
way (rooted at a suitable boundary edge); so are all graphs whose bounded faces are odd, and
chains of faces.

`BallBound` is the weighted lower bound carried by the induction: pair profiles in the ball class
(`InBall`) on active edges and greedy ones (`Dominant`) on tame edges. It needs four properties
of single faces:

* `ballTriClosed` — a triangle maps the ball class on its two side edges to the ball class. This
  is proved here, from the six-family extension `Matched.extend`;
* `BallFaceClosed m` — a face with `m ≥ 2` interior vertices does so when one path edge is in the
  ball class and the others are greedy. This is a *hypothesis* of the theorems of this file, in
  the manner of `FaceClosed`. It is proved for squares in `Outerplanar/SquareThm.lean`, from
  certificates checked by the kernel, and for all `m` in `Outerplanar/LongFace.lean`, by a
  reduction of longer faces; that file states the resulting theorem `ecc_three_of_oneLoadBuilt`;
* `DomFaceClosed m` — a face with an odd number `m` of interior vertices maps greedy profiles on
  all its path edges to a greedy profile. Also a hypothesis here; it is a count of the colourings
  of a path, proved in `Outerplanar/OddFace.lean`;
* `BallAllClosed m` — a face with an odd number `m ≥ 3` of interior vertices maps the ball class
  on all its path edges to the ball class. Also a hypothesis here; it is proved in
  `Outerplanar/OddBall.lean` from the walks on three colours of `Outerplanar/Walks.lean`.

This is a result of this repository's 2026-11 AI research collaboration.
-/

namespace Outerplanar

open Finset

/-! ### Closure under one face, as properties -/

/-- One sixth of the number of `3`-colourings of a cycle of length `m + 2`: the constant of a
face with `m` interior vertices. -/
noncomputable def faceConst3 (m : ℕ) : ℝ :=
  ((((3 : ℕ) : ℝ) - 1) ^ (m + 1) - (-1) ^ (m + 1)) / (3 : ℕ)

theorem faceConst3_pos (m : ℕ) : 0 < faceConst3 m := faceConst_pos (le_refl 3) m

theorem faceConst3_one : faceConst3 1 = 1 := by norm_num [faceConst3]

/-- A triangle maps the ball class on its two side edges to the ball class on its base. -/
def BallTriClosed : Prop :=
  ∀ (Lu Lv : Finset ℕ) (Li : Fin 1 → Finset ℕ), Lu.card = 3 → Lv.card = 3 →
    (∀ j, (Li j).card = 3) → ∀ (E : Fin 2 → ℕ → ℕ → ℝ), (∀ j c d, 0 ≤ E j c d) →
    ∀ (A : Fin 2 → ℝ), (∀ j, 0 < A j) →
    (∀ j : Fin 2,
      InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) →
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (∏ j, A j)

/-- A face with `m` interior vertices maps the ball class on one path edge `j₀`, with greedy
profiles on the other path edges, to the ball class on its root edge, with the constant of the
constant-list count. -/
def BallFaceClosed (m : ℕ) : Prop :=
  ∀ (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ), Lu.card = 3 → Lv.card = 3 →
    (∀ j, (Li j).card = 3) → ∀ (j₀ : Fin (m + 1)) (E : Fin (m + 1) → ℕ → ℕ → ℝ),
    (∀ j c d, 0 ≤ E j c d) → ∀ (A : Fin (m + 1) → ℝ), (∀ j, 0 < A j) →
    InBall (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀) →
    (∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) →
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E)
      (faceConst3 m * ∏ j, A j)

/-- A face with `m` interior vertices and greedy profiles on all its path edges has a greedy
profile on its root edge, with the constant of the constant-list count. This holds exactly for
odd `m` (`domFaceClosed_odd` in `Outerplanar/OddFace.lean`; for even `m` the count can be one
short). -/
def DomFaceClosed (m : ℕ) : Prop :=
  ∀ (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ), (∀ j, (Li j).card = 3) →
    ∀ (E : Fin (m + 1) → ℕ → ℕ → ℝ), (∀ j c d, 0 ≤ E j c d) → ∀ (A : Fin (m + 1) → ℝ),
    (∀ j, 0 < A j) →
    (∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) →
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j)

/-- A face with `m` interior vertices maps the ball class on *all* its path edges to the ball
class on its root edge. This holds for odd `m`: `ballTriClosed` for triangles, and
`ballOddClosed` in `Outerplanar/OddBall.lean` for `m ≥ 3`. It fails for squares. -/
def BallAllClosed (m : ℕ) : Prop :=
  ∀ (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ), Lu.card = 3 → Lv.card = 3 →
    (∀ j, (Li j).card = 3) → ∀ (E : Fin (m + 1) → ℕ → ℕ → ℝ), (∀ j c d, 0 ≤ E j c d) →
    ∀ (A : Fin (m + 1) → ℝ), (∀ j, 0 < A j) →
    (∀ j : Fin (m + 1),
      InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) →
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j)

/-- The same with ordinary edges elsewhere on the path: the form in which a proof is carried
out. `ballFaceClosed_of_bare` recovers `BallFaceClosed`. -/
def BallFaceBare (m : ℕ) : Prop :=
  ∀ (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ), Lu.card = 3 → Lv.card = 3 →
    (∀ j, (Li j).card = 3) → ∀ (j₀ : Fin (m + 1)) (W : ℕ → ℕ → ℝ), (∀ c d, 0 ≤ W c d) →
    ∀ A : ℝ, 0 < A →
    InBall (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) W A →
    InBall Lu Lv (faceSum Li (fun _ _ => 1)
      (fun j => if j = j₀ then W else fun c d => if c ≠ d then 1 else 0)) (faceConst3 m * A)

/-- Greedy profiles on the other path edges only help. -/
theorem ballFaceClosed_of_bare {m : ℕ} (h : BallFaceBare m) : BallFaceClosed m := by
  intro Lu Lv Li hLu hLv hLi j₀ E hE0 A hA hE hdom
  set E' : Fin (m + 1) → ℕ → ℕ → ℝ :=
    fun j => if j = j₀ then E j₀ else fun c d => if c ≠ d then 1 else 0 with hE'
  set K : ℝ := ∏ j ∈ univ.erase j₀, A j with hK
  have hKpos : 0 < K := Finset.prod_pos fun j _ => hA j
  have hE'0 : ∀ j c d, 0 ≤ E' j c d := by
    intro j c d
    by_cases hj : j = j₀
    · simp only [hE', hj, ite_true]
      exact hE0 _ _ _
    · simp only [hE', hj, ite_false]
      split_ifs <;> norm_num
  have hbare := h Lu Lv Li hLu hLv hLi j₀ (E j₀) (hE0 j₀) (A j₀) (hA j₀) hE
  have hF0 : ∀ c d, 0 ≤ faceSum Li (fun _ _ => 1) E' c d :=
    faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) hE'0
  -- scale by the constants of the greedy edges
  have hscaled : InBall Lu Lv (fun c d => faceSum Li (fun _ _ => 1) E' c d * K)
      (faceConst3 m * A j₀ * K) :=
    InBall.mul (mul_pos (faceConst3_pos m) (hA j₀)).le hKpos.le hbare
      (Dominant.inBall (W := fun _ _ => K) hKpos.le fun _ _ _ _ _ => le_refl K)
  have hconst : faceConst3 m * ∏ j, A j = faceConst3 m * A j₀ * K := by
    rw [hK, ← Finset.mul_prod_erase univ A (mem_univ j₀)]
    ring
  rw [hconst]
  refine hscaled.mono (fun c d => mul_nonneg (hF0 c d) hKpos.le) fun c hc d hd _ => ?_
  -- termwise comparison
  unfold faceSum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun g hg => ?_
  simp only [Finset.prod_const_one, one_mul]
  have hmem : ∀ i : Fin (m + 2), pathCol c d g i ∈ pathList Lu Lv Li i := fun i =>
    pathCol_mem hc hd (fun j => Fintype.mem_piFinset.mp hg j) i
  by_cases hall : ∀ j : Fin (m + 1), j ≠ j₀ → pathCol c d g j.castSucc ≠ pathCol c d g j.succ
  · -- every other edge is properly coloured
    have e1 : ∏ j : Fin (m + 1), E' j (pathCol c d g j.castSucc) (pathCol c d g j.succ)
        = E j₀ (pathCol c d g j₀.castSucc) (pathCol c d g j₀.succ) := by
      rw [← Finset.mul_prod_erase univ _ (mem_univ j₀)]
      have : ∏ j ∈ univ.erase j₀, E' j (pathCol c d g j.castSucc) (pathCol c d g j.succ) = 1 :=
        Finset.prod_eq_one fun j hj => by
          have hne := Finset.ne_of_mem_erase hj
          simp only [hE', hne, ite_false, hall j hne, ne_eq, not_false_eq_true, ite_true]
      rw [this, mul_one]
      simp only [hE', ite_true]
    rw [e1, ← Finset.mul_prod_erase univ _ (mem_univ j₀)]
    refine mul_le_mul_of_nonneg_left ?_ (hE0 _ _ _)
    exact Finset.prod_le_prod₀ (fun j _ => (hA j).le) fun j hj =>
      hdom j (Finset.ne_of_mem_erase hj) _ (hmem _) _ (hmem _) (hall j (Finset.ne_of_mem_erase hj))
  · -- some other edge is not: the bare term vanishes
    obtain ⟨j, hj, heq⟩ : ∃ j : Fin (m + 1), j ≠ j₀ ∧
        pathCol c d g j.castSucc = pathCol c d g j.succ := by
      by_contra hne
      exact hall fun j hj heq => hne ⟨j, hj, heq⟩
    have e0 : ∏ j : Fin (m + 1), E' j (pathCol c d g j.castSucc) (pathCol c d g j.succ) = 0 :=
      Finset.prod_eq_zero (mem_univ j) (by simp only [hE', hj, ite_false, heq, ne_eq,
        not_true_eq_false])
    rw [e0, zero_mul]
    exact Finset.prod_nonneg fun j _ => hE0 _ _ _

/-- One term of the sum over the colours of the apex of a triangle. -/
theorem tri_term_le (Li : Fin 1 → Finset ℕ) (E : Fin 2 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (a b : ℕ) {e : ℕ} (he : e ∈ Li 0) :
    E 0 a e * E 1 e b ≤ faceSum Li (fun _ _ => 1) E a b := by
  have hg : (fun _ : Fin 1 => e) ∈ Fintype.piFinset Li :=
    Fintype.mem_piFinset.mpr fun j => by rw [Subsingleton.elim j 0]; exact he
  have hterm : ∀ g ∈ Fintype.piFinset Li, 0 ≤ (∏ _j : Fin 1, (1 : ℝ)) *
      ∏ j : Fin 2, E j (pathCol a b g j.castSucc) (pathCol a b g j.succ) := fun g _ =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => zero_le_one)
      (Finset.prod_nonneg fun j _ => hE0 _ _ _)
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum hterm hg)
  have p0 : pathCol a b (fun _ : Fin 1 => e) (Fin.castSucc (0 : Fin 2)) = a :=
    consSnoc_zero _ _ _ _ (by simp)
  have p1 : pathCol a b (fun _ : Fin 1 => e) (Fin.succ (0 : Fin 2)) = e :=
    consSnoc_mid _ _ _ _ (0 : Fin 1) (by simp)
  have p1' : pathCol a b (fun _ : Fin 1 => e) (Fin.castSucc (1 : Fin 2)) = e :=
    consSnoc_mid _ _ _ _ (0 : Fin 1) (by simp)
  have p2 : pathCol a b (fun _ : Fin 1 => e) (Fin.succ (1 : Fin 2)) = b :=
    consSnoc_last _ _ _ _ (by simp)
  rw [Fin.prod_univ_two, p0, p1, p1', p2]
  simp only [Finset.prod_const_one, one_mul]

/-- The lists at the ends of the two side edges of a triangle. -/
theorem pathList_tri (Lu Lv : Finset ℕ) (Li : Fin 1 → Finset ℕ) :
    pathList Lu Lv Li (Fin.castSucc (0 : Fin 2)) = Lu ∧
      pathList Lu Lv Li (Fin.succ (0 : Fin 2)) = Li 0 ∧
      pathList Lu Lv Li (Fin.castSucc (1 : Fin 2)) = Li 0 ∧
      pathList Lu Lv Li (Fin.succ (1 : Fin 2)) = Lv :=
  ⟨consSnoc_zero _ _ _ _ (by simp), consSnoc_mid _ _ _ _ (0 : Fin 1) (by simp),
    consSnoc_mid _ _ _ _ (0 : Fin 1) (by simp), consSnoc_last _ _ _ _ (by simp)⟩

/-- A list of three colours has a colour different from two given ones. -/
theorem exists_avoid {Lx : Finset ℕ} (hx : Lx.card = 3) (c d : ℕ) :
    ∃ e ∈ Lx, e ≠ c ∧ e ≠ d := by
  obtain ⟨e, he⟩ : ((Lx.erase c).erase d).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.pred_card_le_card_erase (s := Lx) (a := c)
    have h2 := Finset.pred_card_le_card_erase (s := Lx.erase c) (a := d)
    omega
  exact ⟨e, (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).2,
    (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1, (Finset.mem_erase.mp he).1⟩

/-- A triangle with greedy side edges is greedy: the apex has a colour avoiding both ends. -/
theorem dominant_tri (Lu Lv : Finset ℕ) (Li : Fin 1 → Finset ℕ) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin 2 → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 2 → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j : Fin 2,
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) (∏ j, A j) := by
  intro c hc d hd _
  obtain ⟨e, heL, hec, hed⟩ := exists_avoid (hLi 0) c d
  obtain ⟨l0, l1, l2, l3⟩ := pathList_tri Lu Lv Li
  have h0 := hE 0 c (by rw [l0]; exact hc) e (by rw [l1]; exact heL) (Ne.symm hec)
  have h1 := hE 1 e (by rw [l2]; exact heL) d (by rw [l3]; exact hd) hed
  rw [Fin.prod_univ_two]
  exact (mul_le_mul h0 h1 (hA 1) ((hA 0).trans h0)).trans (tri_term_le Li E hE0 c d heL)

/-- **Triangles preserve the ball class.** The six good colourings of the base extend to the
apex so that they are matched on both side edges (`Matched.extend`); the colouring that receives
the moved weight extends by any colour of the apex avoiding its two ends. -/
theorem ballTriClosed : BallTriClosed := by
  intro Lu Lv Li _ _ hLi E hE0 A hA hE p q hm hpq j c hc d hd hcd
  obtain ⟨l0, l1, l2, l3⟩ := pathList_tri Lu Lv Li
  have hI0 : InBall Lu (Li 0) (E 0) (A 0) := by
    have := hE 0
    rwa [l0, l1] at this
  have hI1 : InBall (Li 0) Lv (E 1) (A 1) := by
    have := hE 1
    rwa [l2, l3] at this
  obtain ⟨g, hgm, hgp, hgq, hm0, hm1⟩ := hm.extend (hLi 0) hpq
  obtain ⟨e, heL, hec, hed⟩ := exists_avoid (hLi 0) c d
  have k0 := hI0 p g hm0.symm (fun i => (hgp i).symm) j c hc e heL (Ne.symm hec)
  have k1 := hI1 g q hm1 hgq j e heL d hd hed
  have hF : ∀ a b x, x ∈ Li 0 → E 0 a x * E 1 x b ≤ faceSum Li (fun _ _ => 1) E a b :=
    fun a b x hx => tri_term_le Li E hE0 a b hx
  have h00 : ∀ a b x, 0 ≤ E 0 a x * E 1 x b := fun a b x => mul_nonneg (hE0 _ _ _) (hE0 _ _ _)
  calc (∏ j, A j) ^ 600 = A 0 ^ 600 * A 1 ^ 600 := by rw [Fin.prod_univ_two, mul_pow]
    _ ≤ ((∏ k ∈ univ.erase j, E 0 (p k) (g k)) ^ 100 * E 0 (p j) (g j) ^ 91 * E 0 c e ^ 9)
        * ((∏ k ∈ univ.erase j, E 1 (g k) (q k)) ^ 100 * E 1 (g j) (q j) ^ 91 * E 1 e d ^ 9) :=
      mul_le_mul k0 k1 (pow_nonneg (hA 1).le _) ((pow_nonneg (hA 0).le _).trans k0)
    _ = (∏ k ∈ univ.erase j, E 0 (p k) (g k) * E 1 (g k) (q k)) ^ 100
        * (E 0 (p j) (g j) * E 1 (g j) (q j)) ^ 91 * (E 0 c e * E 1 e d) ^ 9 := by
      rw [Finset.prod_mul_distrib]
      ring
    _ ≤ _ := ball_mul_le (Finset.prod_nonneg fun k _ => h00 _ _ _) (h00 _ _ _) (h00 _ _ _)
        (Finset.prod_le_prod₀ (fun k _ => h00 _ _ _) fun k _ => hF _ _ _ (hgm k))
        (hF _ _ _ (hgm j)) (hF _ _ _ heL)

/-! ### The graphs -/

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Both orientations of the path edges `j ∈ J` of an ear. -/
def earPairs {m : ℕ} (u v : V) (x : Fin m → V) (J : Finset (Fin (m + 1))) : Finset (V × V) :=
  J.image (fun j => (earPath u v x j.castSucc, earPath u v x j.succ)) ∪
    J.image (fun j => (earPath u v x j.succ, earPath u v x j.castSucc))

/-- `OneLoadBuilt G S act`: the induced subgraph on `S` is built from an edge by ears on edges,
`act` being the set of (ordered pairs of ends of) active edges. A new face on the edge `uv` makes
the path edges in `J` active; this needs `uv` active, and for an ear with an even number of
vertices `J` has at most one element. A new face on a tame edge has an odd number of interior
vertices. -/
inductive OneLoadBuilt : Finset V → Finset (V × V) → Prop
  | edge (u v : V) (huv : G.Adj u v) : OneLoadBuilt {u, v} {(u, v), (v, u)}
  | face (S : Finset V) (act : Finset (V × V)) (m : ℕ) (u v : V) (x : Fin m → V)
      (he : IsEar G S u v x) (J : Finset (Fin (m + 1))) (hJ : J.Nonempty → (u, v) ∈ act)
      (hlong : 2 ≤ m → (u, v) ∈ act → J.card ≤ 1 ∨ Odd m) (hodd : (u, v) ∉ act → Odd m)
      (hS : OneLoadBuilt S act) :
      OneLoadBuilt (S ∪ univ.image x) (act ∪ earPairs u v x J)

/-- The invariant on one ordered edge: the ball class if it is active, greedy otherwise. -/
def EdgeInv (act : Finset (V × V)) (L : V → Finset ℕ) (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ)
    (a b : V) : Prop :=
  ((a, b) ∈ act → InBall (L a) (L b) (Ω a b) (A a b)) ∧
    ((a, b) ∉ act → Dominant (L a) (L b) (Ω a b) (A a b))

/-- The weighted lower bound on the vertex set `S` with active edges `act`: for lists of three
colours and pair profiles satisfying the invariant, the weighted partition function is at least
the constant-list count times the constants of the profiles. -/
def BallBound (S : Finset V) (act : Finset (V × V)) : Prop :=
  ∀ (L : V → Finset ℕ) (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ),
    (∀ x ∈ S, (L x).card = 3) → (∀ x y c d, 0 ≤ Ω x y c d) → (∀ x y, 0 < A x y) →
    (∀ a ∈ S, ∀ b ∈ S, G.Adj a b → EdgeInv act L Ω A a b) →
    ZG G S (fun _ => range 3) (fun _ _ => 1) neProfile * ∏ p ∈ adjPairs G S, A p.1 p.2
      ≤ ZG G S L (fun _ _ => 1) Ω

variable {G}

theorem OneLoadBuilt.act_mem {S : Finset V} {act : Finset (V × V)} (h : OneLoadBuilt G S act)
    {a b : V} (hab : (a, b) ∈ act) : a ∈ S ∧ b ∈ S := by
  induction h with
  | edge u v huv =>
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hab ⊢
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  | face S act m u v x he J hJ hlong hodd hS ih =>
    rcases mem_union.mp hab with h1 | h1
    · exact ⟨mem_union_left _ (ih h1).1, mem_union_left _ (ih h1).2⟩
    · simp only [earPairs, mem_union, mem_image, Prod.mk.injEq] at h1
      rcases h1 with ⟨j, _, rfl, rfl⟩ | ⟨j, _, rfl, rfl⟩
      · exact ⟨he.earPath_mem _, he.earPath_mem _⟩
      · exact ⟨he.earPath_mem _, he.earPath_mem _⟩

/-- A path edge of a new ear is active exactly when it was chosen. -/
theorem IsEar.mem_act_iff {S : Finset V} {m : ℕ} {u v : V} {x : Fin m → V}
    (he : IsEar G S u v x) {act : Finset (V × V)} (hact : ∀ a b, (a, b) ∈ act → a ∈ S ∧ b ∈ S)
    (J : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    ((earPath u v x j.castSucc, earPath u v x j.succ) ∈ act ∪ earPairs u v x J ↔ j ∈ J) ∧
      ((earPath u v x j.succ, earPath u v x j.castSucc) ∈ act ∪ earPairs u v x J ↔ j ∈ J) := by
  have hinj := he.earPath_injective
  have hne : ∀ j' : Fin (m + 1), ¬ (j.castSucc = j'.succ ∧ j.succ = j'.castSucc) := by
    rintro j' ⟨h1, h2⟩
    have e1 := congrArg Fin.val h1
    have e2 := congrArg Fin.val h2
    simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
    omega
  constructor
  · constructor
    · intro h
      rcases mem_union.mp h with h1 | h1
      · exact absurd (hact _ _ h1) (he.earPath_not_both j)
      · simp only [earPairs, mem_union, mem_image, Prod.mk.injEq] at h1
        rcases h1 with ⟨j', hj', e1, _⟩ | ⟨j', _, e1, e2⟩
        · have := Fin.castSucc_injective _ (hinj e1)
          exact this ▸ hj'
        · exact absurd ⟨(hinj e1).symm, (hinj e2).symm⟩ (hne j')
    · intro hj
      refine mem_union_right _ ?_
      simp only [earPairs, mem_union, mem_image]
      exact Or.inl ⟨j, hj, rfl⟩
  · constructor
    · intro h
      rcases mem_union.mp h with h1 | h1
      · exact absurd ((hact _ _ h1).symm) (he.earPath_not_both j)
      · simp only [earPairs, mem_union, mem_image, Prod.mk.injEq] at h1
        rcases h1 with ⟨j', _, e1, e2⟩ | ⟨j', hj', e1, _⟩
        · exact absurd ⟨(hinj e2).symm, (hinj e1).symm⟩ (hne j')
        · have := Fin.succ_injective _ (hinj e1)
          exact this ▸ hj'
    · intro hj
      refine mem_union_right _ ?_
      simp only [earPairs, mem_union, mem_image]
      exact Or.inr ⟨j, hj, rfl⟩

/-! ### The base edge -/

theorem ballBound_edge {u v : V} (huv : G.Adj u v) : BallBound G {u, v} {(u, v), (v, u)} := by
  intro L Ω A hcard hΩ hA hinv
  have huv' : u ≠ v := huv.ne
  have hu : u ∉ ({v} : Finset V) := by simpa using huv'
  have hv : v ∈ ({v} : Finset V) := mem_singleton_self v
  have huniq : ∀ z ∈ ({v} : Finset V), G.Adj u z → z = v := fun z hz _ => mem_singleton.mp hz
  have hve : ({v} : Finset V) = insert v ∅ := by simp
  have hiso : ∀ z ∈ (∅ : Finset V), ¬ G.Adj v z := by simp
  -- the constant-list count
  have hconst : ZG G {u, v} (fun _ => range 3) (fun _ _ => 1) neProfile = 6 := by
    show ZG G (insert u {v}) (fun _ => range 3) (fun _ _ => 1) neProfile = 6
    rw [ZG_const_insert_pendant G 3 hu hv huv huniq, hve,
      ZG_const_insert_isolated G 3 (notMem_empty v) hiso, ZG_empty]
    norm_num
  -- the product of the constants
  have hprod : ∏ p ∈ adjPairs G {u, v}, A p.1 p.2 = A u v * A v u := by
    show ∏ p ∈ adjPairs G (insert u {v}), A p.1 p.2 = A u v * A v u
    rw [prod_adjPairs_insert_pendant G hu hv huv huniq (fun p => A p.1 p.2), hve,
      adjPairs_insert_isolated G hiso]
    simp [adjPairs]
  -- the list count
  have hZ : ZG G {u, v} L (fun _ _ => 1) Ω
      = ∑ d ∈ L v, ∑ c ∈ L u, Ω v u d c * Ω u v c d := by
    show ZG G (insert u {v}) L (fun _ _ => 1) Ω = _
    rw [ZG_insert_pendant G hu hv huv huniq,
      ← ZG_update_vertex G hv L (fun _ _ => 1) Ω
        (fun d => ∑ c ∈ L u, Ω v u d c * Ω u v c d * 1)]
    simp only [hve]
    rw [ZG_insert_isolated G (notMem_empty v) hiso, ZG_empty]
    simp
  rw [hconst, hprod, hZ]
  have huS : u ∈ ({u, v} : Finset V) := by simp
  have hvS : v ∈ ({u, v} : Finset V) := by simp
  have h1 := (hinv v hvS u huS huv.symm).1 (by simp)
  have h2 := ((hinv u huS v hvS huv).1 (by simp)).swap
  have h12 := InBall.mul (hA v u).le (hA u v).le h1 h2
  have := h12.sum_ge (hcard v hvS) (hcard u huS) (mul_pos (hA v u) (hA u v))
    (fun c d => mul_nonneg (hΩ _ _ _ _) (hΩ _ _ _ _))
  linarith [this]

/-! ### Adding a face -/

/-- The step of the induction, given the profile class of the new face on its root edge. -/
theorem step_face {m : ℕ} {S : Finset V} {u v : V} {x : Fin m → V} (he : IsEar G S u v x)
    {act act' : Finset (V × V)} (L : V → Finset ℕ) (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ)
    (hcard : ∀ z ∈ S ∪ univ.image x, (L z).card = 3)
    (hΩ : ∀ x y c d, 0 ≤ Ω x y c d) (hA : ∀ x y, 0 < A x y)
    (hsame : ∀ a ∈ S, ∀ b ∈ S, ((a, b) ∈ act' ↔ (a, b) ∈ act))
    (hinv : ∀ a ∈ S ∪ univ.image x, ∀ b ∈ S ∪ univ.image x, G.Adj a b → EdgeInv act' L Ω A a b)
    (hFa : (u, v) ∈ act → InBall (L u) (L v)
      (faceSum (fun j => L (x j)) (fun _ _ => 1) (earE Ω u v x))
      (faceConst3 m
        * ∏ j : Fin (m + 1), A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc)))
    (hFt : (u, v) ∉ act → Dominant (L u) (L v)
      (faceSum (fun j => L (x j)) (fun _ _ => 1) (earE Ω u v x))
      (faceConst3 m
        * ∏ j : Fin (m + 1), A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc)))
    (ih : BallBound G S act) :
    ZG G (S ∪ univ.image x) (fun _ => range 3) (fun _ _ => 1) neProfile
        * ∏ p ∈ adjPairs G (S ∪ univ.image x), A p.1 p.2
      ≤ ZG G (S ∪ univ.image x) L (fun _ _ => 1) Ω := by
  have huvm : (u, v) ∈ adjPairs G S := (mem_adjPairs G).mpr ⟨he.hu, he.hv, he.huv⟩
  have hC : 0 < faceConst3 m
      * ∏ j : Fin (m + 1), A (earPath u v x j.castSucc) (earPath u v x j.succ)
        * A (earPath u v x j.succ) (earPath u v x j.castSucc) :=
    mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => mul_pos (hA _ _) (hA _ _))
  have hF0 : ∀ c d, 0 ≤ faceSum (fun j => L (x j)) (fun _ _ => 1) (earE Ω u v x) c d :=
    faceSum_nonneg _ _ _ (fun j c _ => zero_le_one)
      (fun j c d => mul_nonneg (hΩ _ _ _ _) (hΩ _ _ _ _))
  have ih' := ih L
    (fun a b => if a = u ∧ b = v then fun c d => Ω u v c d
      * faceSum (fun j => L (x j)) (fun _ _ => 1) (earE Ω u v x) c d else Ω a b)
    (fun a b => if a = u ∧ b = v then A u v
      * (faceConst3 m
      * ∏ j : Fin (m + 1), A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc)) else A a b)
    (fun z hz => hcard z (mem_union_left _ hz))
    (by
      intro a b c d
      by_cases hab : a = u ∧ b = v
      · simp only [hab, and_self, ite_true]
        exact mul_nonneg (hΩ _ _ _ _) (hF0 c d)
      · simp only [hab, ite_false]
        exact hΩ _ _ _ _)
    (by
      intro a b
      by_cases hab : a = u ∧ b = v
      · simp only [hab, and_self, ite_true]
        exact mul_pos (hA _ _) hC
      · simp only [hab, ite_false]
        exact hA _ _)
    (by
      intro a ha b hb hadj
      have hold := hinv a (mem_union_left _ ha) b (mem_union_left _ hb) hadj
      by_cases hab : a = u ∧ b = v
      · obtain ⟨rfl, rfl⟩ := hab
        simp only [EdgeInv, and_self, ite_true]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact InBall.mul (hA _ _).le hC.le (hold.1 ((hsame a ha b hb).mpr h)) (hFa h)
        · exact Dominant.mul (hA _ _).le hC.le
            (hold.2 fun h' => h ((hsame a ha b hb).mp h')) (hFt h)
      · simp only [EdgeInv, hab, ite_false]
        exact ⟨fun h => hold.1 ((hsame a ha b hb).mpr h),
          fun h => hold.2 fun h' => h ((hsame a ha b hb).mp h')⟩)
  rw [prod_adjPairs_update G huvm A, ZG_update_pair G huvm L _ Ω, ← he.ZG_eq] at ih'
  rw [he.ZG_const G (by norm_num : 1 ≤ 3), he.prod_adjPairs (fun p => A p.1 p.2)]
  refine le_of_eq_of_le ?_ ih'
  unfold faceConst3
  ring

/-! ### The main theorems -/

/-- The weighted lower bound for graphs built with at most one loaded edge below every long
face, given closure under single faces. -/
theorem ballBound_of_oneLoadBuilt (hface : ∀ m, 2 ≤ m → BallFaceClosed m)
    (hdom : ∀ m, Odd m → DomFaceClosed m) (hall : ∀ m, Odd m → 3 ≤ m → BallAllClosed m)
    {S : Finset V} {act : Finset (V × V)} (h : OneLoadBuilt G S act) : BallBound G S act := by
  induction h with
  | edge u v huv => exact ballBound_edge huv
  | face S act m u v x he J hJ hlong hodd hS ih =>
    intro L Ω A hcard hΩ hA hinv
    have hact : ∀ a b, (a, b) ∈ act → a ∈ S ∧ b ∈ S := fun a b hab => hS.act_mem hab
    have hxm : ∀ j, x j ∈ S ∪ univ.image x := fun j =>
      mem_union_right _ (mem_image_of_mem _ (mem_univ j))
    -- old edges keep their tags
    have hsame : ∀ a ∈ S, ∀ b ∈ S, ((a, b) ∈ act ∪ earPairs u v x J ↔ (a, b) ∈ act) := by
      intro a ha b hb
      refine ⟨fun h => ?_, fun h => mem_union_left _ h⟩
      rcases mem_union.mp h with h1 | h1
      · exact h1
      · simp only [earPairs, mem_union, mem_image, Prod.mk.injEq] at h1
        rcases h1 with ⟨j, _, rfl, rfl⟩ | ⟨j, _, rfl, rfl⟩
        · exact absurd ⟨ha, hb⟩ (he.earPath_not_both j)
        · exact absurd ⟨hb, ha⟩ (he.earPath_not_both j)
    -- the profiles of the path edges
    have hEa : ∀ j ∈ J, InBall (pathList (L u) (L v) (fun j => L (x j)) j.castSucc)
        (pathList (L u) (L v) (fun j => L (x j)) j.succ) (earE Ω u v x j)
        (A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc)) := by
      intro j hj
      rw [pathList_eq_earPath, pathList_eq_earPath]
      have hm := he.mem_act_iff hact J j
      exact InBall.mul (hA _ _).le (hA _ _).le
        ((hinv _ (he.earPath_mem _) _ (he.earPath_mem _) (he.earPath_adj j)).1 (hm.1.mpr hj))
        ((hinv _ (he.earPath_mem _) _ (he.earPath_mem _) (he.earPath_adj j).symm).1
          (hm.2.mpr hj)).swap
    have hEt : ∀ j ∉ J, Dominant (pathList (L u) (L v) (fun j => L (x j)) j.castSucc)
        (pathList (L u) (L v) (fun j => L (x j)) j.succ) (earE Ω u v x j)
        (A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc)) := by
      intro j hj
      rw [pathList_eq_earPath, pathList_eq_earPath]
      have hm := he.mem_act_iff hact J j
      exact Dominant.mul (hA _ _).le (hA _ _).le
        ((hinv _ (he.earPath_mem _) _ (he.earPath_mem _) (he.earPath_adj j)).2
          fun h => hj (hm.1.mp h))
        ((hinv _ (he.earPath_mem _) _ (he.earPath_mem _) (he.earPath_adj j).symm).2
          fun h => hj (hm.2.mp h)).swap
    have hE0 : ∀ j c d, 0 ≤ earE Ω u v x j c d := fun j c d =>
      mul_nonneg (hΩ _ _ _ _) (hΩ _ _ _ _)
    have hApos : ∀ j : Fin (m + 1), 0 < A (earPath u v x j.castSucc) (earPath u v x j.succ)
        * A (earPath u v x j.succ) (earPath u v x j.castSucc) := fun j =>
      mul_pos (hA _ _) (hA _ _)
    have hEany : ∀ j, InBall (pathList (L u) (L v) (fun j => L (x j)) j.castSucc)
        (pathList (L u) (L v) (fun j => L (x j)) j.succ) (earE Ω u v x j)
        (A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc)) := fun j => by
      by_cases hj : j ∈ J
      · exact hEa j hj
      · exact (hEt j hj).inBall (hApos j).le
    have hcu := hcard u (mem_union_left _ he.hu)
    have hcv := hcard v (mem_union_left _ he.hv)
    have hci : ∀ j, (L (x j)).card = 3 := fun j => hcard (x j) (hxm j)
    refine step_face he L Ω A hcard hΩ hA hsame hinv (fun huvact => ?_) (fun huvact => ?_) ih
    · -- the root edge is active
      by_cases hm2 : 2 ≤ m
      · rcases hlong hm2 huvact with hJ1 | hoddm
        · -- an ear of two or more vertices with at most one active path edge
          obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin (m + 1), ∀ j, j ≠ j₀ → j ∉ J := by
            rcases Finset.eq_empty_or_nonempty J with hJe | ⟨j₀, hj₀⟩
            · exact ⟨0, fun j _ => by simp [hJe]⟩
            · refine ⟨j₀, fun j hj hjJ => hj ?_⟩
              exact Finset.card_le_one.mp hJ1 j hjJ j₀ hj₀
          exact hface m hm2 (L u) (L v) (fun j => L (x j)) hcu hcv hci j₀ (earE Ω u v x) hE0 _
            hApos (hEany j₀) fun j hj => hEt j (hj₀ j hj)
        · -- an ear with an odd number of vertices: any path edges may be active
          have h3 : 3 ≤ m := by
            obtain ⟨r, hr⟩ := hoddm
            omega
          exact hall m hoddm h3 (L u) (L v) (fun j => L (x j)) hcu hcv hci (earE Ω u v x) hE0 _
            hApos hEany
      · -- a triangle
        have hm1 : m = 1 := by have := he.hm; omega
        subst hm1
        have key := ballTriClosed (L u) (L v) (fun j => L (x j)) hcu hcv hci (earE Ω u v x) hE0 _ hApos hEany
        rw [faceConst3_one, one_mul]
        exact key
    · -- the root edge is tame: a face of odd length with tame sides
      have hJe : J = ∅ := by
        by_contra hne
        exact huvact (hJ (Finset.nonempty_iff_ne_empty.mpr hne))
      exact hdom m (hodd huvact) (L u) (L v) (fun j => L (x j)) hci (earE Ω u v x) hE0 _ hApos
        fun j => hEt j (by simp [hJe])

variable (G)

/-- Three colours with at most one loaded edge below every long face, given closure under
single faces. `Outerplanar/LongFace.lean` proves the closure and states the theorem without
this hypothesis (`ecc_three_of_oneLoadBuilt`). -/
theorem ecc_three_of_oneLoadBuilt_of_face (hface : ∀ m, 2 ≤ m → BallFaceClosed m)
    (hdom : ∀ m, Odd m → DomFaceClosed m) (hall : ∀ m, Odd m → 3 ≤ m → BallAllClosed m)
    {act : Finset (V × V)} (h : OneLoadBuilt G univ act) : G.ECCAt 3 := by
  intro L hL
  have key := ballBound_of_oneLoadBuilt hface hdom hall h L neProfile (fun _ _ => 1)
    (fun x _ => hL x) (fun _ _ c d => by unfold neProfile; split_ifs <;> norm_num)
    (fun _ _ => one_pos)
    (fun a _ b _ _ => ⟨fun _ => inBall_ne (L a) (L b), fun _ => dominant_ne (L a) (L b)⟩)
  rw [Finset.prod_const_one, mul_one, ZG_univ_eq_col, ZG_univ_eq_col] at key
  have key' : (G.colConst 3 : ℝ) ≤ (G.col L : ℝ) := key
  exact_mod_cast key'

/-- The same from the bare form of the face property. -/
theorem ecc_three_of_oneLoadBuilt_of_bare (hbare : ∀ m, 2 ≤ m → BallFaceBare m)
    (hdom : ∀ m, Odd m → DomFaceClosed m) (hall : ∀ m, Odd m → 3 ≤ m → BallAllClosed m)
    {act : Finset (V × V)} (h : OneLoadBuilt G univ act) : G.ECCAt 3 :=
  ecc_three_of_oneLoadBuilt_of_face G (fun m hm => ballFaceClosed_of_bare (hbare m hm)) hdom hall
    h

end Outerplanar
