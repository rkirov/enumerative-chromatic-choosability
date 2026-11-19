/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.VBall

/-!
# Path sums over lists of lists

For the induction on the length of a face it is convenient to describe a path by the list `Vs`
of the colour lists of its vertices *after* the first one (the last entry is the list of the end
vertex), with one edge profile per entry. `psum Vs Es c d` is the sum over the colourings of the
path with first colour `c` and last colour `d` of the product of the edge profiles; the empty
path gives the identity.

* `psum_append` — splitting a path at a vertex;
* `faceSum_eq_psum` — the face sum of `Outerplanar/FaceDefs.lean` is a path sum;
* `psum_reverse` — reading a path backwards;
* `free_end_ge`, `free_start_ge` — a path of `n` ordinary edges with one free end has at least
  `2 ^ n` proper colourings.
-/

namespace Outerplanar

open Finset

/-- The profile of an ordinary edge. -/
def neP (c d : ℕ) : ℝ := if c ≠ d then 1 else 0

theorem neP_nonneg (c d : ℕ) : 0 ≤ neP c d := by
  unfold neP
  split_ifs <;> norm_num

/-- The path sum: `Vs` are the lists of the vertices after the first one, `Es` the profiles of
the edges. -/
noncomputable def psum : List (Finset ℕ) → List (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | [], _, c, d => if c = d then 1 else 0
  | _ :: _, [], _, _ => 0
  | L :: Vs, E :: Es, c, d => ∑ x ∈ L, E c x * psum Vs Es x d

theorem psum_nil (Es : List (ℕ → ℕ → ℝ)) (c d : ℕ) : psum [] Es c d = if c = d then 1 else 0 := by
  cases Es <;> rfl

theorem psum_cons (L : Finset ℕ) (Vs : List (Finset ℕ)) (E : ℕ → ℕ → ℝ)
    (Es : List (ℕ → ℕ → ℝ)) (c d : ℕ) :
    psum (L :: Vs) (E :: Es) c d = ∑ x ∈ L, E c x * psum Vs Es x d := rfl

theorem psum_nonneg : ∀ (Vs : List (Finset ℕ)) (Es : List (ℕ → ℕ → ℝ)),
    (∀ E ∈ Es, ∀ c d, 0 ≤ E c d) → ∀ c d, 0 ≤ psum Vs Es c d
  | [], Es, _, c, d => by
    rw [psum_nil]
    split_ifs <;> norm_num
  | _ :: _, [], _, _, _ => le_rfl
  | L :: Vs, E :: Es, h, c, d => by
    rw [psum_cons]
    exact sum_nonneg fun x _ => mul_nonneg (h E List.mem_cons_self _ _)
      (psum_nonneg Vs Es (fun E' hE' => h E' (List.mem_cons_of_mem _ hE')) _ _)

/-- One edge. -/
theorem psum_single (L : Finset ℕ) (E : ℕ → ℕ → ℝ) (c d : ℕ) (hd : d ∈ L) :
    psum [L] [E] c d = E c d := by
  rw [psum_cons]
  simp only [psum_nil]
  rw [Finset.sum_eq_single d (fun x _ hx => by rw [ite_eq_right hx, mul_zero])
    (fun h => absurd hd h), ite_eq_left rfl, mul_one]

/-- **Splitting a path at a vertex** with list `X`. -/
theorem psum_append : ∀ (A : List (Finset ℕ)) (X : Finset ℕ) (B : List (Finset ℕ))
    (Ea Eb : List (ℕ → ℕ → ℝ)), Ea.length = A.length + 1 → ∀ c d,
    psum (A ++ X :: B) (Ea ++ Eb) c d = ∑ x ∈ X, psum (A ++ [X]) Ea c x * psum B Eb x d
  | [], X, B, Ea, Eb, hlen, c, d => by
    obtain ⟨E, rfl⟩ : ∃ E, Ea = [E] := by
      match Ea, hlen with
      | [E], _ => exact ⟨E, rfl⟩
    show psum (X :: B) (E :: Eb) c d = ∑ x ∈ X, psum [X] [E] c x * psum B Eb x d
    rw [psum_cons]
    exact Finset.sum_congr rfl fun x hx => by rw [psum_single X E c x hx]
  | L :: A, X, B, Ea, Eb, hlen, c, d => by
    obtain ⟨E, Ea', rfl⟩ : ∃ E Ea', Ea = E :: Ea' := by
      match Ea, hlen with
      | E :: Ea', _ => exact ⟨E, Ea', rfl⟩
    have hlen' : Ea'.length = A.length + 1 := by simpa using hlen
    show psum (L :: (A ++ X :: B)) (E :: (Ea' ++ Eb)) c d
      = ∑ x ∈ X, psum (L :: (A ++ [X])) (E :: Ea') c x * psum B Eb x d
    rw [psum_cons]
    simp only [psum_cons, psum_append A X B Ea' Eb hlen', Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => by ring

/-! ### The face sum as a path sum -/

/-- Peeling the first interior vertex of a face. -/
theorem faceSum_succ {m : ℕ} (Li : Fin (m + 1) → Finset ℕ) (E : Fin (m + 2) → ℕ → ℕ → ℝ)
    (c d : ℕ) :
    faceSum Li (fun _ _ => 1) E c d
      = ∑ x ∈ Li 0, E 0 c x * faceSum (Fin.tail Li) (fun _ _ => 1) (Fin.tail E) x d := by
  unfold faceSum
  simp only [Finset.prod_const_one, one_mul, Finset.mul_sum]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij' (fun xg _ => (Fin.cons xg.1 xg.2 : Fin (m + 1) → ℕ))
    (fun g _ => (g 0, Fin.tail g)) ?_ ?_ ?_ ?_ ?_
  · intro xg hxg
    rw [Fintype.mem_piFinset]
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (mem_product.mp hxg).1
    · exact Fintype.mem_piFinset.mp (mem_product.mp hxg).2 i
  · intro g hg
    exact mem_product.mpr ⟨Fintype.mem_piFinset.mp hg 0,
      Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hg i.succ⟩
  · intro xg _
    simp
  · intro g _
    exact Fin.cons_self_tail g
  · intro xg _
    have hpc : ∀ i : Fin (m + 2), pathCol c d (Fin.cons xg.1 xg.2 : Fin (m + 1) → ℕ) i.succ
        = pathCol xg.1 d xg.2 i := fun i => by
      unfold pathCol
      rw [Fin.cons_succ, ← Fin.cons_snoc_eq_snoc_cons]
    have h0 : pathCol c d (Fin.cons xg.1 xg.2 : Fin (m + 1) → ℕ) (Fin.castSucc 0) = c := by
      unfold pathCol
      rfl
    have h1 : pathCol c d (Fin.cons xg.1 xg.2 : Fin (m + 1) → ℕ) (Fin.succ 0) = xg.1 := by
      rw [hpc]
      unfold pathCol
      rfl
    have hR : ∏ j : Fin (m + 2), E j
          (pathCol c d (Fin.cons xg.1 xg.2 : Fin (m + 1) → ℕ) j.castSucc)
          (pathCol c d (Fin.cons xg.1 xg.2 : Fin (m + 1) → ℕ) j.succ)
        = E 0 c xg.1 * ∏ j : Fin (m + 1), Fin.tail E j (pathCol xg.1 d xg.2 j.castSucc)
          (pathCol xg.1 d xg.2 j.succ) := by
      rw [Fin.prod_univ_succ, h0, h1]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      have e1 : (j.succ : Fin (m + 2)).castSucc = (j.castSucc).succ := rfl
      rw [e1, hpc, hpc]
      rfl
    exact hR.symm

/-- **The face sum is a path sum.** -/
theorem faceSum_eq_psum : ∀ {m : ℕ} (Li : Fin m → Finset ℕ) (Lv : Finset ℕ)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (c d : ℕ), d ∈ Lv →
    faceSum Li (fun _ _ => 1) E c d = psum (List.ofFn Li ++ [Lv]) (List.ofFn E) c d
  | 0, Li, Lv, E, c, d, hd => by
    have e : faceSum Li (fun _ _ => 1) E c d = E 0 c d := by
      unfold faceSum
      have hg : ∀ g : Fin 0 → ℕ, (∏ _j : Fin 0, (1 : ℝ))
          * ∏ j : Fin 1, E j (pathCol c d g j.castSucc) (pathCol c d g j.succ) = E 0 c d :=
        fun g => by
          rw [Fin.prod_univ_one, Fin.prod_univ_zero, one_mul]
          have p0 : pathCol c d g (Fin.castSucc (0 : Fin 1)) = c :=
            consSnoc_zero _ _ _ _ (by simp)
          have p1 : pathCol c d g (Fin.succ (0 : Fin 1)) = d :=
            consSnoc_last _ _ _ _ (by simp)
          rw [p0, p1]
      simp only [hg]
      rw [Finset.sum_const, Fintype.card_piFinset, Fin.prod_univ_zero, one_smul]
    rw [e]
    show E 0 c d = psum [Lv] [E 0] c d
    rw [psum_single Lv (E 0) c d hd]
  | m + 1, Li, Lv, E, c, d, hd => by
    rw [faceSum_succ, List.ofFn_succ, List.ofFn_succ]
    show _ = psum (Li 0 :: (List.ofFn (fun i => Li i.succ) ++ [Lv]))
      (E 0 :: List.ofFn fun i => E i.succ) c d
    rw [psum_cons]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [faceSum_eq_psum (Fin.tail Li) Lv (Fin.tail E) x d hd]
    rfl

/-! ### Reading a path backwards -/

/-- **A path read backwards.** `Is` are the lists of the interior vertices. -/
theorem psum_reverse : ∀ (Is : List (Finset ℕ)) (Es : List (ℕ → ℕ → ℝ)) (Lu Lv : Finset ℕ),
    Es.length = Is.length + 1 → ∀ c ∈ Lu, ∀ d ∈ Lv,
    psum (Is ++ [Lv]) Es c d
      = psum (Is.reverse ++ [Lu]) (Es.reverse.map fun E a b => E b a) d c
  | [], Es, Lu, Lv, hlen, c, hc, d, hd => by
    obtain ⟨E, rfl⟩ : ∃ E, Es = [E] := by
      match Es, hlen with
      | [E], _ => exact ⟨E, rfl⟩
    show psum [Lv] [E] c d = psum [Lu] [fun a b => E b a] d c
    rw [psum_single Lv E c d hd, psum_single Lu _ d c hc]
  | L :: Is, Es, Lu, Lv, hlen, c, hc, d, hd => by
    obtain ⟨E, Es', rfl⟩ : ∃ E Es', Es = E :: Es' := by
      match Es, hlen with
      | E :: Es', _ => exact ⟨E, Es', rfl⟩
    have hlen' : Es'.length = Is.length + 1 := by simpa using hlen
    show psum (L :: (Is ++ [Lv])) (E :: Es') c d = _
    rw [psum_cons]
    have e : (L :: Is).reverse ++ [Lu] = Is.reverse ++ L :: [Lu] := by simp
    have e' : ((E :: Es').reverse.map fun E a b => E b a)
        = (Es'.reverse.map fun E a b => E b a) ++ [fun a b => E b a] := by simp
    rw [e, e', psum_append Is.reverse L [Lu] _ _ (by simp [hlen'])]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [psum_reverse Is Es' L Lv hlen' x hx d hd, psum_single Lu _ x c hc, mul_comm]

/-! ### Ordinary edges -/

/-- The profiles of `n` ordinary edges. -/
def nes (n : ℕ) : List (ℕ → ℕ → ℝ) := List.replicate n neP

theorem nes_succ (n : ℕ) : nes (n + 1) = neP :: nes n := rfl

theorem nes_nonneg (n : ℕ) : ∀ E ∈ nes n, ∀ c d, 0 ≤ E c d := fun E hE c d => by
  rw [List.eq_of_mem_replicate hE]
  exact neP_nonneg c d

/-- A list of three colours has at least two colours other than a given one. -/
theorem two_le_sum_neP {L : Finset ℕ} (hL : L.card = 3) (c : ℕ) :
    (2 : ℝ) ≤ ∑ x ∈ L, neP c x := by
  have h1 : ∑ x ∈ L, neP c x = ((L.erase c).card : ℝ) := by
    unfold neP
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_filter]
    simp only [Nat.cast_one]
    congr 1
    ext x
    simp [Finset.mem_erase, eq_comm, and_comm]
  rw [h1]
  have h2 := Finset.pred_card_le_card_erase (s := L) (a := c)
  have h3 : 2 ≤ (L.erase c).card := by omega
  exact_mod_cast h3

theorem two_le_sum_neP' {L : Finset ℕ} (hL : L.card = 3) (c : ℕ) :
    (2 : ℝ) ≤ ∑ x ∈ L, neP x c := by
  have e : ∑ x ∈ L, neP x c = ∑ x ∈ L, neP c x :=
    Finset.sum_congr rfl fun x _ => by unfold neP; simp [eq_comm]
  rw [e]
  exact two_le_sum_neP hL c

/-- **A free end**: a path of ordinary edges from a fixed colour, summed over the colour of its
last vertex, has at least `2 ^ n` colourings. -/
theorem free_end_ge : ∀ (A : List (Finset ℕ)) (X : Finset ℕ), (∀ L ∈ A, L.card = 3) →
    X.card = 3 → ∀ c, (2 : ℝ) ^ (A.length + 1) ≤ ∑ x ∈ X, psum (A ++ [X]) (nes (A.length + 1)) c x
  | [], X, _, hX, c => by
    have e : ∑ x ∈ X, psum [X] (nes 1) c x = ∑ x ∈ X, neP c x :=
      Finset.sum_congr rfl fun x hx => psum_single X neP c x hx
    show (2 : ℝ) ^ (0 + 1) ≤ ∑ x ∈ X, psum [X] (nes 1) c x
    rw [e, zero_add, pow_one]
    exact two_le_sum_neP hX c
  | L :: A, X, hA, hX, c => by
    have ih := free_end_ge A X (fun L' hL' => hA L' (List.mem_cons_of_mem _ hL')) hX
    have e : ∑ x ∈ X, psum ((L :: A) ++ [X]) (nes ((L :: A).length + 1)) c x
        = ∑ l ∈ L, neP c l * ∑ x ∈ X, psum (A ++ [X]) (nes (A.length + 1)) l x := by
      show ∑ x ∈ X, psum (L :: (A ++ [X])) (neP :: nes (A.length + 1)) c x = _
      simp only [psum_cons, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e]
    calc (2 : ℝ) ^ ((L :: A).length + 1) = 2 * 2 ^ (A.length + 1) := by
          rw [List.length_cons, pow_succ]; ring
      _ ≤ (∑ l ∈ L, neP c l) * 2 ^ (A.length + 1) :=
          mul_le_mul_of_nonneg_right (two_le_sum_neP (hA L List.mem_cons_self) c) (by positivity)
      _ = ∑ l ∈ L, neP c l * 2 ^ (A.length + 1) := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (ih l) (neP_nonneg c l)

/-- **A free start**: a path of ordinary edges to a fixed colour of its last vertex, summed over
the colour of its first vertex, has at least `2 ^ n` colourings. -/
theorem free_start_ge : ∀ (Vs : List (Finset ℕ)) (X₀ : Finset ℕ), (∀ L ∈ Vs, L.card = 3) →
    X₀.card = 3 → ∀ d ∈ Vs.getLastD X₀, (2 : ℝ) ^ Vs.length ≤ ∑ c ∈ X₀, psum Vs (nes Vs.length) c d
  | [], X₀, _, _, d, hd => by
    have hd' : d ∈ X₀ := hd
    simp only [psum_nil, List.length_nil, pow_zero]
    rw [Finset.sum_eq_single d (fun x _ hx => by rw [ite_eq_right hx]) (fun h => absurd hd' h),
      ite_eq_left rfl]
  | L :: Vs, X₀, hV, hX, d, hd => by
    have hd' : d ∈ Vs.getLastD L := by
      cases Vs with
      | nil => exact hd
      | cons L' Vs' => exact hd
    have ih := free_start_ge Vs L (fun L' hL' => hV L' (List.mem_cons_of_mem _ hL'))
      (hV L List.mem_cons_self) d hd'
    have e : ∑ c ∈ X₀, psum (L :: Vs) (nes (L :: Vs).length) c d
        = ∑ l ∈ L, (∑ c ∈ X₀, neP c l) * psum Vs (nes Vs.length) l d := by
      show ∑ c ∈ X₀, psum (L :: Vs) (neP :: nes Vs.length) c d = _
      simp only [psum_cons, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [e]
    calc (2 : ℝ) ^ (L :: Vs).length = 2 * 2 ^ Vs.length := by
          rw [List.length_cons, pow_succ]; ring
      _ ≤ 2 * ∑ l ∈ L, psum Vs (nes Vs.length) l d := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = ∑ l ∈ L, 2 * psum Vs (nes Vs.length) l d := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (two_le_sum_neP' hX l)
          (psum_nonneg _ _ (nes_nonneg _) _ _)

end Outerplanar
