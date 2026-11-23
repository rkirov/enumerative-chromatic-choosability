/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Arms

/-!
# Faces of odd length are transparent

A path with `m` interior vertices, each with a list of three colours, has at least
`(2 ^ (m + 1) - 1) / 3` proper colourings between any two given end colours when `m` is odd, and
at least `(2 ^ (m + 1) - 2) / 3` when `m` is even (`path_count`). For odd `m` the first number is
the constant of a face with `m` interior vertices, the number of colourings of the path from three
colours between two different end colours. For even `m` the bound is one short of that constant,
and the square with lists `012, 012, 123, 123` and end colours `0, 3` attains it.

So a face of odd length whose path edges carry greedy profiles (`Dominant`: at least the constant
on every pair of distinct colours) has a greedy profile on its root edge, with the constant of the
constant-list count: `domFaceClosed_odd`. A piece all of whose faces are odd therefore behaves
like a plain edge, and only faces of even length can load an edge. This is the property
`DomFaceClosed` that `Outerplanar/OneLoad.lean` asks for.

The proof of `path_count` carries three bounds on the number `H x` of colourings of the rest of
the path as a function of the colour `x` before it: on one value, on the sum of two values and
on the sum of three values at different colours.

This is a result of this repository's 2026-11 AI research collaboration.
-/

namespace Outerplanar

open Finset

/-! ### The bound -/

/-- The lower bound on the number of proper colourings of a path with `m` interior vertices
between two given colours: `0, 1, 2, 5, 10, 21, 42, …`. -/
noncomputable def oddB : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (m + 2) => oddB m + 2 ^ (m + 1)

theorem oddB_add_two (m : ℕ) : oddB (m + 2) = oddB m + 2 ^ (m + 1) := by
  rw [oddB]

theorem oddB_nonneg : ∀ m, 0 ≤ oddB m
  | 0 => by rw [oddB]
  | 1 => by rw [oddB]; exact zero_le_one
  | (m + 2) => by
    rw [oddB_add_two]
    have := oddB_nonneg m
    positivity

/-- For an odd number of interior vertices the bound is the constant of the face. -/
theorem oddB_odd : ∀ k : ℕ, oddB (2 * k + 1) = faceConst3 (2 * k + 1)
  | 0 => by rw [faceConst3_one, oddB]
  | (k + 1) => by
    have e : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [e, oddB_add_two, oddB_odd k, faceConst3_add_two]

/-! ### Sums over a list of three colours -/

theorem sum_three {L : Finset ℕ} (hL : L.card = 3) (f : ℕ → ℝ) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∑ l ∈ L, f l = f a + f b + f c := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hL
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]
  ring

/-- A list of three colours has two different colours other than a given one. -/
theorem exists_two_avoid {L : Finset ℕ} (hL : L.card = 3) (x : ℕ) :
    ∃ a ∈ L, ∃ b ∈ L, a ≠ b ∧ a ≠ x ∧ b ≠ x := by
  have h1 := Finset.pred_card_le_card_erase (s := L) (a := x)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (L.erase x).card)
  exact ⟨a, (Finset.mem_erase.mp ha).2, b, (Finset.mem_erase.mp hb).2, hab,
    (Finset.mem_erase.mp ha).1, (Finset.mem_erase.mp hb).1⟩

/-! ### Counting the colourings of a path -/

/-- **Colourings of a path between two given colours.** `Vs` are the lists of the interior
vertices, `Lv` the list of the last vertex, `d` its colour; `x` is the colour of the first
vertex. The three statements bound the number of proper colourings from below for one colour
`x`, for two different colours together and for three different colours together. -/
theorem path_count : ∀ (Vs : List (Finset ℕ)) (Lv : Finset ℕ), (∀ L ∈ Vs, L.card = 3) →
    ∀ d ∈ Lv,
    (∀ x, oddB Vs.length ≤ psum (Vs ++ [Lv]) (nes (Vs.length + 1)) x d) ∧
    (∀ x x', x ≠ x' → oddB (Vs.length + 1)
      ≤ psum (Vs ++ [Lv]) (nes (Vs.length + 1)) x d
        + psum (Vs ++ [Lv]) (nes (Vs.length + 1)) x' d) ∧
    (∀ x x' x'', x ≠ x' → x ≠ x'' → x' ≠ x'' → (2 : ℝ) ^ (Vs.length + 1)
      ≤ psum (Vs ++ [Lv]) (nes (Vs.length + 1)) x d
        + psum (Vs ++ [Lv]) (nes (Vs.length + 1)) x' d
        + psum (Vs ++ [Lv]) (nes (Vs.length + 1)) x'' d)
  | [], Lv, _, d, hd => by
    have e : ∀ x, psum ([] ++ [Lv]) (nes (([] : List (Finset ℕ)).length + 1)) x d = neP x d :=
      fun x => psum_single Lv neP x d hd
    simp only [e]
    refine ⟨fun x => ?_, fun x x' hxx' => ?_, fun x x' x'' h1 h2 h3 => ?_⟩
    · show oddB 0 ≤ neP x d
      rw [oddB]
      exact neP_nonneg x d
    · show oddB 1 ≤ neP x d + neP x' d
      rw [oddB]
      unfold neP
      split_ifs <;> first | (exfalso; omega) | norm_num
    · show (2 : ℝ) ^ (0 + 1) ≤ neP x d + neP x' d + neP x'' d
      unfold neP
      split_ifs <;> first | (exfalso; omega) | norm_num
  | L :: Vs, Lv, hV, d, hd => by
    obtain ⟨ha, hb, hc⟩ := path_count Vs Lv (fun L' hL' => hV L' (List.mem_cons_of_mem _ hL')) d hd
    have hL : L.card = 3 := hV L List.mem_cons_self
    -- the number of colourings of the rest of the path, by the colour before it
    set H : ℕ → ℝ := fun l => psum (Vs ++ [Lv]) (nes (Vs.length + 1)) l d with hH
    have hH0 : ∀ l, 0 ≤ H l := fun l => (oddB_nonneg _).trans (ha l)
    have hstep : ∀ x, psum ((L :: Vs) ++ [Lv]) (nes (Vs.length + 1 + 1)) x d
        = ∑ l ∈ L, neP x l * H l := fun x => rfl
    have hsum : (2 : ℝ) ^ (Vs.length + 1) ≤ ∑ l ∈ L, H l := by
      obtain ⟨a, b, c, hab, hac, hbc, e⟩ := sum_three hL H
      rw [e]
      exact hc a b c hab hac hbc
    simp only [List.length_cons, hstep]
    refine ⟨fun x => ?_, fun x x' hxx' => ?_, fun x x' x'' h1 h2 h3 => ?_⟩
    · -- one colour: two colours of `L` avoid it
      obtain ⟨a, haL, b, hbL, hab, hax, hbx⟩ := exists_two_avoid hL x
      have hterm : ∀ l ∈ L, ((if l = a then (1 : ℝ) else 0) + (if l = b then 1 else 0)) * H l
          ≤ neP x l * H l := fun l _ => by
        refine mul_le_mul_of_nonneg_right ?_ (hH0 l)
        unfold neP
        split_ifs <;> first | (exfalso; omega) | norm_num
      have e : ∑ l ∈ L, ((if l = a then (1 : ℝ) else 0) + (if l = b then 1 else 0)) * H l
          = H a + H b := by
        simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
          Finset.sum_ite_eq', haL, hbL, ite_true]
      calc oddB (Vs.length + 1) ≤ H a + H b := hb a b hab
        _ = _ := e.symm
        _ ≤ _ := Finset.sum_le_sum hterm
    · -- two colours: every colour of `L` avoids one of them, and one avoids both
      obtain ⟨t, htL, htx, htx'⟩ := exists_avoid hL x x'
      have hterm : ∀ l ∈ L, ((1 : ℝ) + (if l = t then 1 else 0)) * H l
          ≤ neP x l * H l + neP x' l * H l := fun l _ => by
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hH0 l)
        unfold neP
        split_ifs <;> first | (exfalso; omega) | norm_num
      have e : ∑ l ∈ L, ((1 : ℝ) + (if l = t then 1 else 0)) * H l = ∑ l ∈ L, H l + H t := by
        simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
          Finset.sum_ite_eq', htL, ite_true]
      rw [← Finset.sum_add_distrib]
      calc oddB (Vs.length + 1 + 1) = oddB Vs.length + 2 ^ (Vs.length + 1) := oddB_add_two _
        _ ≤ ∑ l ∈ L, H l + H t := by linarith [ha t]
        _ = _ := e.symm
        _ ≤ _ := Finset.sum_le_sum hterm
    · -- three colours: every colour of `L` avoids two of them
      have hterm : ∀ l ∈ L, (2 : ℝ) * H l
          ≤ neP x l * H l + neP x' l * H l + neP x'' l * H l := fun l _ => by
        rw [← add_mul, ← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hH0 l)
        unfold neP
        split_ifs <;> first | (exfalso; omega) | norm_num
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      calc (2 : ℝ) ^ (Vs.length + 1 + 1) = 2 * 2 ^ (Vs.length + 1) := by ring
        _ ≤ 2 * ∑ l ∈ L, H l := by linarith
        _ = ∑ l ∈ L, 2 * H l := Finset.mul_sum _ _ _
        _ ≤ _ := Finset.sum_le_sum hterm

/-! ### Faces with greedy edges -/

/-- A face whose path edges carry greedy profiles has at least the product of their constants
for every proper colouring of its path. -/
theorem faceSum_ge_bare {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    {c d : ℕ} (hc : c ∈ Lu) (hd : d ∈ Lv) :
    (∏ j, A j) * faceSum Li (fun _ _ => 1) (fun _ => neP) c d
      ≤ faceSum Li (fun _ _ => 1) E c d := by
  unfold faceSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  simp only [Finset.prod_const_one, one_mul]
  have hmem : ∀ i : Fin (m + 2), pathCol c d g i ∈ pathList Lu Lv Li i := fun i =>
    pathCol_mem hc hd (fun j => Fintype.mem_piFinset.mp hg j) i
  by_cases hall : ∀ j : Fin (m + 1), pathCol c d g j.castSucc ≠ pathCol c d g j.succ
  · have e1 : ∏ j : Fin (m + 1), neP (pathCol c d g j.castSucc) (pathCol c d g j.succ) = 1 :=
      Finset.prod_eq_one fun j _ => by simp [neP, hall j]
    rw [e1, mul_one]
    exact Finset.prod_le_prod₀ (fun j _ => hA j) fun j _ =>
      hE j _ (hmem _) _ (hmem _) (hall j)
  · obtain ⟨j, heq⟩ : ∃ j : Fin (m + 1), pathCol c d g j.castSucc = pathCol c d g j.succ := by
      by_contra hne
      exact hall fun j heq => hne ⟨j, heq⟩
    have e0 : ∏ j : Fin (m + 1), neP (pathCol c d g j.castSucc) (pathCol c d g j.succ) = 0 :=
      Finset.prod_eq_zero (mem_univ j) (by simp [neP, heq])
    rw [e0, mul_zero]
    exact Finset.prod_nonneg fun j _ => hE0 _ _ _

/-- **Faces of odd length preserve greedy profiles.** With an odd number of interior vertices and
greedy profiles on all path edges, the profile of the face is greedy on its root edge, with the
constant of the constant-list count. -/
theorem domFaceClosed_odd (m : ℕ) (hm : Odd m) : DomFaceClosed m := by
  intro Lu Lv Li hLi E hE0 A hA hE c hc d hd _
  obtain ⟨k, rfl⟩ := hm
  have h1 := faceSum_ge_bare Lu Lv Li E hE0 A (fun j => (hA j).le) hE hc hd
  have h2 : faceSum Li (fun _ _ => 1) (fun _ => neP) c d
      = psum (List.ofFn Li ++ [Lv]) (nes (2 * k + 1 + 1)) c d := by
    rw [faceSum_eq_psum Li Lv _ c d hd, List.ofFn_const]
    rfl
  have hcard : ∀ L ∈ List.ofFn Li, L.card = 3 := fun L hL => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hL
    exact hLi i
  have h3 := (path_count (List.ofFn Li) Lv hcard d hd).1 c
  rw [List.length_ofFn, oddB_odd] at h3
  calc faceConst3 (2 * k + 1) * ∏ j, A j
      = (∏ j, A j) * faceConst3 (2 * k + 1) := mul_comm _ _
    _ ≤ (∏ j, A j) * faceSum Li (fun _ _ => 1) (fun _ => neP) c d :=
        mul_le_mul_of_nonneg_left (by rw [h2]; exact h3)
          (Finset.prod_nonneg fun j _ => (hA j).le)
    _ ≤ _ := h1

end Outerplanar
