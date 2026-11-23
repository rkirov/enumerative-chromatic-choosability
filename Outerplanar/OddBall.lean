/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.OddFace
import Outerplanar.Walks

/-!
# Faces of odd length with every path edge loaded

A face with an odd number `m ≥ 3` of interior vertices maps the ball class on *all* its path
edges to the ball class on its root edge (`ballOddClosed`). Triangles do the same
(`ballTriClosed`, `Outerplanar/OneLoad.lean`); squares do not.

The lists along the path are enumerated so that equal colours of consecutive lists get equal
indices (`exists_aligned`). The colourings of the path that use only good pairs are then the
walks on three indices, the root family is the set of cells `(a, σ b)`, `a ≠ b`, for a bijection
`σ` of the indices, and the statement is `walks_ball` of `Outerplanar/Walks.lean`.

This is a result of this repository's 2026-11 AI research collaboration.
-/

namespace Outerplanar

open Finset

/-! ### The tables of a path -/

/-- The profile of an edge read through enumerations of its two lists. -/
def idxM (E : ℕ → ℕ → ℝ) (ζ ξ : Fin 3 → ℕ) : Fin 3 → Fin 3 → ℝ := fun x y => E (ζ x) (ξ y)

/-- The tables of a path: `ζ₀` enumerates the list of the first vertex, `ζs` those of the
others. -/
def mkMs : (Fin 3 → ℕ) → List (Fin 3 → ℕ) → List (ℕ → ℕ → ℝ) → List (Fin 3 → Fin 3 → ℝ)
  | _, [], _ => []
  | _, _ :: _, [] => []
  | ζ₀, ζ₁ :: ζs, E :: Es => idxM E ζ₀ ζ₁ :: mkMs ζ₁ ζs Es

theorem mkMs_length : ∀ (ζ₀ : Fin 3 → ℕ) (ζs : List (Fin 3 → ℕ)) (Es : List (ℕ → ℕ → ℝ)),
    ζs.length = Es.length → (mkMs ζ₀ ζs Es).length = Es.length
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | ζ₀, ζ₁ :: ζs, E :: Es, h => by
    rw [mkMs, List.length_cons, List.length_cons, mkMs_length ζ₁ ζs Es (by simpa using h)]

/-- The ball class on every edge of a path, in the form of lists. -/
def ChainBall : Finset ℕ → List (Finset ℕ) → List (ℕ → ℕ → ℝ) → List ℝ → Prop
  | _, [], [], [] => True
  | S, L :: Vs, E :: Es, A :: As => InBall S L E A ∧ ChainBall L Vs Es As
  | _, _, _, _ => False

theorem pathList_tail {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin (m + 1) → Finset ℕ)
    (i : Fin (m + 2)) :
    pathList Lu Lv Li i.succ = pathList (Li 0) Lv (Fin.tail Li) i := by
  unfold pathList
  rw [Fin.cons_succ, Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]

theorem chain_of_fin : ∀ {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (A : Fin (m + 1) → ℝ),
    (∀ j : Fin (m + 1),
      InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) →
    ChainBall Lu (List.ofFn Li ++ [Lv]) (List.ofFn E) (List.ofFn A)
  | 0, Lu, Lv, Li, E, A, h => by
    have h0 := h 0
    have p0 : pathList Lu Lv Li (Fin.castSucc (0 : Fin 1)) = Lu :=
      consSnoc_zero _ _ _ _ (by simp)
    have p1 : pathList Lu Lv Li (Fin.succ (0 : Fin 1)) = Lv := consSnoc_last _ _ _ _ (by simp)
    rw [p0, p1] at h0
    simp only [List.ofFn_succ, List.ofFn_zero, List.nil_append]
    exact ⟨h0, trivial⟩
  | m + 1, Lu, Lv, Li, E, A, h => by
    have h0 := h 0
    have p0 : pathList Lu Lv Li (Fin.castSucc (0 : Fin (m + 2))) = Lu :=
      consSnoc_zero _ _ _ _ (by simp)
    have p1 : pathList Lu Lv Li (Fin.succ (0 : Fin (m + 2))) = Li 0 :=
      consSnoc_mid _ _ _ _ (0 : Fin (m + 1)) (by simp)
    rw [p0, p1] at h0
    have ih := chain_of_fin (Li 0) Lv (Fin.tail Li) (Fin.tail E) (Fin.tail A) (fun j => by
      have hj := h j.succ
      have e1 : (j.succ : Fin (m + 2)).castSucc = (j.castSucc).succ := rfl
      rw [e1, pathList_tail, pathList_tail] at hj
      exact hj)
    rw [List.ofFn_succ (f := Li), List.ofFn_succ (f := E), List.ofFn_succ (f := A)]
    exact ⟨h0, ih⟩

/-- Enumerations along a path with the ball class on every edge: consecutive ones are aligned,
so every table satisfies the ball inequalities for the pairs of different indices. -/
theorem frames : ∀ (Vs : List (Finset ℕ)) (Es : List (ℕ → ℕ → ℝ)) (As : List ℝ) (S : Finset ℕ)
    (ζ₀ : Fin 3 → ℕ), Function.Injective ζ₀ → (∀ a, ζ₀ a ∈ S) → (∀ L ∈ Vs, L.card = 3) →
    (∀ E ∈ Es, ∀ c d, 0 ≤ E c d) → ChainBall S Vs Es As →
    ∃ ζs : List (Fin 3 → ℕ),
      List.Forall₂ (fun (ζ : Fin 3 → ℕ) (L : Finset ℕ) => Function.Injective ζ ∧ ∀ a, ζ a ∈ L)
        ζs Vs ∧
      List.Forall₂ OffBall (mkMs ζ₀ ζs Es) As ∧ ∀ M ∈ mkMs ζ₀ ζs Es, ∀ a b, 0 ≤ M a b
  | [], [], [], _, _, _, _, _, _, _ => ⟨[], List.Forall₂.nil, List.Forall₂.nil, by simp [mkMs]⟩
  | [], [], _ :: _, _, _, _, _, _, _, h => absurd h (by simp [ChainBall])
  | [], _ :: _, _, _, _, _, _, _, _, h => absurd h (by simp [ChainBall])
  | _ :: _, [], _, _, _, _, _, _, _, h => absurd h (by simp [ChainBall])
  | _ :: _, _ :: _, [], _, _, _, _, _, _, h => absurd h (by simp [ChainBall])
  | L :: Vs, E :: Es, A :: As, S, ζ₀, hζ₀, hζ₀m, hV, hE0, h => by
    obtain ⟨hE, hrest⟩ := h
    obtain ⟨ξ, hξ, hξm, hal'⟩ := exists_aligned (hV L List.mem_cons_self) hζ₀
    have hal : ∀ a b, ζ₀ a = ξ b → a = b := fun a b e => hal' b a e.symm
    obtain ⟨ζs, h1, h2, h3⟩ := frames Vs Es As L ξ hξ hξm
      (fun L' hL' => hV L' (List.mem_cons_of_mem _ hL'))
      (fun E' hE' => hE0 E' (List.mem_cons_of_mem _ hE')) hrest
    have hidx := hE.idx hζ₀ hξ hζ₀m hξm
    have hcompat : Compat id (fun c d => decide (ζ₀ c = ξ d)) :=
      ⟨Function.injective_id, fun c d hcd => hal c d (of_decide_eq_true hcd)⟩
    have hoff : OffBall (idxM E ζ₀ ξ) A := fun j c d hcd =>
      hidx id hcompat j c d (decide_eq_false fun e => hcd (hal c d e))
    refine ⟨ξ :: ζs, List.Forall₂.cons ⟨hξ, hξm⟩ h1, ?_, ?_⟩
    · rw [mkMs]
      exact List.Forall₂.cons hoff h2
    · intro M hM a b
      rw [mkMs] at hM
      rcases List.mem_cons.mp hM with rfl | hM'
      · exact hE0 E List.mem_cons_self _ _
      · exact h3 M hM' a b

/-! ### Walks are colourings -/

/-- The walks on the indices are colourings of the path. -/
theorem pw_le_psum : ∀ (Vs : List (Finset ℕ)) (Es : List (ℕ → ℕ → ℝ)) (ζs : List (Fin 3 → ℕ))
    (ζ₀ : Fin 3 → ℕ), Es.length = Vs.length →
    List.Forall₂ (fun (ζ : Fin 3 → ℕ) (L : Finset ℕ) => Function.Injective ζ ∧ ∀ a, ζ a ∈ L)
      ζs Vs →
    (∀ E ∈ Es, ∀ c d, 0 ≤ E c d) → ∀ a b,
    pw (mkMs ζ₀ ζs Es) a b ≤ psum Vs Es (ζ₀ a) ((ζs.getLastD ζ₀) b)
  | [], Es, [], ζ₀, _, _, _, a, b => by
    rw [mkMs, pw, psum_nil]
    show (if a = b then (1 : ℝ) else 0) ≤ if ζ₀ a = ζ₀ b then 1 else 0
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, ite_false]
      split_ifs <;> norm_num
  | [], _, _ :: _, _, _, h, _, _, _ => by cases h
  | _ :: _, _, [], _, _, h, _, _, _ => by cases h
  | L :: Vs, [], ζ₁ :: ζs, ζ₀, hlen, _, _, a, b => by simp at hlen
  | L :: Vs, E :: Es, ζ₁ :: ζs, ζ₀, hlen, h, hE0, a, b => by
    obtain ⟨⟨hζ₁, hζ₁m⟩, hrest⟩ := List.forall₂_cons.mp h
    have hEs : ∀ E' ∈ Es, ∀ c d, 0 ≤ E' c d := fun E' hE' => hE0 E' (List.mem_cons_of_mem _ hE')
    have hE := hE0 E List.mem_cons_self
    have ih := pw_le_psum Vs Es ζs ζ₁ (by simpa using hlen) hrest hEs
    rw [mkMs, pw, psum_cons, getLastD_cons]
    set d := (ζs.getLastD ζ₁) b with hd
    set f : ℕ → ℝ := fun x => E (ζ₀ a) x * psum Vs Es x d with hf
    have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (hE _ _) (psum_nonneg Vs Es hEs _ _)
    have hne : ζ₁ (a + 1) ≠ ζ₁ (a + 2) := fun e => by
      have := hζ₁ e
      fin_cases a <;> simp at this
    have hsub : ({ζ₁ (a + 1), ζ₁ (a + 2)} : Finset ℕ) ⊆ L := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hζ₁m _
      · rw [mem_singleton.mp hx]
        exact hζ₁m _
    have hsum : f (ζ₁ (a + 1)) + f (ζ₁ (a + 2)) ≤ ∑ x ∈ L, f x := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hf0 x
    refine le_trans ?_ hsum
    show idxM E ζ₀ ζ₁ a (a + 1) * pw (mkMs ζ₁ ζs Es) (a + 1) b
        + idxM E ζ₀ ζ₁ a (a + 2) * pw (mkMs ζ₁ ζs Es) (a + 2) b
      ≤ E (ζ₀ a) (ζ₁ (a + 1)) * psum Vs Es (ζ₁ (a + 1)) d
        + E (ζ₀ a) (ζ₁ (a + 2)) * psum Vs Es (ζ₁ (a + 2)) d
    exact add_le_add (mul_le_mul_of_nonneg_left (ih _ _) (hE _ _))
      (mul_le_mul_of_nonneg_left (ih _ _) (hE _ _))

/-! ### The theorem -/

theorem faceConst3_eq_dN : ∀ m, faceConst3 m = (dN (m + 1) : ℝ)
  | 0 => by norm_num [faceConst3, dN_succ, dN_zero, sN_zero]
  | 1 => by
    rw [faceConst3_one]
    norm_num [dN_succ, sN_succ, dN_zero, sN_zero]
  | m + 2 => by
    have h1 := dN_add_two (m + 1)
    have h2 := dN_succ (m + 1)
    have h3 := two_pow_eq (m + 1)
    have h : dN (m + 2 + 1) = dN (m + 1) + 2 ^ (m + 1) := by
      show dN (m + 1 + 2) = _
      omega
    rw [faceConst3_add_two, faceConst3_eq_dN m, h]
    push_cast
    ring

theorem forall₂_getLastD {P : (Fin 3 → ℕ) → Finset ℕ → Prop} :
    ∀ (ζs : List (Fin 3 → ℕ)) (Vs : List (Finset ℕ)) (ζ₀ : Fin 3 → ℕ) (S : Finset ℕ),
    List.Forall₂ P ζs Vs → P ζ₀ S → P (ζs.getLastD ζ₀) (Vs.getLastD S)
  | [], [], _, _, _, h => h
  | ζ :: ζs, L :: Vs, ζ₀, S, h, _ => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    rw [getLastD_cons, getLastD_cons]
    exact forall₂_getLastD ζs Vs ζ L h2 h1
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h

/-- **Faces of odd length preserve the ball class with every path edge loaded.** -/
theorem ballOddClosed (m : ℕ) (hodd : Odd m) (h3 : 3 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  refine inBall_of_idx hLu hLv fun α β hα hβ hαm hβm _ => ⟨id, Function.bijective_id, ?_⟩
  intro j c d _
  set Vs := List.ofFn Li ++ [Lv] with hVs
  have hVcard : ∀ L ∈ Vs, L.card = 3 := by
    intro L hL
    rcases List.mem_append.mp hL with h | h
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp h
      exact hLi i
    · rw [List.mem_singleton.mp h]
      exact hLv
  have hEs0 : ∀ E' ∈ List.ofFn E, ∀ c d, 0 ≤ E' c d := by
    intro E' hE' c d
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hE'
    exact hE0 i c d
  have hAs : ∀ A' ∈ List.ofFn A, 0 < A' := by
    intro A' hA'
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hA'
    exact hA i
  obtain ⟨ζs, hζs, hOff, hMnn⟩ := frames Vs (List.ofFn E) (List.ofFn A) Lu α hα hαm hVcard hEs0
    (chain_of_fin Lu Lv Li E A hE)
  have hlenV : Vs.length = m + 1 := by simp [hVs]
  have hlenE : (List.ofFn E).length = m + 1 := List.length_ofFn
  have hlenζ : ζs.length = m + 1 := by rw [hζs.length_eq, hlenV]
  set Ms := mkMs α ζs (List.ofFn E) with hMs
  have hlenM : Ms.length = m + 1 := by
    rw [hMs, mkMs_length _ _ _ (by rw [hlenζ, hlenE]), hlenE]
  -- the enumeration of the last list
  have hend : Function.Injective (ζs.getLastD α) ∧ ∀ a, (ζs.getLastD α) a ∈ Lv := by
    have h := forall₂_getLastD (P := fun ζ L => Function.Injective ζ ∧ ∀ a, ζ a ∈ L) ζs Vs α Lu
      hζs ⟨hα, hαm⟩
    have e : Vs.getLastD Lu = Lv := by
      rw [hVs, getLastD_append]
      rfl
    rwa [e] at h
  have himg : ∀ b, ∃ x, (ζs.getLastD α) x = β b := fun b => by
    have hb : β b ∈ univ.image (ζs.getLastD α) := by
      rw [image_enum hLv hend.1 hend.2]
      exact hβm b
    obtain ⟨x, -, hx⟩ := mem_image.mp hb
    exact ⟨x, hx⟩
  choose σ hσ using himg
  have hσinj : Function.Injective σ := fun b b' e => hβ (by rw [← hσ b, ← hσ b', e])
  obtain ⟨r, hr⟩ := hodd
  have key := walks_ball Ms (List.ofFn A) (r + 1) (by omega) (by rw [hlenM]; omega) hMnn hAs hOff
    σ hσinj j c (σ d)
  have hp := pw_nonneg Ms hMnn
  have hcell : ∀ a b : Fin 3, pw Ms a (σ b) ≤ faceSum Li (fun _ _ => 1) E (α a) (β b) := fun a b => by
    rw [faceSum_eq_psum Li Lv E (α a) (β b) (hβm b), ← hσ b]
    exact pw_le_psum Vs (List.ofFn E) ζs α (by rw [hlenE, hlenV]) hζs hEs0 a (σ b)
  show (faceConst3 m * ∏ j, A j) ^ 600
    ≤ (∏ k ∈ univ.erase j, faceSum Li (fun _ _ => 1) E (α (offPair k).1) (β (offPair k).2)) ^ 100
      * faceSum Li (fun _ _ => 1) E (α (offPair j).1) (β (offPair j).2) ^ 91
      * faceSum Li (fun _ _ => 1) E (α c) (β d) ^ 9
  calc (faceConst3 m * ∏ j, A j) ^ 600
      = ((dN Ms.length : ℝ) * (List.ofFn A).prod) ^ 600 := by
        rw [hlenM, ← faceConst3_eq_dN, List.prod_ofFn]
    _ ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (σ (offPair k).2)) ^ 100
        * pw Ms (offPair j).1 (σ (offPair j).2) ^ 91 * pw Ms c (σ d) ^ 9 := key
    _ ≤ _ := by
        refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (prod_nonneg fun k _ => hp _ _)
          (Finset.prod_le_prod₀ (fun k _ => hp _ _) fun k _ => hcell _ _) _)
          (pow_le_pow_left₀ (hp _ _) (hcell _ _) _) (pow_nonneg (hp _ _) _)
          (pow_nonneg (prod_nonneg fun k _ => (hp _ _).trans (hcell _ _)) _))
          (pow_le_pow_left₀ (hp _ _) (hcell _ _) _) (pow_nonneg (hp _ _) _)
          (mul_nonneg (pow_nonneg (prod_nonneg fun k _ => (hp _ _).trans (hcell _ _)) _)
            (pow_nonneg ((hp _ _).trans (hcell _ _)) _))

end Outerplanar
