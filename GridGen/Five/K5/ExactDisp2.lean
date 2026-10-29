/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.ExactDisp

/-!
# Height five at `k = 5`: dispatch against stored size vectors

`dispatch_of_searchX` with the size vectors of the table stored as literals (`hitS`), checked
once against the table (`dispatch_of_searchS`), so that a hit of the search is a list lookup.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-- The hit test against stored size vectors, in either orientation. -/
def hitS (S : List (List ℕ)) (xs : List ℕ) : Bool := S.contains xs || S.contains (revSizes xs)

theorem hitS_hitX {T : List XSpec} {S : List (List ℕ)} (hS : S = T.map fun sp => sizesOf sp.atoms)
    {xs : List ℕ} (h : hitS S xs = true) : hitX T xs = true := by
  subst hS
  simp only [hitS, Bool.or_eq_true, List.contains_iff_mem, List.mem_map] at h
  simp only [hitX, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with ⟨sp, hsp, e⟩ | ⟨sp, hsp, e⟩
  · exact ⟨sp, hsp, Or.inl e⟩
  · exact ⟨sp, hsp, Or.inr e⟩

/-- **Dispatch from a search** against stored size vectors. -/
theorem dispatch_of_searchS {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (T : List XSpec) (S : List (List ℕ))
    (E : List (List ℕ × ℕ)) (ord : List (ℕ × List ℕ × List ℕ))
    (hS : decide (S = T.map fun sp => sizesOf sp.atoms) = true)
    (hs : search E (fun a => hitS S (masks31.map a)) ord (fun _ => 0) (E.map fun _ => 0) = true ∧
      ordOk E ord = true)
    (hE : ∀ c ∈ E, lsum (fun k => (atomSet B₁ B₂ B₃ B₄ B₅ k).card) c.1 = c.2)
    (h7 : ∀ k, 0 < k → k < 32 → (atomSet B₁ B₂ B₃ B₄ B₅ k).card < 7) :
    ∃ sp ∈ T, AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅ ∨ AtomsMatch sp.toSpec5 B₅ B₄ B₃ B₂ B₁ := by
  have hS' := of_decide_eq_true hS
  obtain ⟨hs, hok⟩ := hs
  simp only [ordOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Nat.beq_eq, List.any_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hcov, hnod⟩, hind⟩, hnd⟩, hfl⟩ := hok
  refine hitX_atoms (hitS_hitX hS' ?_)
  have hs' : search E (fun a => hitS S (masks31.map a)) ord (fun _ => 0)
      (E.map fun c => lsum (fun _ => 0) c.1) = true := by
    have e : ∀ S : List ℕ, lsum (fun _ => 0) S = 0 := fun S => by
      induction S with
      | nil => rfl
      | cons m S ih => simp [lsum, ih]
    simpa [e] using hs
  have := search_sound E _ (fun k => (atomSet B₁ B₂ B₃ B₄ B₅ k).card) hE hnd ord (fun _ => 0) hnod
    hfl ?_ (fun _ => Nat.zero_le _) ?_ hs'
  · simpa using this
  · intro p hp
    refine ⟨?_, hind p hp, rfl⟩
    by_cases hk : p.1 = 0 ∨ 32 ≤ p.1
    · rw [atomSet_card_zero _ _ _ _ _ hk]; norm_num
    · exact h7 p.1 (by omega) (by omega)
  · intro k hk
    by_cases hk' : k = 0 ∨ 32 ≤ k
    · rw [atomSet_card_zero _ _ _ _ _ hk']
    · exfalso
      rcases hcov k (by omega) with h0 | ⟨p, hp, e⟩
      · omega
      · exact hk p hp e

/-! ### The search with evaluated partial sums -/

/-- Evaluate the entries of a list once. -/
def forceL : List ℕ → (List ℕ → Bool) → Bool
  | [], k => k []
  | x :: xs, k => forceN x fun x' => forceL xs fun xs' => k (x' :: xs')

theorem forceL_eq : ∀ (l : List ℕ) (k : List ℕ → Bool), forceL l k = k l
  | [], _ => rfl
  | x :: xs, k => by simp only [forceL, forceN_eq, forceL_eq xs]

/-- `search` with the partial sums evaluated at every node. -/
def searchF (E : List (List ℕ × ℕ)) (hit : (ℕ → ℕ) → Bool) :
    List (ℕ × List ℕ × List ℕ) → (ℕ → ℕ) → List ℕ → Bool
  | [], a, s => !(decide (s = E.map Prod.snd)) || hit a
  | p :: ord, a, s => ball5 7 fun v => forceL (addc s p.2.1 v) fun s' =>
      !(okL s' (E.map Prod.snd) p.2.2) || searchF E hit ord (upd a p.1 v) s'

theorem ball5_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ v, f v = g v) : ball5 n f = ball5 n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ball5, ih, h n]

theorem searchF_eq (E : List (List ℕ × ℕ)) (hit : (ℕ → ℕ) → Bool) :
    ∀ (ord : List (ℕ × List ℕ × List ℕ)) (a : ℕ → ℕ) (s : List ℕ),
      searchF E hit ord a s = search E hit ord a s
  | [], _, _ => rfl
  | p :: ord, a, s => by
    simp only [searchF, search]
    refine ball5_congr fun v => ?_
    rw [forceL_eq, searchF_eq E hit ord]

/-- The hit test with the size vector and its reflection evaluated once. -/
def hitF (S : List (List ℕ)) (a : ℕ → ℕ) : Bool :=
  forceL (masks31.map a) fun xs => forceL (revSizes xs) fun ys => S.contains xs || S.contains ys

theorem hitF_eq (S : List (List ℕ)) (a : ℕ → ℕ) : hitF S a = hitS S (masks31.map a) := by
  simp only [hitF, forceL_eq, hitS]

/-- `searchF` with the hit test `hitF`. -/
def searchFS (E : List (List ℕ × ℕ)) (S : List (List ℕ)) :
    List (ℕ × List ℕ × List ℕ) → (ℕ → ℕ) → List ℕ → Bool
  | [], a, s => !(decide (s = E.map Prod.snd)) || hitF S a
  | p :: ord, a, s => ball5 7 fun v => forceL (addc s p.2.1 v) fun s' =>
      !(okL s' (E.map Prod.snd) p.2.2) || searchFS E S ord (upd a p.1 v) s'

theorem searchFS_eq (E : List (List ℕ × ℕ)) (S : List (List ℕ)) :
    ∀ (ord : List (ℕ × List ℕ × List ℕ)) (a : ℕ → ℕ) (s : List ℕ),
      searchFS E S ord a s = search E (fun a => hitS S (masks31.map a)) ord a s
  | [], _, _ => by simp only [searchFS, search, hitF_eq]
  | p :: ord, a, s => by
    simp only [searchFS, search]
    refine ball5_congr fun v => ?_
    rw [forceL_eq, searchFS_eq E S ord]

theorem ball5_of {n : ℕ} {f : ℕ → Bool} (h : ∀ x, x < n → f x = true) : ball5 n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ball5, Bool.and_eq_true]
    exact ⟨ih fun x hx => h x (by omega), h n (by omega)⟩

/-- **A node of the search** passes when every child that survives the pruning test passes. -/
theorem searchFS_node {E : List (List ℕ × ℕ)} {S : List (List ℕ)} {p : ℕ × List ℕ × List ℕ}
    {ord : List (ℕ × List ℕ × List ℕ)} {a : ℕ → ℕ} {s : List ℕ}
    (h : ∀ v, v < 7 → okL (addc s p.2.1 v) (E.map Prod.snd) p.2.2 = true →
      searchFS E S ord (upd a p.1 v) (addc s p.2.1 v) = true) :
    searchFS E S (p :: ord) a s = true := by
  simp only [searchFS]
  refine ball5_of fun v hv => ?_
  rw [forceL_eq]
  by_cases hok : okL (addc s p.2.1 v) (E.map Prod.snd) p.2.2 = true
  · rw [h v hv hok, Bool.or_true]
  · simp only [Bool.not_eq_true] at hok
    rw [hok]; rfl

end GridGen.Five.K5
