/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Cone
import GridGen.Five.Local

/-!
# Height five: counting proper colourings by their equalities

Generated in part by `ai_research_notes/h5k6/ex5/gencount.py`.

For each of the fifteen equality patterns `σ` of a proper five-row column (the canonical
patterns, `GridGen/Five/Uniform.lean`), the proper colourings from lists `A, …, E` that are
constant on the blocks of `σ` are the proper colourings of the quotient graph, whose lists are the
intersections over the blocks. The quotient of the path is a path, a star, a triangle (with a
pendant) or a four-cycle; its count is an inclusion–exclusion polynomial in the Venn sizes
(`cnt0`, …, `cnt14`). By Möbius inversion over the patterns (`mob_canons`), the number of proper
colourings in each pattern orbit is an integer combination of these counts (`card_orb`).
-/

namespace GridGen.Five.Ex5

open Finset

/-! ### The quotient graphs -/

/-- A triangle: a centre from `S` adjacent to an edge from `X`, `Y`. -/
def tri (S X Y : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (S ×ˢ Four.sts2 X Y).filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2)

/-- A triangle with a pendant vertex from `P` at its centre. -/
def triP (P S X Y : Finset ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (P ×ˢ tri S X Y).filter (fun p => p.1 ≠ p.2.1)

/-- A star: a centre from `S` with leaves from `X`, `Y` and (first) `Z`. -/
def starT (Z S X Y : Finset ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Z ×ˢ (S ×ˢ (X ×ˢ Y)).filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2)).filter
    (fun p => p.1 ≠ p.2.1)

/-- A four-cycle: a vertex from `S` adjacent to both ends of a path from `X, Y, Z`. -/
def c4 (S X Y Z : Finset ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (S ×ˢ Four.sts3 X Y Z).filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.2)

theorem card_sts3 (B C D : Finset ℕ) :
    ((Four.sts3 B C D).card : ℤ) =
      B.card * (C.card * D.card - (C ∩ D).card) - ((B ∩ C).card * D.card - (B ∩ C ∩ D).card) := by
  rw [Four.card_sts3, Four.card_sts2, Four.card_sts2]

theorem card_sts4 (A B C D : Finset ℕ) :
    ((Four.sts A B C D).card : ℤ) =
      A.card * B.card * C.card * D.card
        - (A ∩ B).card * C.card * D.card - A.card * (B ∩ C).card * D.card
        - A.card * B.card * (C ∩ D).card
        + (A ∩ B ∩ C).card * D.card + A.card * (B ∩ C ∩ D).card
        + (A ∩ B).card * (C ∩ D).card - (A ∩ B ∩ C ∩ D).card :=
  Four.card_sts_formula A B C D

theorem card_triP (P S X Y : Finset ℕ) :
    ((triP P S X Y).card : ℤ) =
      P.card * (S.card * (X.card * Y.card - (X ∩ Y).card) - ((X ∩ S).card * Y.card - (X ∩ S ∩ Y).card)
        - (X.card * (Y ∩ S).card - (X ∩ (Y ∩ S)).card))
      - ((S ∩ P).card * (X.card * Y.card - (X ∩ Y).card)
        - ((X ∩ (S ∩ P)).card * Y.card - (X ∩ (S ∩ P) ∩ Y).card)
        - (X.card * (Y ∩ (S ∩ P)).card - (X ∩ (Y ∩ (S ∩ P))).card)) := by
  rw [triP, Lookback.card_prepend P (tri S X Y) Prod.fst]
  have h : (tri S X Y).filter (fun r => r.1 ∈ P) = tri (S ∩ P) X Y := by
    ext p; simp only [tri, Finset.mem_filter, Finset.mem_product, Finset.mem_inter]; tauto
  rw [h, tri, tri, Four.card_triangle, Four.card_triangle]

theorem card_starT (Z S X Y : Finset ℕ) :
    ((starT Z S X Y).card : ℤ) =
      Z.card * (S.card * X.card * Y.card - (X ∩ S).card * Y.card - X.card * (Y ∩ S).card
        + (X ∩ Y ∩ S).card)
      - ((S ∩ Z).card * X.card * Y.card - (X ∩ (S ∩ Z)).card * Y.card
        - X.card * (Y ∩ (S ∩ Z)).card + (X ∩ Y ∩ (S ∩ Z)).card) := by
  rw [starT, Lookback.card_prepend Z _ Prod.fst]
  have h : ((S ×ˢ (X ×ˢ Y)).filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2)).filter
      (fun r => r.1 ∈ Z) = ((S ∩ Z) ×ˢ (X ×ˢ Y)).filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_inter]; tauto
  rw [h, Lookback.card_star, Lookback.card_star]

theorem card_c4 (S X Y Z : Finset ℕ) :
    ((c4 S X Y Z).card : ℤ) =
      S.card * (X.card * (Y.card * Z.card - (Y ∩ Z).card) - ((X ∩ Y).card * Z.card - (X ∩ Y ∩ Z).card))
      - ((X ∩ S).card * (Y.card * Z.card - (Y ∩ Z).card)
        - ((X ∩ S ∩ Y).card * Z.card - (X ∩ S ∩ Y ∩ Z).card))
      - (X.card * (Y.card * (Z ∩ S).card - (Y ∩ (Z ∩ S)).card)
        - ((X ∩ Y).card * (Z ∩ S).card - (X ∩ Y ∩ (Z ∩ S)).card))
      + ((X ∩ Z ∩ S).card * Y.card - (X ∩ Z ∩ S ∩ Y).card) := by
  rw [c4, Lookback.card_pairAvoid S (Four.sts3 X Y Z) Prod.fst (fun r => r.2.2)]
  have h1 : (Four.sts3 X Y Z).filter (fun r => r.1 ∈ S) = Four.sts3 (X ∩ S) Y Z := by
    ext p; simp only [Finset.mem_filter, Four.mem_sts3, Finset.mem_inter]; tauto
  have h2 : (Four.sts3 X Y Z).filter (fun r => r.2.2 ∈ S) = Four.sts3 X Y (Z ∩ S) := by
    ext p; simp only [Finset.mem_filter, Four.mem_sts3, Finset.mem_inter]; tauto
  have h3 : ((Four.sts3 X Y Z).filter (fun r => r.1 ∈ S ∧ r.1 = r.2.2)).card
      = (Four.sts2 (X ∩ Z ∩ S) Y).card := by
    refine Finset.card_nbij' (fun r => (r.1, r.2.1)) (fun p => (p.1, p.2, p.1)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b, c⟩ h
      simp only [Finset.coe_filter, Four.mem_sts3, Four.mem_sts2, Finset.mem_inter,
        Set.mem_ofPred_eq, Finset.mem_coe] at h ⊢
      grind
    · rintro ⟨a, b⟩ h
      simp only [Finset.coe_filter, Four.mem_sts3, Four.mem_sts2, Finset.mem_inter,
        Set.mem_ofPred_eq, Finset.mem_coe] at h ⊢
      grind
    · rintro ⟨a, b, c⟩ h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at h ⊢
      grind
    · rintro ⟨a, b⟩ h
      rfl
  rw [h1, h2, h3, card_sts3, card_sts3, card_sts3, Four.card_sts2]

/-! ### The fifteen counts -/

theorem bij0 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t ∧ r1 t = r5 t)).card = (Four.sts2 (A ∩ C ∩ E) (B ∩ D)).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t)) (fun p => (p.1, p.2, p.1, p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b⟩ h
    rfl

theorem bij1 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card = (Four.sts3 (A ∩ C) (B ∩ D) E).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r5 t)) (fun p => (p.1, p.2.1, p.1, p.2.1, p.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, e⟩ h
    rfl

theorem bij2 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r3 t ∧ r1 t = r5 t)).card = (Four.sts3 B (A ∩ C ∩ E) D).card := by
  refine Finset.card_nbij' (fun t => (r2 t, r1 t, r4 t)) (fun p => (p.2.1, p.1, p.2.1, p.2.2, p.2.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨b, a, d⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨b, a, d⟩ h
    rfl

theorem bij3 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r5 t)).card = (tri (A ∩ C) (B ∩ E) D).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r4 t)) (fun p => (p.1, p.2.1, p.1, p.2.2, p.2.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, d⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, d⟩ h
    rfl

theorem bij4 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r3 t)).card = (Four.sts B (A ∩ C) D E).card := by
  refine Finset.card_nbij' (fun t => (r2 t, r1 t, r4 t, r5 t)) (fun p => (p.2.1, p.1, p.2.1, p.2.2.1, p.2.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨b, a, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨b, a, d, e⟩ h
    rfl

theorem bij5 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r4 t ∧ r2 t = r5 t)).card = (tri (A ∩ D) (B ∩ E) C).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r3 t)) (fun p => (p.1, p.2.1, p.2.2, p.1, p.2.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c⟩ h
    rfl

theorem bij6 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r4 t ∧ r3 t = r5 t)).card = (tri (A ∩ D) B (C ∩ E)).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r3 t)) (fun p => (p.1, p.2.1, p.2.2, p.1, p.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c⟩ h
    rfl

theorem bij7 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r4 t)).card = (triP E (A ∩ D) B C).card := by
  refine Finset.card_nbij' (fun t => (r5 t, r1 t, r2 t, r3 t)) (fun p => (p.2.1, p.2.2.1, p.2.2.2, p.2.1, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨e, a, b, c⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨e, a, b, c⟩ h
    rfl

theorem bij8 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r2 t = r4 t ∧ r1 t = r5 t)).card = (Four.sts3 (A ∩ E) (B ∩ D) C).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r3 t)) (fun p => (p.1, p.2.1, p.2.2, p.2.1, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c⟩ h
    rfl

theorem bij9 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r2 t = r4 t ∧ r3 t = r5 t)).card = (Four.sts3 A (B ∩ D) (C ∩ E)).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r3 t)) (fun p => (p.1, p.2.1, p.2.2, p.2.1, p.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c⟩ h
    rfl

theorem bij10 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r2 t = r4 t)).card = (starT E (B ∩ D) A C).card := by
  refine Finset.card_nbij' (fun t => (r5 t, r2 t, r1 t, r3 t)) (fun p => (p.2.2.1, p.2.1, p.2.2.2, p.2.1, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨e, b, a, c⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨e, b, a, c⟩ h
    rfl

theorem bij11 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r1 t = r5 t)).card = (c4 (A ∩ E) B C D).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r3 t, r4 t)) (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d⟩ h
    rfl

theorem bij12 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r2 t = r5 t)).card = (triP A (B ∩ E) C D).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r3 t, r4 t)) (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2, p.2.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d⟩ h
    rfl

theorem bij13 (A B C D E : Finset ℕ) :
    ((sts A B C D E).filter (fun t => r3 t = r5 t)).card = (Four.sts A B (C ∩ E) D).card := by
  refine Finset.card_nbij' (fun t => (r1 t, r2 t, r3 t, r4 t)) (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2, p.2.2.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d, e⟩ h
    simp only [Finset.coe_filter, mem_sts, Four.mem_sts, Four.mem_sts2, Four.mem_sts3, tri, triP, starT, c4, Finset.mem_product, Finset.mem_filter, Finset.mem_inter, Set.mem_ofPred_eq, Finset.mem_coe, r1, r2, r3, r4, r5, Four.r1, Four.r2, Four.r3, Four.r4] at h ⊢
    grind
  · rintro ⟨a, b, c, d⟩ h
    rfl

theorem cnt0 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t ∧ r1 t = r5 t)).card : ℤ) =
      -((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) + ((B ∩ D).card : ℤ) * ((A ∩ C ∩ E).card : ℤ) := by
  rw [bij0]
  rw [Four.card_sts2]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt1 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℤ) =
      ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) - ((A ∩ C).card : ℤ) * ((B ∩ D ∩ E).card : ℤ) - ((A ∩ B ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) + ((A ∩ C).card : ℤ) * ((B ∩ D).card : ℤ) * ((E).card : ℤ) := by
  rw [bij1]
  rw [card_sts3]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt2 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r3 t ∧ r1 t = r5 t)).card : ℤ) =
      ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) - ((B).card : ℤ) * ((A ∩ C ∩ D ∩ E).card : ℤ) - ((D).card : ℤ) * ((A ∩ B ∩ C ∩ E).card : ℤ) + ((B).card : ℤ) * ((D).card : ℤ) * ((A ∩ C ∩ E).card : ℤ) := by
  rw [bij2]
  rw [card_sts3]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt3 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r5 t)).card : ℤ) =
      2 * ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) - ((A ∩ C).card : ℤ) * ((B ∩ D ∩ E).card : ℤ) - ((D).card : ℤ) * ((A ∩ B ∩ C ∩ E).card : ℤ) - ((A ∩ C ∩ D).card : ℤ) * ((B ∩ E).card : ℤ) + ((A ∩ C).card : ℤ) * ((D).card : ℤ) * ((B ∩ E).card : ℤ) := by
  rw [bij3]
  rw [tri, Four.card_triangle]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt4 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r3 t)).card : ℤ) =
      -((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) + ((B).card : ℤ) * ((A ∩ C ∩ D ∩ E).card : ℤ) + ((A ∩ B ∩ C).card : ℤ) * ((D ∩ E).card : ℤ) + ((A ∩ B ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) - ((B).card : ℤ) * ((A ∩ C).card : ℤ) * ((D ∩ E).card : ℤ) - ((B).card : ℤ) * ((A ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) - ((A ∩ B ∩ C).card : ℤ) * ((D).card : ℤ) * ((E).card : ℤ) + ((B).card : ℤ) * ((A ∩ C).card : ℤ) * ((D).card : ℤ) * ((E).card : ℤ) := by
  rw [bij4]
  rw [card_sts4]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt5 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r4 t ∧ r2 t = r5 t)).card : ℤ) =
      2 * ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) - ((C).card : ℤ) * ((A ∩ B ∩ D ∩ E).card : ℤ) - ((A ∩ D).card : ℤ) * ((B ∩ C ∩ E).card : ℤ) - ((A ∩ C ∩ D).card : ℤ) * ((B ∩ E).card : ℤ) + ((C).card : ℤ) * ((A ∩ D).card : ℤ) * ((B ∩ E).card : ℤ) := by
  rw [bij5]
  rw [tri, Four.card_triangle]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt6 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r4 t ∧ r3 t = r5 t)).card : ℤ) =
      2 * ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) - ((B).card : ℤ) * ((A ∩ C ∩ D ∩ E).card : ℤ) - ((A ∩ D).card : ℤ) * ((B ∩ C ∩ E).card : ℤ) - ((A ∩ B ∩ D).card : ℤ) * ((C ∩ E).card : ℤ) + ((B).card : ℤ) * ((A ∩ D).card : ℤ) * ((C ∩ E).card : ℤ) := by
  rw [bij6]
  rw [tri, Four.card_triangle]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt7 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r4 t)).card : ℤ) =
      -2 * ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) + ((B).card : ℤ) * ((A ∩ C ∩ D ∩ E).card : ℤ) + ((C).card : ℤ) * ((A ∩ B ∩ D ∩ E).card : ℤ) + ((B ∩ C).card : ℤ) * ((A ∩ D ∩ E).card : ℤ) + 2 * ((A ∩ B ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) - ((B).card : ℤ) * ((C).card : ℤ) * ((A ∩ D ∩ E).card : ℤ) - ((B).card : ℤ) * ((A ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) - ((C).card : ℤ) * ((A ∩ B ∩ D).card : ℤ) * ((E).card : ℤ) - ((B ∩ C).card : ℤ) * ((A ∩ D).card : ℤ) * ((E).card : ℤ) + ((B).card : ℤ) * ((C).card : ℤ) * ((A ∩ D).card : ℤ) * ((E).card : ℤ) := by
  rw [bij7]
  rw [card_triP]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt8 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r2 t = r4 t ∧ r1 t = r5 t)).card : ℤ) =
      ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) - ((C).card : ℤ) * ((A ∩ B ∩ D ∩ E).card : ℤ) - ((B ∩ C ∩ D).card : ℤ) * ((A ∩ E).card : ℤ) + ((C).card : ℤ) * ((B ∩ D).card : ℤ) * ((A ∩ E).card : ℤ) := by
  rw [bij8]
  rw [card_sts3]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt9 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r2 t = r4 t ∧ r3 t = r5 t)).card : ℤ) =
      ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) - ((A).card : ℤ) * ((B ∩ C ∩ D ∩ E).card : ℤ) - ((A ∩ B ∩ D).card : ℤ) * ((C ∩ E).card : ℤ) + ((A).card : ℤ) * ((B ∩ D).card : ℤ) * ((C ∩ E).card : ℤ) := by
  rw [bij9]
  rw [card_sts3]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt10 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r2 t = r4 t)).card : ℤ) =
      -((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) + ((A).card : ℤ) * ((B ∩ C ∩ D ∩ E).card : ℤ) + ((C).card : ℤ) * ((A ∩ B ∩ D ∩ E).card : ℤ) + ((A ∩ B ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) - ((A).card : ℤ) * ((C).card : ℤ) * ((B ∩ D ∩ E).card : ℤ) - ((A).card : ℤ) * ((B ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) - ((C).card : ℤ) * ((A ∩ B ∩ D).card : ℤ) * ((E).card : ℤ) + ((A).card : ℤ) * ((C).card : ℤ) * ((B ∩ D).card : ℤ) * ((E).card : ℤ) := by
  rw [bij10]
  rw [card_starT]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt11 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r1 t = r5 t)).card : ℤ) =
      -3 * ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) + ((B).card : ℤ) * ((A ∩ C ∩ D ∩ E).card : ℤ) + ((C).card : ℤ) * ((A ∩ B ∩ D ∩ E).card : ℤ) + ((B ∩ C).card : ℤ) * ((A ∩ D ∩ E).card : ℤ) + ((D).card : ℤ) * ((A ∩ B ∩ C ∩ E).card : ℤ) + ((C ∩ D).card : ℤ) * ((A ∩ B ∩ E).card : ℤ) + ((B ∩ C ∩ D).card : ℤ) * ((A ∩ E).card : ℤ) - ((B).card : ℤ) * ((C).card : ℤ) * ((A ∩ D ∩ E).card : ℤ) - ((B).card : ℤ) * ((C ∩ D).card : ℤ) * ((A ∩ E).card : ℤ) - ((C).card : ℤ) * ((D).card : ℤ) * ((A ∩ B ∩ E).card : ℤ) - ((B ∩ C).card : ℤ) * ((D).card : ℤ) * ((A ∩ E).card : ℤ) + ((B).card : ℤ) * ((C).card : ℤ) * ((D).card : ℤ) * ((A ∩ E).card : ℤ) := by
  rw [bij11]
  rw [card_c4]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt12 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r2 t = r5 t)).card : ℤ) =
      -2 * ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) + 2 * ((A).card : ℤ) * ((B ∩ C ∩ D ∩ E).card : ℤ) + ((C).card : ℤ) * ((A ∩ B ∩ D ∩ E).card : ℤ) + ((D).card : ℤ) * ((A ∩ B ∩ C ∩ E).card : ℤ) + ((C ∩ D).card : ℤ) * ((A ∩ B ∩ E).card : ℤ) - ((A).card : ℤ) * ((C).card : ℤ) * ((B ∩ D ∩ E).card : ℤ) - ((A).card : ℤ) * ((D).card : ℤ) * ((B ∩ C ∩ E).card : ℤ) - ((A).card : ℤ) * ((C ∩ D).card : ℤ) * ((B ∩ E).card : ℤ) - ((C).card : ℤ) * ((D).card : ℤ) * ((A ∩ B ∩ E).card : ℤ) + ((A).card : ℤ) * ((C).card : ℤ) * ((D).card : ℤ) * ((B ∩ E).card : ℤ) := by
  rw [bij12]
  rw [card_triP]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt13 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => r3 t = r5 t)).card : ℤ) =
      -((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) + ((A).card : ℤ) * ((B ∩ C ∩ D ∩ E).card : ℤ) + ((A ∩ B).card : ℤ) * ((C ∩ D ∩ E).card : ℤ) + ((D).card : ℤ) * ((A ∩ B ∩ C ∩ E).card : ℤ) - ((A).card : ℤ) * ((B).card : ℤ) * ((C ∩ D ∩ E).card : ℤ) - ((A).card : ℤ) * ((D).card : ℤ) * ((B ∩ C ∩ E).card : ℤ) - ((A ∩ B).card : ℤ) * ((D).card : ℤ) * ((C ∩ E).card : ℤ) + ((A).card : ℤ) * ((B).card : ℤ) * ((D).card : ℤ) * ((C ∩ E).card : ℤ) := by
  rw [bij13]
  rw [card_sts4]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

theorem cnt14 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => True)).card : ℤ) =
      ((A ∩ B ∩ C ∩ D ∩ E).card : ℤ) - ((A).card : ℤ) * ((B ∩ C ∩ D ∩ E).card : ℤ) - ((A ∩ B).card : ℤ) * ((C ∩ D ∩ E).card : ℤ) - ((A ∩ B ∩ C).card : ℤ) * ((D ∩ E).card : ℤ) - ((A ∩ B ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) + ((A).card : ℤ) * ((B).card : ℤ) * ((C ∩ D ∩ E).card : ℤ) + ((A).card : ℤ) * ((B ∩ C).card : ℤ) * ((D ∩ E).card : ℤ) + ((A).card : ℤ) * ((B ∩ C ∩ D).card : ℤ) * ((E).card : ℤ) + ((A ∩ B).card : ℤ) * ((C).card : ℤ) * ((D ∩ E).card : ℤ) + ((A ∩ B).card : ℤ) * ((C ∩ D).card : ℤ) * ((E).card : ℤ) + ((A ∩ B ∩ C).card : ℤ) * ((D).card : ℤ) * ((E).card : ℤ) - ((A).card : ℤ) * ((B).card : ℤ) * ((C).card : ℤ) * ((D ∩ E).card : ℤ) - ((A).card : ℤ) * ((B).card : ℤ) * ((C ∩ D).card : ℤ) * ((E).card : ℤ) - ((A).card : ℤ) * ((B ∩ C).card : ℤ) * ((D).card : ℤ) * ((E).card : ℤ) - ((A ∩ B).card : ℤ) * ((C).card : ℤ) * ((D).card : ℤ) * ((E).card : ℤ) + ((A).card : ℤ) * ((B).card : ℤ) * ((C).card : ℤ) * ((D).card : ℤ) * ((E).card : ℤ) := by
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), card_sts_formula]
  simp only [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
  ring

/-- The equality pattern predicates: `eb k t` says that `t` is constant on the blocks of the
`k`-th canonical pattern (`canons`). -/
def eb (k : ℕ) (t : T5) : Bool :=
  match k with
  | 0 => decide (r1 t = r3 t) && decide (r2 t = r4 t) && decide (r1 t = r5 t)
  | 1 => decide (r1 t = r3 t) && decide (r2 t = r4 t)
  | 2 => decide (r1 t = r3 t) && decide (r1 t = r5 t)
  | 3 => decide (r1 t = r3 t) && decide (r2 t = r5 t)
  | 4 => decide (r1 t = r3 t)
  | 5 => decide (r1 t = r4 t) && decide (r2 t = r5 t)
  | 6 => decide (r1 t = r4 t) && decide (r3 t = r5 t)
  | 7 => decide (r1 t = r4 t)
  | 8 => decide (r2 t = r4 t) && decide (r1 t = r5 t)
  | 9 => decide (r2 t = r4 t) && decide (r3 t = r5 t)
  | 10 => decide (r2 t = r4 t)
  | 11 => decide (r1 t = r5 t)
  | 12 => decide (r2 t = r5 t)
  | 13 => decide (r3 t = r5 t)
  | _ => true

theorem eb_congr {s t : T5} (h : SamePat s t) (k : ℕ) : eb k s = eb k t := by
  obtain ⟨h13, h24, h35, h14, h25, h15⟩ := h
  have e13 : decide (r1 s = r3 s) = decide (r1 t = r3 t) := decide_eq_decide.mpr h13
  have e24 : decide (r2 s = r4 s) = decide (r2 t = r4 t) := decide_eq_decide.mpr h24
  have e35 : decide (r3 s = r5 s) = decide (r3 t = r5 t) := decide_eq_decide.mpr h35
  have e14 : decide (r1 s = r4 s) = decide (r1 t = r4 t) := decide_eq_decide.mpr h14
  have e25 : decide (r2 s = r5 s) = decide (r2 t = r5 t) := decide_eq_decide.mpr h25
  have e15 : decide (r1 s = r5 s) = decide (r1 t = r5 t) := decide_eq_decide.mpr h15
  unfold eb
  split <;> simp only [e13, e24, e35, e14, e25, e15]

theorem mob_canons0 : ∀ c ∈ canons,
    (if orb c = 0 then (1 : ℤ) else 0) = (if eb 0 c then 1 else 0) := by
  decide +kernel

theorem card_orb0 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 0)).card : ℤ) = (((sts A B C D E).filter (fun t => eb 0 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons0 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons1 : ∀ c ∈ canons,
    (if orb c = 1 then (1 : ℤ) else 0) = -2 * (if eb 0 c then 1 else 0) + (if eb 1 c then 1 else 0) + (if eb 9 c then 1 else 0) := by
  decide +kernel

theorem card_orb1 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 1)).card : ℤ) = -2 * (((sts A B C D E).filter (fun t => eb 0 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 1 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 9 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons1 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons2 : ∀ c ∈ canons,
    (if orb c = 2 then (1 : ℤ) else 0) = -(if eb 0 c then 1 else 0) + (if eb 2 c then 1 else 0) := by
  decide +kernel

theorem card_orb2 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 2)).card : ℤ) = -(((sts A B C D E).filter (fun t => eb 0 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 2 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons2 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons3 : ∀ c ∈ canons,
    (if orb c = 3 then (1 : ℤ) else 0) = (if eb 3 c then 1 else 0) + (if eb 6 c then 1 else 0) := by
  decide +kernel

theorem card_orb3 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 3)).card : ℤ) = (((sts A B C D E).filter (fun t => eb 3 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 6 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons3 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons4 : ∀ c ∈ canons,
    (if orb c = 4 then (1 : ℤ) else 0) = 2 * (if eb 0 c then 1 else 0) - (if eb 1 c then 1 else 0) - 2 * (if eb 2 c then 1 else 0) - (if eb 3 c then 1 else 0) + (if eb 4 c then 1 else 0) - (if eb 6 c then 1 else 0) - (if eb 9 c then 1 else 0) + (if eb 13 c then 1 else 0) := by
  decide +kernel

theorem card_orb4 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 4)).card : ℤ) = 2 * (((sts A B C D E).filter (fun t => eb 0 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 1 t = true)).card : ℤ) - 2 * (((sts A B C D E).filter (fun t => eb 2 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 3 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 4 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 6 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 9 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 13 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons4 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons5 : ∀ c ∈ canons,
    (if orb c = 5 then (1 : ℤ) else 0) = (if eb 5 c then 1 else 0) := by
  decide +kernel

theorem card_orb5 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 5)).card : ℤ) = (((sts A B C D E).filter (fun t => eb 5 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons5 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons6 : ∀ c ∈ canons,
    (if orb c = 6 then (1 : ℤ) else 0) = -(if eb 3 c then 1 else 0) - 2 * (if eb 5 c then 1 else 0) - (if eb 6 c then 1 else 0) + (if eb 7 c then 1 else 0) + (if eb 12 c then 1 else 0) := by
  decide +kernel

theorem card_orb6 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 6)).card : ℤ) = -(((sts A B C D E).filter (fun t => eb 3 t = true)).card : ℤ) - 2 * (((sts A B C D E).filter (fun t => eb 5 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 6 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 7 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 12 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons6 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons7 : ∀ c ∈ canons,
    (if orb c = 7 then (1 : ℤ) else 0) = -(if eb 0 c then 1 else 0) + (if eb 8 c then 1 else 0) := by
  decide +kernel

theorem card_orb7 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 7)).card : ℤ) = -(((sts A B C D E).filter (fun t => eb 0 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 8 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons7 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons8 : ∀ c ∈ canons,
    (if orb c = 8 then (1 : ℤ) else 0) = 2 * (if eb 0 c then 1 else 0) - (if eb 1 c then 1 else 0) - (if eb 8 c then 1 else 0) - (if eb 9 c then 1 else 0) + (if eb 10 c then 1 else 0) := by
  decide +kernel

theorem card_orb8 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 8)).card : ℤ) = 2 * (((sts A B C D E).filter (fun t => eb 0 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 1 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 8 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 9 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 10 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons8 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons9 : ∀ c ∈ canons,
    (if orb c = 9 then (1 : ℤ) else 0) = (if eb 0 c then 1 else 0) - (if eb 2 c then 1 else 0) - (if eb 8 c then 1 else 0) + (if eb 11 c then 1 else 0) := by
  decide +kernel

theorem card_orb9 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 9)).card : ℤ) = (((sts A B C D E).filter (fun t => eb 0 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 2 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 8 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 11 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons9 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem mob_canons10 : ∀ c ∈ canons,
    (if orb c = 10 then (1 : ℤ) else 0) = -2 * (if eb 0 c then 1 else 0) + (if eb 1 c then 1 else 0) + 2 * (if eb 2 c then 1 else 0) + (if eb 3 c then 1 else 0) - (if eb 4 c then 1 else 0) + (if eb 5 c then 1 else 0) + (if eb 6 c then 1 else 0) - (if eb 7 c then 1 else 0) + (if eb 8 c then 1 else 0) + (if eb 9 c then 1 else 0) - (if eb 10 c then 1 else 0) - (if eb 11 c then 1 else 0) - (if eb 12 c then 1 else 0) - (if eb 13 c then 1 else 0) + (if eb 14 c then 1 else 0) := by
  decide +kernel

theorem card_orb10 (A B C D E : Finset ℕ) :
    (((sts A B C D E).filter (fun t => orb t = 10)).card : ℤ) = -2 * (((sts A B C D E).filter (fun t => eb 0 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 1 t = true)).card : ℤ) + 2 * (((sts A B C D E).filter (fun t => eb 2 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 3 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 4 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 5 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 6 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 7 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 8 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 9 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 10 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 11 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 12 t = true)).card : ℤ) - (((sts A B C D E).filter (fun t => eb 13 t = true)).card : ℤ) + (((sts A B C D E).filter (fun t => eb 14 t = true)).card : ℤ) := by
  simp only [Finset.card_filter]
  push_cast
  try simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hp := proper_of_mem_sts ht
  have hs := samePat_canon hp
  have e := mob_canons10 _ (canon_mem hp)
  rw [← orb_congr hs] at e
  simp only [← eb_congr hs] at e
  rw [e]
  try (split_ifs <;> simp)

theorem filter_eb0 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 0 t = true) = (sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t ∧ r1 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb1 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 1 t = true) = (sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb2 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 2 t = true) = (sts A B C D E).filter (fun t => r1 t = r3 t ∧ r1 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb3 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 3 t = true) = (sts A B C D E).filter (fun t => r1 t = r3 t ∧ r2 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb4 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 4 t = true) = (sts A B C D E).filter (fun t => r1 t = r3 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb5 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 5 t = true) = (sts A B C D E).filter (fun t => r1 t = r4 t ∧ r2 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb6 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 6 t = true) = (sts A B C D E).filter (fun t => r1 t = r4 t ∧ r3 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb7 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 7 t = true) = (sts A B C D E).filter (fun t => r1 t = r4 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb8 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 8 t = true) = (sts A B C D E).filter (fun t => r2 t = r4 t ∧ r1 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb9 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 9 t = true) = (sts A B C D E).filter (fun t => r2 t = r4 t ∧ r3 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb10 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 10 t = true) = (sts A B C D E).filter (fun t => r2 t = r4 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb11 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 11 t = true) = (sts A B C D E).filter (fun t => r1 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb12 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 12 t = true) = (sts A B C D E).filter (fun t => r2 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb13 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 13 t = true) = (sts A B C D E).filter (fun t => r3 t = r5 t) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

theorem filter_eb14 (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (fun t => eb 14 t = true) = (sts A B C D E).filter (fun t => True) := by
  refine Finset.filter_congr fun t _ => ?_
  simp [eb, and_assoc]

/-- Venn data of five lists: `xI` is the size of the intersection of the lists in the row
mask `I` (bit `i` for row `i + 1`). -/
structure V5 where
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : ℕ)

/-- The Venn data of five lists. -/
def venn5 (A B C D E : Finset ℕ) : V5 :=
  ⟨(A).card, (B).card, (A ∩ B).card, (C).card, (A ∩ C).card, (B ∩ C).card, (A ∩ B ∩ C).card, (D).card, (A ∩ D).card, (B ∩ D).card, (A ∩ B ∩ D).card, (C ∩ D).card, (A ∩ C ∩ D).card, (B ∩ C ∩ D).card, (A ∩ B ∩ C ∩ D).card, (E).card, (A ∩ E).card, (B ∩ E).card, (A ∩ B ∩ E).card, (C ∩ E).card, (A ∩ C ∩ E).card, (B ∩ C ∩ E).card, (A ∩ B ∩ C ∩ E).card, (D ∩ E).card, (A ∩ D ∩ E).card, (B ∩ D ∩ E).card, (A ∩ B ∩ D ∩ E).card, (C ∩ D ∩ E).card, (A ∩ C ∩ D ∩ E).card, (B ∩ C ∩ D ∩ E).card, (A ∩ B ∩ C ∩ D ∩ E).card⟩

theorem nsub_eq {a b c : ℕ} (h : (a : ℤ) - b = c) : Nat.sub a b = c := by
  show a - b = c; omega

/-- The count of the pattern predicate `eb 0`, from the Venn data. -/
def nk0 (x : V5) : ℕ := Nat.sub (Nat.mul x.x10 x.x21) (x.x31)

theorem nk0_eq (A B C D E : Finset ℕ) :
    nk0 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 0 t = true)).card := by
  rw [filter_eb0]
  apply nsub_eq
  have h := cnt0 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 1`, from the Venn data. -/
def nk1 (x : V5) : ℕ := Nat.sub (Nat.add x.x31 (Nat.mul (Nat.mul x.x5 x.x10) x.x16)) (Nat.add (Nat.mul x.x5 x.x26) (Nat.mul x.x15 x.x16))

theorem nk1_eq (A B C D E : Finset ℕ) :
    nk1 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 1 t = true)).card := by
  rw [filter_eb1]
  apply nsub_eq
  have h := cnt1 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 2`, from the Venn data. -/
def nk2 (x : V5) : ℕ := Nat.sub (Nat.add x.x31 (Nat.mul (Nat.mul x.x2 x.x8) x.x21)) (Nat.add (Nat.mul x.x2 x.x29) (Nat.mul x.x8 x.x23))

theorem nk2_eq (A B C D E : Finset ℕ) :
    nk2 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 2 t = true)).card := by
  rw [filter_eb2]
  apply nsub_eq
  have h := cnt2 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 3`, from the Venn data. -/
def nk3 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.mul 2 x.x31) (Nat.mul (Nat.mul x.x5 x.x8) x.x18)) (Nat.add (Nat.add (Nat.mul x.x5 x.x26) (Nat.mul x.x8 x.x23)) (Nat.mul x.x13 x.x18))

theorem nk3_eq (A B C D E : Finset ℕ) :
    nk3 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 3 t = true)).card := by
  rw [filter_eb3]
  apply nsub_eq
  have h := cnt3 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 4`, from the Venn data. -/
def nk4 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.add (Nat.add (Nat.mul x.x2 x.x29) (Nat.mul x.x7 x.x24)) (Nat.mul x.x15 x.x16)) (Nat.mul (Nat.mul (Nat.mul x.x2 x.x5) x.x8) x.x16)) (Nat.add (Nat.add (Nat.add x.x31 (Nat.mul (Nat.mul x.x2 x.x5) x.x24)) (Nat.mul (Nat.mul x.x2 x.x13) x.x16)) (Nat.mul (Nat.mul x.x7 x.x8) x.x16))

theorem nk4_eq (A B C D E : Finset ℕ) :
    nk4 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 4 t = true)).card := by
  rw [filter_eb4]
  apply nsub_eq
  have h := cnt4 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 5`, from the Venn data. -/
def nk5 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.mul 2 x.x31) (Nat.mul (Nat.mul x.x4 x.x9) x.x18)) (Nat.add (Nat.add (Nat.mul x.x4 x.x27) (Nat.mul x.x9 x.x22)) (Nat.mul x.x13 x.x18))

theorem nk5_eq (A B C D E : Finset ℕ) :
    nk5 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 5 t = true)).card := by
  rw [filter_eb5]
  apply nsub_eq
  have h := cnt5 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 6`, from the Venn data. -/
def nk6 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.mul 2 x.x31) (Nat.mul (Nat.mul x.x2 x.x9) x.x20)) (Nat.add (Nat.add (Nat.mul x.x2 x.x29) (Nat.mul x.x9 x.x22)) (Nat.mul x.x11 x.x20))

theorem nk6_eq (A B C D E : Finset ℕ) :
    nk6 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 6 t = true)).card := by
  rw [filter_eb6]
  apply nsub_eq
  have h := cnt6 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 7`, from the Venn data. -/
def nk7 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul x.x2 x.x29) (Nat.mul x.x4 x.x27)) (Nat.mul x.x6 x.x25)) (Nat.mul (Nat.mul 2 x.x15) x.x16)) (Nat.mul (Nat.mul (Nat.mul x.x2 x.x4) x.x9) x.x16)) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 2 x.x31) (Nat.mul (Nat.mul x.x2 x.x4) x.x25)) (Nat.mul (Nat.mul x.x2 x.x13) x.x16)) (Nat.mul (Nat.mul x.x4 x.x11) x.x16)) (Nat.mul (Nat.mul x.x6 x.x9) x.x16))

theorem nk7_eq (A B C D E : Finset ℕ) :
    nk7 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 7 t = true)).card := by
  rw [filter_eb7]
  apply nsub_eq
  have h := cnt7 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 8`, from the Venn data. -/
def nk8 (x : V5) : ℕ := Nat.sub (Nat.add x.x31 (Nat.mul (Nat.mul x.x4 x.x10) x.x17)) (Nat.add (Nat.mul x.x4 x.x27) (Nat.mul x.x14 x.x17))

theorem nk8_eq (A B C D E : Finset ℕ) :
    nk8 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 8 t = true)).card := by
  rw [filter_eb8]
  apply nsub_eq
  have h := cnt8 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 9`, from the Venn data. -/
def nk9 (x : V5) : ℕ := Nat.sub (Nat.add x.x31 (Nat.mul (Nat.mul x.x1 x.x10) x.x20)) (Nat.add (Nat.mul x.x1 x.x30) (Nat.mul x.x11 x.x20))

theorem nk9_eq (A B C D E : Finset ℕ) :
    nk9 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 9 t = true)).card := by
  rw [filter_eb9]
  apply nsub_eq
  have h := cnt9 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 10`, from the Venn data. -/
def nk10 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.add (Nat.add (Nat.mul x.x1 x.x30) (Nat.mul x.x4 x.x27)) (Nat.mul x.x15 x.x16)) (Nat.mul (Nat.mul (Nat.mul x.x1 x.x4) x.x10) x.x16)) (Nat.add (Nat.add (Nat.add x.x31 (Nat.mul (Nat.mul x.x1 x.x4) x.x26)) (Nat.mul (Nat.mul x.x1 x.x14) x.x16)) (Nat.mul (Nat.mul x.x4 x.x11) x.x16))

theorem nk10_eq (A B C D E : Finset ℕ) :
    nk10 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 10 t = true)).card := by
  rw [filter_eb10]
  apply nsub_eq
  have h := cnt10 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 11`, from the Venn data. -/
def nk11 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul x.x2 x.x29) (Nat.mul x.x4 x.x27)) (Nat.mul x.x6 x.x25)) (Nat.mul x.x8 x.x23)) (Nat.mul x.x12 x.x19)) (Nat.mul x.x14 x.x17)) (Nat.mul (Nat.mul (Nat.mul x.x2 x.x4) x.x8) x.x17)) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 3 x.x31) (Nat.mul (Nat.mul x.x2 x.x4) x.x25)) (Nat.mul (Nat.mul x.x2 x.x12) x.x17)) (Nat.mul (Nat.mul x.x4 x.x8) x.x19)) (Nat.mul (Nat.mul x.x6 x.x8) x.x17))

theorem nk11_eq (A B C D E : Finset ℕ) :
    nk11 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 11 t = true)).card := by
  rw [filter_eb11]
  apply nsub_eq
  have h := cnt11 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 12`, from the Venn data. -/
def nk12 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mul 2 x.x1) x.x30) (Nat.mul x.x4 x.x27)) (Nat.mul x.x8 x.x23)) (Nat.mul x.x12 x.x19)) (Nat.mul (Nat.mul (Nat.mul x.x1 x.x4) x.x8) x.x18)) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 2 x.x31) (Nat.mul (Nat.mul x.x1 x.x4) x.x26)) (Nat.mul (Nat.mul x.x1 x.x8) x.x22)) (Nat.mul (Nat.mul x.x1 x.x12) x.x18)) (Nat.mul (Nat.mul x.x4 x.x8) x.x19))

theorem nk12_eq (A B C D E : Finset ℕ) :
    nk12 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 12 t = true)).card := by
  rw [filter_eb12]
  apply nsub_eq
  have h := cnt12 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 13`, from the Venn data. -/
def nk13 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.add (Nat.add (Nat.mul x.x1 x.x30) (Nat.mul x.x3 x.x28)) (Nat.mul x.x8 x.x23)) (Nat.mul (Nat.mul (Nat.mul x.x1 x.x2) x.x8) x.x20)) (Nat.add (Nat.add (Nat.add x.x31 (Nat.mul (Nat.mul x.x1 x.x2) x.x28)) (Nat.mul (Nat.mul x.x1 x.x8) x.x22)) (Nat.mul (Nat.mul x.x3 x.x8) x.x20))

theorem nk13_eq (A B C D E : Finset ℕ) :
    nk13 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 13 t = true)).card := by
  rw [filter_eb13]
  apply nsub_eq
  have h := cnt13 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The count of the pattern predicate `eb 14`, from the Venn data. -/
def nk14 (x : V5) : ℕ := Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add x.x31 (Nat.mul (Nat.mul x.x1 x.x2) x.x28)) (Nat.mul (Nat.mul x.x1 x.x6) x.x24)) (Nat.mul (Nat.mul x.x1 x.x14) x.x16)) (Nat.mul (Nat.mul x.x3 x.x4) x.x24)) (Nat.mul (Nat.mul x.x3 x.x12) x.x16)) (Nat.mul (Nat.mul x.x7 x.x8) x.x16)) (Nat.mul (Nat.mul (Nat.mul (Nat.mul x.x1 x.x2) x.x4) x.x8) x.x16)) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul x.x1 x.x30) (Nat.mul x.x3 x.x28)) (Nat.mul x.x7 x.x24)) (Nat.mul x.x15 x.x16)) (Nat.mul (Nat.mul (Nat.mul x.x1 x.x2) x.x4) x.x24)) (Nat.mul (Nat.mul (Nat.mul x.x1 x.x2) x.x12) x.x16)) (Nat.mul (Nat.mul (Nat.mul x.x1 x.x6) x.x8) x.x16)) (Nat.mul (Nat.mul (Nat.mul x.x3 x.x4) x.x8) x.x16))

theorem nk14_eq (A B C D E : Finset ℕ) :
    nk14 (venn5 A B C D E) = ((sts A B C D E).filter (fun t => eb 14 t = true)).card := by
  rw [filter_eb14]
  apply nsub_eq
  have h := cnt14 A B C D E
  simp only [venn5, Nat.add_eq, Nat.mul_eq] at h ⊢
  push_cast
  linarith

/-- The orbit counts. -/
structure C11 where
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℕ)
  deriving DecidableEq

/-- The orbit counts of the proper colourings, from the Venn data. -/
def clsV (x : V5) : C11 :=
  ⟨Nat.sub (nk0 x) (0),
    Nat.sub (Nat.add (nk1 x) (nk9 x)) (Nat.mul 2 (nk0 x)),
    Nat.sub (nk2 x) (nk0 x),
    Nat.sub (Nat.add (nk3 x) (nk6 x)) (0),
    Nat.sub (Nat.add (Nat.add (Nat.mul 2 (nk0 x)) (nk4 x)) (nk13 x)) (Nat.add (Nat.add (Nat.add (Nat.add (nk1 x) (Nat.mul 2 (nk2 x))) (nk3 x)) (nk6 x)) (nk9 x)),
    Nat.sub (nk5 x) (0),
    Nat.sub (Nat.add (nk7 x) (nk12 x)) (Nat.add (Nat.add (nk3 x) (Nat.mul 2 (nk5 x))) (nk6 x)),
    Nat.sub (nk8 x) (nk0 x),
    Nat.sub (Nat.add (Nat.mul 2 (nk0 x)) (nk10 x)) (Nat.add (Nat.add (nk1 x) (nk8 x)) (nk9 x)),
    Nat.sub (Nat.add (nk0 x) (nk11 x)) (Nat.add (nk2 x) (nk8 x)),
    Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (nk1 x) (Nat.mul 2 (nk2 x))) (nk3 x)) (nk5 x)) (nk6 x)) (nk8 x)) (nk9 x)) (nk14 x)) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 2 (nk0 x)) (nk4 x)) (nk7 x)) (nk10 x)) (nk11 x)) (nk12 x)) (nk13 x))⟩

/-- The number of proper colourings in an orbit. -/
def corb (A B C D E : Finset ℕ) (o : Fin 11) : ℕ := ((sts A B C D E).filter (fun t => orb t = o)).card

/-- **The orbit counts from the Venn data.** -/
theorem clsV_venn5 (A B C D E : Finset ℕ) :
    clsV (venn5 A B C D E) = ⟨corb A B C D E 0, corb A B C D E 1, corb A B C D E 2, corb A B C D E 3, corb A B C D E 4, corb A B C D E 5, corb A B C D E 6, corb A B C D E 7, corb A B C D E 8, corb A B C D E 9, corb A B C D E 10⟩ := by
  have e0 := nk0_eq A B C D E; have e1 := nk1_eq A B C D E; have e2 := nk2_eq A B C D E
  have e3 := nk3_eq A B C D E; have e4 := nk4_eq A B C D E; have e5 := nk5_eq A B C D E
  have e6 := nk6_eq A B C D E; have e7 := nk7_eq A B C D E; have e8 := nk8_eq A B C D E
  have e9 := nk9_eq A B C D E; have e10 := nk10_eq A B C D E; have e11 := nk11_eq A B C D E
  have e12 := nk12_eq A B C D E; have e13 := nk13_eq A B C D E; have e14 := nk14_eq A B C D E
  simp only [clsV, C11.mk.injEq, corb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply nsub_eq
    have := card_orb0 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb1 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb2 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb3 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb4 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb5 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb6 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb7 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb8 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb9 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith
  · apply nsub_eq
    have := card_orb10 A B C D E
    simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11, ← e12,
      ← e13, ← e14] at this
    try simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    linarith

end GridGen.Five.Ex5
