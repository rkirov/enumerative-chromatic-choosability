/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Shape

/-!
# Height four at `k = 4`: assembling the classification

The next columns are split by their consecutive mismatches `(a, b, c)` (`aᵢ = 4 - |Bᵢ ∩ Bᵢ₊₁|`).
For each triple, `dispatchCheck` (`GridGen/Four/Dispatch.lean`) enumerates the atom sizes of all
columns with these mismatches and finds each among the certified keys (`certAt_dispatch`); the
125 triples together give Codex's (OpenAI) classification `Classify4` (`classify4_of`).
-/

namespace GridGen.Four.K4

open Finset GridGen.Four

/-- The classification for the next columns with mismatches `(a, b, c)`. -/
def TripleOK (a b c : ℕ) : Prop :=
  ∀ B : Col, CardsIn 4 4 B → (B.1 ∩ B.2.1).card + a = 4 → (B.2.1 ∩ B.2.2.1).card + b = 4 →
    (B.2.2.1 ∩ B.2.2.2).card + c = 4 → ∀ Y : Col, CardsIn 3 4 Y → ¬ Bad Y B → RaysOK (dvec Y B)

/-- The mismatch selector. -/
def selT (a b c : ℕ) (x y z : ℕ) : Bool := Nat.beq x a && Nat.beq y b && Nat.beq z c

/-- **Dispatch**: every column with mismatches `(a, b, c)` has certified atom sizes. -/
theorem certAt_dispatch {a b c : ℕ} {keys : List (List ℕ)}
    (hc : dispatchCheck 4 5 (selT a b c) (fun xs => keys.contains xs) = true)
    (hk : ∀ xs ∈ keys, CertAt xs) (ha : a < 5) (hb : b < 5) (hcc : c < 5) : TripleOK a b c := by
  intro B hB h12 h23 h34 Y hY hbad
  obtain ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨a4, a4'⟩⟩ := hB
  have hmem := dispatch_of_check hc ⟨ha, hb, hcc⟩ (by simp [selT, Nat.beq_refl])
    (le_antisymm a1' a1) (le_antisymm a2' a2) (le_antisymm a3' a3) (le_antisymm a4' a4) h12 h23 h34
  have hx : atomsOf B ∈ keys := by
    rw [List.contains_iff_mem] at hmem
    exact hmem
  exact hk _ hx B ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨a4, a4'⟩⟩ rfl Y hY hbad

/-- No keys. -/
theorem certAll_nil : ∀ xs ∈ ([] : List (List ℕ)), CertAt xs :=
  fun _ h => absurd h List.not_mem_nil

/-- One more certified key. The generated dispatch modules chain these, so that elaborating the
certificate list costs one unification per key (an `rcases` over the membership disjunction is
quadratic). -/
theorem certAll_cons {x : List ℕ} {l : List (List ℕ)} (h : CertAt x) (t : ∀ y ∈ l, CertAt y) :
    ∀ y ∈ x :: l, CertAt y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact h
  · exact t y hy

/-- **The classification from the 125 mismatch triples.** -/
theorem classify4_of (h : ∀ a < 5, ∀ b < 5, ∀ c < 5, TripleOK a b c) : Classify4 := by
  intro Y B hY hB hbad
  have c12 : (B.1 ∩ B.2.1).card ≤ 4 :=
    (Finset.card_le_card Finset.inter_subset_left).trans hB.1.2
  have c23 : (B.2.1 ∩ B.2.2.1).card ≤ 4 :=
    (Finset.card_le_card Finset.inter_subset_left).trans hB.2.1.2
  have c34 : (B.2.2.1 ∩ B.2.2.2).card ≤ 4 :=
    (Finset.card_le_card Finset.inter_subset_left).trans hB.2.2.1.2
  exact h (4 - (B.1 ∩ B.2.1).card) (by omega) (4 - (B.2.1 ∩ B.2.2.1).card) (by omega)
    (4 - (B.2.2.1 ∩ B.2.2.2).card) (by omega) B hB (by omega) (by omega) (by omega) Y hY hbad

/-! ### Short names for generated pointwise certificates -/

/-- A cluster reference. -/
abbrev Cl (n : ℕ) : PC := PC.cl n
/-- A pointwise tree. -/
abbrev Tr (t : PT) : PC := PC.tree t
/-- A box. -/
abbrev Bx : PT := PT.box
/-- A single column type. -/
abbrev Ex : PT := PT.exact
/-- A split on the next free class. -/
abbrev Sp (k : PTL) : PT := PT.split k
/-- A list of pointwise trees. -/
abbrev Pk (a : PT) (b : PTL) : PTL := PTL.cons a b
/-- The empty list of pointwise trees. -/
abbrev Pe : PTL := PTL.nil

/-- The verified cluster rows of one region, as a check. -/
def ctabQOK (ctab : ℕ → List (VN × VN)) (q : ℕ) : Bool :=
  (ctab q).all fun c =>
    clusterOK c.1 c.2 (patOf (q / 16)).1 (patOf (q / 16)).2.1 (patOf (q / 16)).2.2 (q % 16)

theorem ctabOK_of {ctab : ℕ → List (VN × VN)} (h : ∀ q < 80, ctabQOK ctab q = true) :
    CtabOK ctab := by
  intro q hq c hc
  exact List.all_eq_true.mp (h q hq) c hc

end GridGen.Four.K4
