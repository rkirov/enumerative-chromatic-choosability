import Mathlib

/-!
# Grid model, part 2: the grid fact for `hf_mem`.

If every column of a path is a proper column colouring drawn from the lists (`hval`, `hvert`) and
consecutive columns are horizontally compatible (`hcompat`), then the colouring the path spells is
a proper grid colouring.  This reduces `hf_mem` to the model's coupling-support properties.
-/

namespace Grid3.Three.Model

abbrev Vtx (W : ℕ) := Fin 3 × Fin W

def PState (S : Type*) : ℕ → Type _
  | 0 => S
  | (k + 1) => PState S k × S

variable {S : Type*}

def colAt : ∀ k, PState S k → Fin (k + 1) → S
  | 0, s => fun _ => s
  | (k + 1), q => Fin.snoc (colAt k q.1) q.2

theorem colAt_injective : ∀ k, Function.Injective (colAt (S := S) k) := by
  intro k
  induction k with
  | zero => intro p q h; exact congrFun h 0
  | succ k ih =>
      intro p q h
      have hlast : p.2 = q.2 := by
        have := congrFun h (Fin.last (k + 1)); simpa [colAt, Fin.snoc_last] using this
      have hinit : colAt k p.1 = colAt k q.1 := by
        have h2 : Fin.init (colAt (k + 1) p) = Fin.init (colAt (k + 1) q) := by rw [h]
        simpa [colAt, Fin.init_snoc] using h2
      exact Prod.ext (ih hinit) hlast

def gridAdj (W : ℕ) : Vtx W → Vtx W → Prop := fun p q =>
  (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val)) ∨
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val))

instance (W : ℕ) : DecidableRel (gridAdj W) := fun _ _ => by unfold gridAdj; infer_instance

def properC {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop) [DecidableRel r]
    (L : V → Finset ℕ) : Finset (V → ℕ) :=
  (Fintype.piFinset L).filter (fun φ => ∀ u v, r u v → φ u ≠ φ v)

lemma mem_properC {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop) [DecidableRel r]
    (L : V → Finset ℕ) (φ : V → ℕ) :
    φ ∈ properC r L ↔ (∀ v, φ v ∈ L v) ∧ (∀ u v, r u v → φ u ≠ φ v) := by
  simp only [properC, Finset.mem_filter, Fintype.mem_piFinset]

variable {C : ℕ}

def toColouring (n : ℕ) (p : PState (Fin 3 → Fin C) n) : Vtx (n + 1) → ℕ :=
  fun v => (colAt n p v.2 v.1).val

/-- **`hf_inj`.** `toColouring` is injective. -/
theorem toColouring_injective (n : ℕ) : Function.Injective (toColouring (C := C) n) := by
  intro p q h
  apply colAt_injective n
  funext j i
  exact Fin.val_injective (congrFun h (i, j))

/-- **The grid fact behind `hf_mem`.** -/
theorem toColouring_mem_properC (n : ℕ) (L' : Vtx (n + 1) → Finset ℕ)
    (p : PState (Fin 3 → Fin C) n)
    (hval : ∀ (j : Fin (n + 1)) (i : Fin 3), (colAt n p j i).val ∈ L' (i, j))
    (hvert : ∀ (j : Fin (n + 1)) (i i' : Fin 3), i ≠ i' → colAt n p j i ≠ colAt n p j i')
    (hcompat : ∀ (i : Fin 3) (j j' : Fin (n + 1)), j.val + 1 = j'.val →
      colAt n p j i ≠ colAt n p j' i) :
    toColouring n p ∈ properC (gridAdj (n + 1)) L' := by
  rw [mem_properC]
  refine ⟨fun v => hval v.2 v.1, ?_⟩
  intro u v huv
  have hcolne : colAt n p u.2 u.1 ≠ colAt n p v.2 v.1 := by
    rcases huv with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · -- same column, adjacent rows
      have hine : u.1 ≠ v.1 := by
        rcases hrow with h | h <;> · intro he; rw [he] at h; omega
      rw [hcol]; exact hvert v.2 u.1 v.1 hine
    · -- same row, adjacent columns
      rw [hrow]
      rcases hcol with h | h
      · exact hcompat v.1 u.2 v.2 h
      · exact (hcompat v.1 v.2 u.2 h).symm
  exact fun he => hcolne (Fin.val_injective he)

/-! ### Markov measure trace (from ModelTrace) -/
def lastCol : ∀ k, PState S k → S
  | 0, s => s
  | (_ + 1), p => p.2

noncomputable def mu (alpha : S → ℝ) (K : ℕ → S → S → ℝ) : ∀ k, PState S k → ℝ
  | 0, s => alpha s
  | (k + 1), p => mu alpha K k p.1 * K k (lastCol k p.1) p.2

lemma lastCol_eq_colAt_last : ∀ (k) (p : PState S k), lastCol k p = colAt k p (Fin.last k)
  | 0, _ => rfl
  | (k + 1), p => by simp [colAt, lastCol, Fin.snoc_last]

lemma colAt_castSucc (k : ℕ) (q : PState S (k + 1)) (i : Fin (k + 1)) :
    colAt (k + 1) q i.castSucc = colAt k q.1 i := by
  simp [colAt, Fin.snoc_castSucc]

lemma mu_nonneg (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hα : ∀ s, 0 ≤ alpha s) (hK : ∀ k c s, 0 ≤ K k c s) :
    ∀ n (q : PState S n), 0 ≤ mu alpha K n q := by
  intro n; induction n with
  | zero => intro q; exact hα q
  | succ k ih => intro p; exact mul_nonneg (ih p.1) (hK k _ p.2)

/-- **The `μ>0` trace.** -/
theorem mu_pos_trace (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hα : ∀ s, 0 ≤ alpha s) (hK : ∀ k c s, 0 ≤ K k c s) :
    ∀ (n) (p : PState S n), 0 < mu alpha K n p →
      (0 < alpha (colAt n p 0)) ∧
      (∀ k : Fin n, 0 < K k.val (colAt n p k.castSucc) (colAt n p k.succ)) := by
  intro n
  induction n with
  | zero => intro p hp; exact ⟨hp, fun k => k.elim0⟩
  | succ k ih =>
      intro p hp
      rw [mu] at hp
      have ha : 0 < mu alpha K k p.1 := by
        rcases mul_pos_iff.mp hp with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact absurd (mu_nonneg alpha K hα hK k p.1) (not_le.mpr h)
      have hb : 0 < K k (lastCol k p.1) p.2 := by
        rcases mul_pos_iff.mp hp with ⟨_, h⟩ | ⟨_, h⟩
        · exact h
        · exact absurd (hK k _ p.2) (not_le.mpr h)
      obtain ⟨ih0, ihk⟩ := ih p.1 ha
      refine ⟨?_, ?_⟩
      · have e : colAt (k + 1) p 0 = colAt k p.1 0 := by
          have := colAt_castSucc k p 0; simpa using this
        rw [e]; exact ih0
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · have e1 : colAt (k + 1) p (Fin.last k).castSucc = lastCol k p.1 := by
            rw [colAt_castSucc, lastCol_eq_colAt_last]
          have e2 : colAt (k + 1) p (Fin.last k).succ = p.2 := by
            rw [Fin.succ_last]; exact (lastCol_eq_colAt_last (k + 1) p).symm
          show 0 < K (Fin.last k).val (colAt (k + 1) p (Fin.last k).castSucc)
            (colAt (k + 1) p (Fin.last k).succ)
          rw [e1, e2, Fin.val_last]; exact hb
        · intro i
          have e1 : colAt (k + 1) p (i.castSucc).castSucc = colAt k p.1 i.castSucc :=
            colAt_castSucc k p i.castSucc
          have e2 : colAt (k + 1) p (i.castSucc).succ = colAt k p.1 i.succ := by
            rw [Fin.succ_castSucc]; exact colAt_castSucc k p i.succ
          show 0 < K (i.castSucc).val (colAt (k + 1) p (i.castSucc).castSucc)
            (colAt (k + 1) p (i.castSucc).succ)
          rw [e1, e2, Fin.coe_castSucc]; exact ihk i

end Grid3.Three.Model
