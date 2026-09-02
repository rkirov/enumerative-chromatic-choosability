/-!
# Packed base-`b` digit vectors

`pkList b g l i = Σ_j g (l[j]) · b^(i+j)`: a list packed as base-`b` digits starting at position
`i`. When every digit is `< b`, position `i+j` reads back `g (l[j])`. Used to turn the packed
accumulators of the certificate checker into per-state sums. No Mathlib.
-/

namespace Grid3.Three.Cert

def pkList {α : Type} (b : Nat) (g : α → Nat) : List α → Nat → Nat
  | [], _ => 0
  | x :: l, i => g x * b ^ i + pkList b g l (i + 1)

/-- `pkList` at position `i` is `b^i` times `pkList` at position `0` -/
theorem pkList_shift {α : Type} (b : Nat) (g : α → Nat) :
    ∀ (l : List α) (i : Nat), pkList b g l i = b ^ i * pkList b g l 0 := by
  intro l
  induction l with
  | nil => intro i; simp [pkList]
  | cons x l ih =>
    intro i
    simp only [pkList]
    rw [ih (i + 1), ih 1]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add, Nat.mul_one]
    ac_rfl

theorem pkList_cons_zero {α : Type} (b : Nat) (g : α → Nat) (x : α) (l : List α) :
    pkList b g (x :: l) 0 = g x + b * pkList b g l 0 := by
  simp only [pkList, Nat.pow_zero, Nat.mul_one, pkList_shift b g l 1, Nat.pow_succ, Nat.one_mul]

/-- all digits below the base -/
def digitsLt {α : Type} (b : Nat) (g : α → Nat) (l : List α) : Prop := ∀ x ∈ l, g x < b

theorem pkList_mod {α : Type} (b : Nat) (g : α → Nat) (x : α) (l : List α) (hx : g x < b) :
    pkList b g (x :: l) 0 % b = g x := by
  rw [pkList_cons_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem pkList_div {α : Type} (b : Nat) (hb : 0 < b) (g : α → Nat) (x : α) (l : List α) (hx : g x < b) :
    pkList b g (x :: l) 0 / b = pkList b g l 0 := by
  rw [pkList_cons_zero, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hx, Nat.zero_add]

/-- reading digit `j` -/
theorem pkList_digit {α : Type} (b : Nat) (hb : 0 < b) (g : α → Nat) :
    ∀ (l : List α) (j : Nat) (hj : j < l.length), digitsLt b g l →
      pkList b g l 0 / b ^ j % b = g (l[j]) := by
  intro l
  induction l with
  | nil => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | cons x l ih =>
    intro j hj hd
    have hx : g x < b := hd x (List.mem_cons_self ..)
    cases j with
    | zero => simp only [Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]; exact pkList_mod b g x l hx
    | succ j =>
      have hd' : digitsLt b g l := fun y hy => hd y (List.mem_cons_of_mem x hy)
      simp only [List.getElem_cons_succ]
      rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, pkList_div b hb g x l hx]
      exact ih j (Nat.lt_of_succ_lt_succ hj) hd'

/-- two packed vectors of the same length with digits below the base agree iff their digits do -/
theorem pkList_inj {α β : Type} (b : Nat) (hb : 0 < b) (g : α → Nat) (h : β → Nat) :
    ∀ (l : List α) (m : List β), l.length = m.length → digitsLt b g l → digitsLt b h m →
      pkList b g l 0 = pkList b h m 0 →
      ∀ j (hj : j < l.length) (hj' : j < m.length), g (l[j]) = h (m[j]) := by
  intro l m hlen hl hm heq j hj hj'
  rw [← pkList_digit b hb g l j hj hl, ← pkList_digit b hb h m j hj' hm, heq]

/-- packing is additive in the digit function -/
theorem pkList_add {α : Type} (b : Nat) (g h : α → Nat) :
    ∀ (l : List α) (i : Nat), pkList b (fun x => g x + h x) l i = pkList b g l i + pkList b h l i := by
  intro l
  induction l with
  | nil => intro i; simp [pkList]
  | cons x l ih =>
    intro i
    simp only [pkList, ih, Nat.add_mul]
    ac_rfl

/-- a single nonzero digit -/
theorem pkList_single {α : Type} [DecidableEq α] (b : Nat) (v : Nat) :
    ∀ (l : List α) (i j : Nat) (hj : j < l.length), l.Nodup →
      pkList b (fun x => if x = l[j] then v else 0) l i = v * b ^ (i + j) := by
  intro l
  induction l with
  | nil => intro i j hj; exact absurd hj (Nat.not_lt_zero _)
  | cons x l ih =>
    intro i j hj hnd
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have hx : x ∉ l := (List.nodup_cons.mp hnd).1
    cases j with
    | zero =>
      simp only [pkList, List.getElem_cons_zero, if_true, Nat.add_zero]
      have : pkList b (fun y => if y = x then v else 0) l (i + 1) = 0 := by
        clear ih hj hnd hnd'
        induction l generalizing i with
        | nil => rfl
        | cons y l ih2 =>
          have hy : y ≠ x := fun h => hx (h ▸ List.mem_cons_self ..)
          have hx' : x ∉ l := fun h => hx (List.mem_cons_of_mem y h)
          simp only [pkList, if_neg hy, Nat.zero_mul, Nat.zero_add]
          exact ih2 (i + 1) hx'
      rw [this, Nat.add_zero]
    | succ j =>
      have hj' : j < l.length := Nat.lt_of_succ_lt_succ hj
      simp only [pkList, List.getElem_cons_succ]
      have hne : x ≠ l[j]'hj' := fun h => hx (h ▸ List.getElem_mem hj')
      rw [if_neg hne, Nat.zero_mul, Nat.zero_add, ih (i + 1) j hj' hnd']
      congr 1
      rw [Nat.add_assoc, Nat.add_comm 1 j]

/-- a packed vector of zero digits is zero -/
theorem pkList_zero_of {α : Type} (b : Nat) (g : α → Nat) :
    ∀ (l : List α) (i : Nat), (∀ x ∈ l, g x = 0) → pkList b g l i = 0 := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons x l ih =>
    intro i h
    simp only [pkList, h x (List.mem_cons_self ..), Nat.zero_mul, Nat.zero_add]
    exact ih (i + 1) (fun y hy => h y (List.mem_cons_of_mem x hy))

end Grid3.Three.Cert
