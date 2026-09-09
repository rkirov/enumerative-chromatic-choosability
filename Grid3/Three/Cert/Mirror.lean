/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Three.Cert.KeyExt
import Grid3.Three.Cert.Types

/-!
# Row reflection on packed types, keys and signatures

Swapping rows `0` and `2` of a column reverses the bits of every pattern (`revPat`), permutes the
seven pattern indices (`rp`), hence permutes the base-4 digits of a packed type (`rtype`) and
the cells of a packed key (`rM`); on signatures it reverses the pattern triple (`rsig`). The
column laws are reflection-equivariant (`lawSig_rsig`, a kernel check of the law table), so a
seam can be transported along the reflection (`Reflect.lean`), and the certificate stores one
record per reflection orbit of keys (`Keys/All.lean`).
-/

namespace Grid3.Three.Cert

/-- pattern reflection (rows `0 ↔ 2`), on `0..7` -/
def revPat (p : Nat) : Nat := p % 2 * 4 + p / 2 % 2 * 2 + p / 4

/-- pattern-index reflection, on `0..6` -/
def rp (p : Nat) : Nat := revPat (p + 1) - 1

/-- a list of base-4 digits, least significant first -/
def pack4 : List Nat → Nat
  | [] => 0
  | d :: L => d + 4 * pack4 L

/-- the reflected type: the pattern multiplicities permuted by `rp` -/
def rtype (m : Nat) : Nat := pack4 (List.ofFn fun i : Fin 7 => mult m (rp i))

/-- the reflected key: the cells permuted by `rp` on both indices -/
def rM (M : Nat) : Nat :=
  pack4 (List.ofFn fun i : Fin 49 => mcount M (rp (i.val / 7)) (rp (i.val % 7)))

/-- the reflected signature: the pattern triple reversed and reflected, the `ABA` flag kept -/
def rsig (s : Nat) : Nat :=
  ((rp (s / 2 % 7) * 7 + rp (s / 14 % 7)) * 7 + rp (s / 98 % 7)) * 2 + s % 2

/-! ### The finite facts -/

theorem rp_lt : ∀ p < 7, rp p < 7 := by decide
theorem rp_rp : ∀ p < 7, rp (rp p) = p := by decide
theorem rp_0 : rp 0 = 3 := by decide
theorem rp_1 : rp 1 = 1 := by decide
theorem rp_2 : rp 2 = 5 := by decide
theorem rp_3 : rp 3 = 0 := by decide
theorem rp_4 : rp 4 = 4 := by decide
theorem rp_5 : rp 5 = 2 := by decide
theorem rp_6 : rp 6 = 6 := by decide
theorem revPat_eq_iff : ∀ x < 8, ∀ p < 7, (revPat x = p + 1 ↔ x = rp p + 1) := by decide
theorem land_revPat : ∀ a < 8, ∀ b < 8, (revPat a &&& revPat b ≠ 0 ↔ a &&& b ≠ 0) := by decide
theorem inter_rp : ∀ p < 7, ∀ q < 7, inter (rp p) (rp q) = inter p q := by decide
theorem rsig_mod_two (s : Nat) : rsig s % 2 = s % 2 := by unfold rsig; omega
/-- `rsig` on a signature with pattern indices `a, b, c` and flag `e` -/
theorem rsig_formula : ∀ a < 7, ∀ b < 7, ∀ c < 7, ∀ e < 2,
    rsig (((a * 7 + b) * 7 + c) * 2 + e) = ((rp c * 7 + rp b) * 7 + rp a) * 2 + e := by
  decide +kernel

/-! ### Digits of `pack4` -/

theorem pack4_lt : ∀ L : List Nat, (∀ d ∈ L, d < 4) → pack4 L < 4 ^ L.length
  | [], _ => by simp [pack4]
  | d :: L, h => by
    have hd : d < 4 := h d (by simp)
    have ih := pack4_lt L (fun x hx => h x (by simp [hx]))
    simp only [pack4, List.length_cons, Nat.pow_succ]
    omega

theorem pack4_digit : ∀ (L : List Nat), (∀ d ∈ L, d < 4) → ∀ j (hj : j < L.length),
    pack4 L / 4 ^ j % 4 = L[j]
  | [], _, j, hj => by simp at hj
  | d :: L, h, 0, _ => by
    have hd : d < 4 := h d (by simp)
    simp only [pack4, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
    omega
  | d :: L, h, j + 1, hj => by
    have hd : d < 4 := h d (by simp)
    have ih := pack4_digit L (fun x hx => h x (by simp [hx])) j (by simpa using hj)
    simp only [pack4, List.getElem_cons_succ]
    rw [Nat.pow_succ, Nat.mul_comm (4 ^ j) 4, ← Nat.div_div_eq_div_mul,
      show (d + 4 * pack4 L) / 4 = pack4 L by omega]
    exact ih

theorem mcount_lt (M p q : Nat) : mcount M p q < 4 := Nat.mod_lt _ (by decide)

theorem mult_rtype (m p : Nat) (hp : p < 7) : mult (rtype m) p = mult m (rp p) := by
  unfold mult rtype
  have hd : ∀ d ∈ (List.ofFn fun i : Fin 7 => mult m (rp i)), d < 4 := by
    intro d hd
    rw [List.mem_ofFn] at hd
    obtain ⟨i, rfl⟩ := hd
    exact mult_lt _ _
  have hj : p < (List.ofFn fun i : Fin 7 => mult m (rp i)).length := by simp [hp]
  rw [pack4_digit _ hd p hj, List.getElem_ofFn]
  rfl

theorem mcount_rM (M p q : Nat) (hp : p < 7) (hq : q < 7) :
    mcount (rM M) p q = mcount M (rp p) (rp q) := by
  rw [mcount_eq_digit_cell]
  unfold digit rM
  have hd : ∀ d ∈ (List.ofFn fun i : Fin 49 => mcount M (rp (i.val / 7)) (rp (i.val % 7))),
      d < 4 := by
    intro d hd
    rw [List.mem_ofFn] at hd
    obtain ⟨i, rfl⟩ := hd
    exact mcount_lt _ _ _
  have hj : 7 * p + q <
      (List.ofFn fun i : Fin 49 => mcount M (rp (i.val / 7)) (rp (i.val % 7))).length := by
    simp; omega
  rw [pack4_digit _ hd (7 * p + q) hj, List.getElem_ofFn]
  simp only
  congr 2 <;> omega

theorem rtype_lt (m : Nat) : rtype m < 16384 := by
  have := pack4_lt (List.ofFn fun i : Fin 7 => mult m (rp i)) (by
    intro d hd
    rw [List.mem_ofFn] at hd
    obtain ⟨i, rfl⟩ := hd
    exact mult_lt _ _)
  unfold rtype
  rw [List.length_ofFn] at this
  exact this

theorem rM_lt (M : Nat) : rM M < 16384 ^ 7 := by
  have := pack4_lt (List.ofFn fun i : Fin 49 => mcount M (rp (i.val / 7)) (rp (i.val % 7))) (by
    intro d hd
    rw [List.mem_ofFn] at hd
    obtain ⟨i, rfl⟩ := hd
    exact mcount_lt _ _ _)
  rw [pow49]
  unfold rM
  rw [List.length_ofFn] at this
  exact this

theorem rtype_eq (m : Nat) : rtype m = mult m 3 + 4 * mult m 1 + 16 * mult m 5 + 64 * mult m 0
    + 256 * mult m 4 + 1024 * mult m 2 + 4096 * mult m 6 := by
  have h : rtype m = mult m 3 + 4 * (mult m 1 + 4 * (mult m 5 + 4 * (mult m 0 + 4 * (mult m 4
      + 4 * (mult m 2 + 4 * (mult m 6 + 4 * 0)))))) := rfl
  rw [h]; omega

/-! ### Row and column sums, validity, the order -/

theorem sumRow_rM (M p : Nat) (hp : p < 7) : sumRow (rM M) p = sumRow M (rp p) := by
  rw [sumRow_eq, sumRow_eq, mcount_rM M p 0 hp (by decide), mcount_rM M p 1 hp (by decide),
    mcount_rM M p 2 hp (by decide), mcount_rM M p 3 hp (by decide), mcount_rM M p 4 hp (by decide),
    mcount_rM M p 5 hp (by decide), mcount_rM M p 6 hp (by decide), rp_0, rp_1, rp_2, rp_3, rp_4,
    rp_5, rp_6]
  omega

theorem sumCol_rM (M q : Nat) (hq : q < 7) : sumCol (rM M) q = sumCol M (rp q) := by
  rw [sumCol_eq, sumCol_eq, mcount_rM M 0 q (by decide) hq, mcount_rM M 1 q (by decide) hq,
    mcount_rM M 2 q (by decide) hq, mcount_rM M 3 q (by decide) hq, mcount_rM M 4 q (by decide) hq,
    mcount_rM M 5 q (by decide) hq, mcount_rM M 6 q (by decide) hq, rp_0, rp_1, rp_2, rp_3, rp_4,
    rp_5, rp_6]
  omega

/-- the reflected key of a valid key is valid for the reflected types -/
theorem validKey_rM {mL mR M : Nat} (hv : validKey mL mR M = true) :
    validKey (rtype mL) (rtype mR) (rM M) = true := by
  apply validKey_of
  · intro p hp q hq hi
    rw [mcount_rM M p q hp hq]
    exact validKey_inter hv (rp p) (rp_lt p hp) (rp q) (rp_lt q hq) (by rw [inter_rp p hp q hq]; exact hi)
  · intro p hp
    rw [sumRow_rM M p hp, mult_rtype mL p hp]
    exact validKey_row hv (rp p) (rp_lt p hp)
  · intro q hq
    rw [sumCol_rM M q hq, mult_rtype mR q hq]
    exact validKey_col hv (rp q) (rp_lt q hq)

theorem keyLE_rM {M M' : Nat} (h : keyLE M M') : keyLE (rM M) (rM M') := by
  intro p hp q hq
  rw [mcount_rM M p q hp hq, mcount_rM M' p q hp hq]
  exact h (rp p) (rp_lt p hp) (rp q) (rp_lt q hq)

/-! ### The types -/

theorem rtype_mem_validTypes : ∀ m ∈ validTypes, rtype m ∈ validTypes := by
  rw [validTypes_eq]; decide +kernel

theorem rtype_UTYPE : rtype UTYPE = UTYPE := by decide

theorem rtype_eq_UTYPE_iff : ∀ m ∈ validTypes, (rtype m = UTYPE ↔ m = UTYPE) := by
  rw [validTypes_eq]; decide +kernel

/-! ### The law table is reflection-equivariant -/

/-- the kernel check: for every valid type and every signature, the mirrored type's count at the
mirrored signature is the type's count at the signature -/
theorem table_rsig : validTypes.all (fun m => (List.range 686).all fun s =>
    (subTable (typeIndex (rtype m)) / 100 ^ rsig s) % 100 == (subTable (typeIndex m) / 100 ^ s) % 100)
      = true := by
  rw [validTypes_eq]; decide +kernel

theorem subTable_rsig (m : Nat) (hm : m ∈ validTypes) (s : Nat) (hs : s < 686) :
    (subTable (typeIndex (rtype m)) / 100 ^ rsig s) % 100 = (subTable (typeIndex m) / 100 ^ s) % 100 := by
  have h := table_rsig
  rw [List.all_eq_true] at h
  have h' := h m hm
  rw [List.all_eq_true] at h'
  have := h' s (List.mem_range.2 hs)
  exact beq_iff_eq.1 this

end Grid3.Three.Cert
