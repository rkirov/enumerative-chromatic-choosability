/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.BitLP

/-!
# Height six at `k = 6`: primitive helpers for the kernel checks of the state bits

As in `GridGen/Five/K5/BitFast.lean`: primitive `Nat` operations (`fN` forces a value once,
`getR`, `all5k`, the codes `kHr`, `kMr`, `kXr`, the capacities `capR`, `eR`, `pairR`), the greedy
count checked with primitive operations (`gchk`, `gchk_eq`), the row conditions of the pins
(`pconds`, `rowOKp`, `eqOKp`, `evc_split`, `rows_all`), and the pointwise check: a class whose
states all pass at the `64` vectors of bonuses, with the largest admissible intersections
`emax` (`ptChk_spec`; by `N6g_anti` this covers every state). The certificate check over code
vectors is `chkW` in `GridGen/Six/BitDP.lean`.

Nothing is trusted: the checks are kernel computations, and their meaning is proved here.
-/

namespace GridGen.Six

open Finset

/-! ### Primitive helpers -/

/-- Evaluate `x` once and pass the value on. -/
def fN (x : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) x

theorem fN_eq (x : ℕ) (k : ℕ → Bool) : fN x k = k x := by
  cases x <;> rfl

/-- `L.getD n 0` by a recursor. -/
def getR (L : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun a _ ih n => Nat.casesOn (motive := fun _ => ℕ) n a ih) L

theorem getR_eq : ∀ (L : List ℕ) (n : ℕ), getR L n = L.getD n 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: L, n + 1 => by
    show getR L n = _
    rw [getR_eq L n]; rfl

/-- `p` at `0, …, 4`. -/
def all5k (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4

theorem all5k_spec {p : ℕ → Bool} (h : all5k p = true) {i : ℕ} (hi : i < 5) : p i = true := by
  simp only [all5k, Bool.and_eq_true] at h
  interval_cases i <;> tauto

/-- `p` at `0, 1`. -/
def all2k (p : ℕ → Bool) : Bool := p 0 && p 1

theorem all2k_spec {p : ℕ → Bool} (h : all2k p = true) {i : ℕ} (hi : i < 2) : p i = true := by
  simp only [all2k, Bool.and_eq_true] at h
  interval_cases i <;> tauto

def kHr (c : ℕ) : ℕ := cond (Nat.beq c 0) 1 0
def kMr (c : ℕ) : ℕ := cond (Nat.beq c 2 || Nat.beq c 4) 1 0
def kXr (c : ℕ) : ℕ := cond (Nat.beq c 3 || Nat.beq c 4) 1 0

theorem beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]

theorem ble_eq_decide (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]

theorem blt_eq_decide (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_eq]

theorem kHr_eq (c : ℕ) : kHr c = kH c := by
  unfold kHr kH; rw [beq_eq_decide]; by_cases h : c = 0 <;> simp [h]

theorem kMr_eq (c : ℕ) : kMr c = kM c := by
  unfold kMr kM; rw [beq_eq_decide, beq_eq_decide]
  by_cases h2 : c = 2 <;> by_cases h4 : c = 4 <;> simp [h2, h4]

theorem kXr_eq (c : ℕ) : kXr c = kX c := by
  unfold kXr kX; rw [beq_eq_decide, beq_eq_decide]
  by_cases h3 : c = 3 <;> by_cases h4 : c = 4 <;> simp [h3, h4]

/-- The capacity of one consecutive pair: its intersection plus its mismatch. -/
def capR (cp ci : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add 4 (kHr cp)) (kXr cp)) (kHr ci)) (kMr ci)

/-- The consecutive intersection from a code pair. -/
def eR (m cp ci : ℕ) : ℕ := Nat.sub (capR cp ci) m

/-- The admissibility of one consecutive pair. -/
def pairR (m cp ci : ℕ) : Bool :=
  (Nat.beq (kMr ci) 0 || Nat.blt 0 m) && (Nat.beq (kXr cp) 0 || Nat.blt 0 m) && Nat.ble m (capR cp ci)

def minR (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

theorem minR_eq (a b : ℕ) : minR a b = min a b := by
  unfold minR
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h, min_eq_left h]; rfl
  · have : Nat.ble a b = false := by
      rw [Bool.eq_false_iff]; intro hh; exact h (Nat.ble_eq.mp hh)
    rw [this, min_eq_right (by omega)]; rfl

/-- The size-vector index from the six bonuses. -/
def nidxR (a b c d e f : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 32 a) (Nat.mul 16 b)) (Nat.mul 8 c))
    (Nat.mul 4 d)) (Nat.mul 2 e)) f

theorem nidxR_eq (a b c d e f : ℕ) :
    nidxR a b c d e f = nidx (5 + a) (5 + b) (5 + c) (5 + d) (5 + e) (5 + f) := by
  simp only [nidxR, nidx, Nat.add_eq, Nat.mul_eq]; omega

/-! ### The greedy count, fast -/

/-- `A + B · N6gM ≤ B · N6gP`, in primitive operations. -/
def gchk (A B n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℕ) : Bool :=
  fN (Nat.sub (Nat.add e1 e2) n2) fun t1 => fN (Nat.sub (Nat.add e2 e3) n3) fun t2 =>
  fN (Nat.sub (Nat.add e3 e4) n4) fun t3 => fN (Nat.sub (Nat.add e4 e5) n5) fun t4 =>
  fN (minR t1 t2) fun q1 => fN (minR t2 t3) fun q2 => fN (minR t3 t4) fun q3 =>
  fN (Nat.sub (Nat.add q1 q2) t2) fun p1 => fN (Nat.sub (Nat.add q2 q3) t3) fun p2 =>
  Nat.ble (Nat.add A (Nat.mul B (
    Nat.add (minR p1 p2) (Nat.add (Nat.mul (Nat.mul q1 n5) n6) (Nat.add (Nat.mul (Nat.mul t1 e4) n6)
    (Nat.add (Nat.mul (Nat.mul t1 n4) e5) (Nat.add (Nat.mul (Nat.mul e1 t3) n6)
    (Nat.add (Nat.mul (Nat.mul e1 e3) e5) (Nat.add (Nat.mul (Nat.mul e1 n3) t4)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul (Nat.mul e1 n3) n4) n5) n6)
    (Nat.add (Nat.mul (Nat.mul n1 q2) n6) (Nat.add (Nat.mul (Nat.mul n1 t2) e5)
    (Nat.add (Nat.mul (Nat.mul n1 e2) t4) (Nat.add (Nat.mul (Nat.mul (Nat.mul (Nat.mul n1 e2) n4) n5) n6)
    (Nat.add (Nat.mul (Nat.mul n1 n2) q3)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul (Nat.mul n1 n2) e3) n5) n6)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul (Nat.mul n1 n2) n3) e4) n6)
    (Nat.mul (Nat.mul (Nat.mul (Nat.mul n1 n2) n3) n4) e5))))))))))))))))))
  (Nat.mul B (
    Nat.add (Nat.mul p1 n6) (Nat.add (Nat.mul q1 e5) (Nat.add (Nat.mul t1 t4)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul t1 n4) n5) n6) (Nat.add (Nat.mul e1 q3)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul e1 e3) n5) n6) (Nat.add (Nat.mul (Nat.mul (Nat.mul e1 n3) e4) n6)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul e1 n3) n4) e5) (Nat.add (Nat.mul n1 p2)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul n1 t2) n5) n6)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul n1 e2) e4) n6) (Nat.add (Nat.mul (Nat.mul (Nat.mul n1 e2) n4) e5)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul n1 n2) t3) n6) (Nat.add (Nat.mul (Nat.mul (Nat.mul n1 n2) e3) e5)
    (Nat.add (Nat.mul (Nat.mul (Nat.mul n1 n2) n3) t4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul n1 n2) n3) n4) n5) n6)))))))))))))))))

theorem gchk_eq (A B n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℕ) :
    gchk A B n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5
      = decide (A + B * N6gM n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5
          ≤ B * N6gP n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5) := by
  simp only [gchk, fN_eq, minR_eq, ble_eq_decide, N6gM, N6gP, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

/-! ### Pins filtered row by row -/

/-- The row conditions of the peels. -/
def peelConds : List BPeel6 → List (ℕ × ℕ)
  | [] => []
  | BPeel6.ev r k :: ps => (r, k) :: peelConds ps
  | BPeel6.eq _ _ :: ps => peelConds ps

/-- The equalities of the peels. -/
def peelEqs : List BPeel6 → List (ℕ × ℕ)
  | [] => []
  | BPeel6.ev _ _ :: ps => peelEqs ps
  | BPeel6.eq r j :: ps => (r, j) :: peelEqs ps

/-- The row conditions of a pin. -/
def pconds (q : BPin6) : List (ℕ × ℕ) := q.blk.conds ++ peelConds q.peels

/-- The conditions of a pin on row `r` hold at code `c`. -/
def rowOKp (q : BPin6) (r c : ℕ) : Bool :=
  (pconds q).all (fun rk => !(Nat.beq rk.1 r) || evk rk.2 c)

/-- The equalities of a pin hold on the pattern `p`. -/
def eqOKp (q : BPin6) (p : T6) : Bool := (peelEqs q.peels).all (fun rj => rowAt rj.1 p == rowAt rj.2 p)

theorem peels_evc (c p : T6) : ∀ ps : List BPeel6,
    ps.all (fun f => f.evc c p)
      = ((peelConds ps).all (fun rk => evk rk.2 (rowAt rk.1 c))
        && (peelEqs ps).all (fun rj => rowAt rj.1 p == rowAt rj.2 p))
  | [] => rfl
  | BPeel6.ev r k :: ps => by
    rw [List.all_cons, peels_evc c p ps]
    simp only [peelConds, peelEqs, List.all_cons, BPeel6.evc, Bool.and_assoc]
  | BPeel6.eq r j :: ps => by
    rw [List.all_cons, peels_evc c p ps]
    simp only [peelConds, peelEqs, List.all_cons, BPeel6.evc]
    cases (rowAt r p == rowAt j p) <;> cases (peelConds ps).all (fun rk => evk rk.2 (rowAt rk.1 c))
      <;> simp

theorem blk_evc (c : T6) :
    ∀ b : BBlk6, b.evc c = b.conds.all (fun rk => evk rk.2 (rowAt rk.1 c))
  | BBlk6.none => rfl
  | BBlk6.one r k => by simp [BBlk6.evc, BBlk6.conds]
  | BBlk6.two r k k' => by simp [BBlk6.evc, BBlk6.conds]
  | BBlk6.three r k k' k'' => by simp [BBlk6.evc, BBlk6.conds, Bool.and_assoc]

theorem evc_split (q : BPin6) (c p : T6) :
    q.evc c p = ((pconds q).all (fun rk => evk rk.2 (rowAt rk.1 c)) && eqOKp q p) := by
  rw [BPin6.evc, peels_evc, blk_evc, pconds, List.all_append, eqOKp]
  cases (BBlk6.conds q.blk).all (fun rk => evk rk.2 (rowAt rk.1 c)) <;>
    cases (peelConds q.peels).all (fun rk => evk rk.2 (rowAt rk.1 c)) <;> simp

/-- The row conditions of a well-formed pin are in range. -/
def condsOK (L : List (ℕ × ℕ)) : Prop := ∀ rk ∈ L, rk.1 < 6

theorem peelConds_ok : ∀ ps : List BPeel6, (ps.all BPeel6.okb) = true → condsOK (peelConds ps)
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | BPeel6.ev r k :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true, BPeel6.okb, decide_eq_true_eq] at h
    intro rk hrk
    rcases List.mem_cons.mp hrk with rfl | hrk
    · exact h.1.1
    · exact peelConds_ok ps h.2 rk hrk
  | BPeel6.eq r j :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact peelConds_ok ps h.2

theorem blk_conds_ok : ∀ b : BBlk6, b.okb = true → condsOK b.conds
  | BBlk6.none, _ => fun _ h => absurd h List.not_mem_nil
  | BBlk6.one r k, h => by
    simp only [BBlk6.okb, decide_eq_true_eq] at h
    intro rk hrk; simp only [BBlk6.conds, List.mem_singleton] at hrk; subst hrk; exact h.1
  | BBlk6.two r k k', h => by
    simp only [BBlk6.okb, decide_eq_true_eq] at h
    intro rk hrk; simp only [BBlk6.conds, List.mem_cons, List.not_mem_nil, or_false] at hrk
    rcases hrk with rfl | rfl
    · show r < 6; omega
    · show r + 1 < 6; omega
  | BBlk6.three r k k' k'', h => by
    simp only [BBlk6.okb, decide_eq_true_eq] at h
    intro rk hrk; simp only [BBlk6.conds, List.mem_cons, List.not_mem_nil, or_false] at hrk
    rcases hrk with rfl | rfl | rfl
    · show r < 6; omega
    · show r + 1 < 6; omega
    · show r + 2 < 6; omega

theorem pconds_ok {q : BPin6} (hq : q.okb = true) : condsOK (pconds q) := by
  simp only [BPin6.okb, Bool.and_eq_true] at hq
  intro rk hrk
  rcases List.mem_append.mp hrk with h | h
  · exact blk_conds_ok q.blk hq.1 rk h
  · exact peelConds_ok q.peels (bpeelOK_all hq.2) rk h

theorem rows_all (c : T6) : ∀ L : List (ℕ × ℕ), condsOK L →
    (L.all (fun rk => !(Nat.beq rk.1 5) || evk rk.2 (r6 c)) &&
      (L.all (fun rk => !(Nat.beq rk.1 4) || evk rk.2 (r5 c)) &&
      (L.all (fun rk => !(Nat.beq rk.1 3) || evk rk.2 (r4 c)) &&
      (L.all (fun rk => !(Nat.beq rk.1 2) || evk rk.2 (r3 c)) &&
      (L.all (fun rk => !(Nat.beq rk.1 1) || evk rk.2 (r2 c)) &&
      L.all (fun rk => !(Nat.beq rk.1 0) || evk rk.2 (r1 c)))))))
      = L.all (fun rk => evk rk.2 (rowAt rk.1 c))
  | [], _ => rfl
  | (r, k) :: L, h => by
    have ih := rows_all c L (fun rk hrk => h rk (List.mem_cons_of_mem _ hrk))
    have hr : r < 6 := h (r, k) List.mem_cons_self
    simp only [List.all_cons]
    rw [← ih]
    interval_cases r <;>
    · simp only [Nat.beq, rowAt, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or,
        Bool.true_and]
      cases evk k (r1 c) <;> cases evk k (r2 c) <;> cases evk k (r3 c) <;> cases evk k (r4 c) <;>
        cases evk k (r5 c) <;> cases evk k (r6 c) <;> simp

/-! ### Admissible code vectors -/

/-- The admissibility of a code vector. -/
def bvalid6 (m1 m2 m3 m4 m5 : ℕ) (c : T6) : Prop :=
  kM (r1 c) = 0 ∧ kX (r6 c) = 0 ∧ pairR m1 (r1 c) (r2 c) = true ∧ pairR m2 (r2 c) (r3 c) = true ∧
    pairR m3 (r3 c) (r4 c) = true ∧ pairR m4 (r4 c) (r5 c) = true ∧ pairR m5 (r5 c) (r6 c) = true

/-- The codes are below `5`. -/
def codes5 (c : T6) : Prop :=
  r1 c < 5 ∧ r2 c < 5 ∧ r3 c < 5 ∧ r4 c < 5 ∧ r5 c < 5 ∧ r6 c < 5

/-! ### The pointwise check -/

/-- The largest admissible intersection of a pair with bonuses `h, h'`. -/
def emaxR (m h h' : ℕ) : ℕ := cond (Nat.blt 0 m) (Nat.sub 6 m) (Nat.add (Nat.add 4 h) h')

def emax (m h h' : ℕ) : ℕ := if 0 < m then 6 - m else 4 + h + h'

theorem emaxR_eq (m h h' : ℕ) : emaxR m h h' = emax m h h' := by
  unfold emaxR emax; rw [blt_eq_decide]; by_cases hm : 0 < m <;> simp [hm]

def pt6 (NM : List ℕ) (m1 m2 m3 m4 m5 h1 h2 h3 h4 h5 : ℕ) : Bool :=
  all2k fun h6 => gchk (getR NM (nidxR h1 h2 h3 h4 h5 h6)) 1000000000000
    (Nat.add 5 h1) (Nat.add 5 h2) (Nat.add 5 h3) (Nat.add 5 h4) (Nat.add 5 h5) (Nat.add 5 h6)
    (emaxR m1 h1 h2) (emaxR m2 h2 h3) (emaxR m3 h3 h4) (emaxR m4 h4 h5) (emaxR m5 h5 h6)

def pt5 (NM : List ℕ) (m1 m2 m3 m4 m5 h1 h2 h3 h4 : ℕ) : Bool :=
  all2k fun h5 => pt6 NM m1 m2 m3 m4 m5 h1 h2 h3 h4 h5
def pt4 (NM : List ℕ) (m1 m2 m3 m4 m5 h1 h2 h3 : ℕ) : Bool :=
  all2k fun h4 => pt5 NM m1 m2 m3 m4 m5 h1 h2 h3 h4
def pt3 (NM : List ℕ) (m1 m2 m3 m4 m5 h1 h2 : ℕ) : Bool :=
  all2k fun h3 => pt4 NM m1 m2 m3 m4 m5 h1 h2 h3
def pt2 (NM : List ℕ) (m1 m2 m3 m4 m5 h1 : ℕ) : Bool :=
  all2k fun h2 => pt3 NM m1 m2 m3 m4 m5 h1 h2

/-- **The pointwise check** of a class at the `64` vectors of bonuses. -/
def ptChk (NM : List ℕ) (m1 m2 m3 m4 m5 : ℕ) : Bool :=
  all2k fun h1 => pt2 NM m1 m2 m3 m4 m5 h1

theorem ptChk_spec {NM : List ℕ} {m1 m2 m3 m4 m5 : ℕ} (h : ptChk NM m1 m2 m3 m4 m5 = true)
    {h1 h2 h3 h4 h5 h6 : ℕ} (g1 : h1 < 2) (g2 : h2 < 2) (g3 : h3 < 2) (g4 : h4 < 2)
    (g5 : h5 < 2) (g6 : h6 < 2) :
    NM.getD (nidx (5 + h1) (5 + h2) (5 + h3) (5 + h4) (5 + h5) (5 + h6)) 0
      + 1000000000000 * N6gM (5 + h1) (5 + h2) (5 + h3) (5 + h4) (5 + h5) (5 + h6)
        (emax m1 h1 h2) (emax m2 h2 h3) (emax m3 h3 h4) (emax m4 h4 h5) (emax m5 h5 h6)
      ≤ 1000000000000 * N6gP (5 + h1) (5 + h2) (5 + h3) (5 + h4) (5 + h5) (5 + h6)
        (emax m1 h1 h2) (emax m2 h2 h3) (emax m3 h3 h4) (emax m4 h4 h5) (emax m5 h5 h6) := by
  have k := all2k_spec (all2k_spec (all2k_spec (all2k_spec (all2k_spec (all2k_spec h g1) g2) g3)
    g4) g5) g6
  rw [gchk_eq, getR_eq, nidxR_eq, decide_eq_true_eq] at k
  simp only [emaxR_eq, Nat.add_eq] at k
  rw [show 5 + h1 = h1 + 5 by ring, show 5 + h2 = h2 + 5 by ring, show 5 + h3 = h3 + 5 by ring,
    show 5 + h4 = h4 + 5 by ring, show 5 + h5 = h5 + 5 by ring, show 5 + h6 = h6 + 5 by ring]
  rw [show 5 + h1 = h1 + 5 by ring, show 5 + h2 = h2 + 5 by ring, show 5 + h3 = h3 + 5 by ring,
    show 5 + h4 = h4 + 5 by ring, show 5 + h5 = h5 + 5 by ring, show 5 + h6 = h6 + 5 by ring] at k
  exact k

end GridGen.Six
