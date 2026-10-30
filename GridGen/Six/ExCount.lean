/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Cone
import GridGen.Six.ExCountData

/-!
# Height six at `k = 6`: orbit counts for the exact certificates

The exact layer (`GridGen/Six/ExDefs.lean`) needs, at every column type, the orbit counts of
the proper colourings of six lists given by bit masks (`cntO`, `card_orb_setOf`). The kernel
computes them as follows:

* the intersections of the masks over all `63` sets of rows, by doubling (`atL`: the list for
  rows `< r + 1` is the list for rows `< r` followed by its intersections with mask `r`);
* their sizes, packed four bits each into one natural (`pk`, `lane`, `PT` for the sizes of
  bytes);
* for each of the `203` set partitions `q`, `N_q` as the product of the packed sizes of its
  blocks (`nvq`, `nvq_eq`), times its Möbius coefficients folded into the six cone functionals
  (the five rays and the lower edge of `Q`), positive and negative parts packed `96` bits each
  (`MQ6`); the accumulation `accS` holds all twelve lanes (`lanes_fun`).

The intersections are also computed by doubling on one packed natural (`dblT_eq`), which is what
the kernel runs (`GridGen/Six/ExDefs.lean`).

The data (`MQ6`, `MQC`) are tied to the Möbius table `MOBT` of `GridGen/Six/PartData.lean` by
kernel checks (`el_ok`, `lane_bound`, `mqc_ok`).
-/

namespace GridGen.Six

open Finset

/-! ### Forcing -/

/-- Evaluate `x` once and pass the value on. -/
def xN (x : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) x

theorem xN_eq (x : ℕ) (k : ℕ → Bool) : xN x k = k x := by
  cases x <;> rfl

/-! ### Packing in lanes -/

/-- Lane `i` of `x`, lanes of `L` bits. -/
def lane (L x i : ℕ) : ℕ := x / 2 ^ (L * i) % 2 ^ L

/-- `Σ_{i<n} f i · 2^(L i)`, in Horner form. -/
def pkF (L : ℕ) : (ℕ → ℕ) → ℕ → ℕ
  | _, 0 => 0
  | f, n + 1 => f 0 + 2 ^ L * pkF L (fun i => f (i + 1)) n

/-- A list packed in lanes, in Horner form. -/
def pk (L : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 ^ L * pk L xs

theorem pk_eq_pkF (L : ℕ) : ∀ xs : List ℕ, pk L xs = pkF L (fun i => xs.getD i 0) xs.length
  | [] => rfl
  | x :: xs => by
    rw [pk, pk_eq_pkF L xs, List.length_cons, pkF]
    simp

theorem lane_zero_add {L a b : ℕ} (ha : a < 2 ^ L) : lane L (a + 2 ^ L * b) 0 = a := by
  unfold lane
  rw [Nat.mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem lane_succ_add {L a b : ℕ} (ha : a < 2 ^ L) (i : ℕ) :
    lane L (a + 2 ^ L * b) (i + 1) = lane L b i := by
  unfold lane
  rw [show L * (i + 1) = L + L * i by ring, pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, zero_add]

theorem lane_pkF {L : ℕ} : ∀ {n : ℕ} {f : ℕ → ℕ}, (∀ i < n, f i < 2 ^ L) →
    ∀ {k}, k < n → lane L (pkF L f n) k = f k
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, f, h, k, hk => by
    rw [pkF]
    cases k with
    | zero => exact lane_zero_add (h 0 (by omega))
    | succ k =>
      rw [lane_succ_add (h 0 (by omega))]
      exact lane_pkF (f := fun i => f (i + 1)) (fun i hi => h (i + 1) (by omega)) (by omega)

theorem pkF_congr {L : ℕ} : ∀ {n : ℕ} {f g : ℕ → ℕ}, (∀ i < n, f i = g i) → pkF L f n = pkF L g n
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    rw [pkF, pkF, h 0 (by omega), pkF_congr (fun i hi => h (i + 1) (by omega))]

theorem pkF_add {L : ℕ} : ∀ {n : ℕ} (f g : ℕ → ℕ),
    pkF L f n + pkF L g n = pkF L (fun i => f i + g i) n
  | 0, _, _ => rfl
  | n + 1, f, g => by
    rw [pkF, pkF, pkF, ← pkF_add]
    ring

theorem pkF_mul {L : ℕ} (a : ℕ) : ∀ {n : ℕ} (f : ℕ → ℕ), a * pkF L f n = pkF L (fun i => a * f i) n
  | 0, _ => by simp [pkF]
  | n + 1, f => by
    rw [pkF, pkF, ← pkF_mul a]
    ring

theorem pkF_zero {L : ℕ} : ∀ {n : ℕ}, pkF L (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [pkF, pkF_zero]; simp

/-! ### The sizes of bytes -/

theorem lane_PT : ∀ x < 256, lane 4 PT x = popc x := by decide +kernel

/-! ### The intersections by doubling -/

/-- The intersection of the masks of the rows `i < r` of `S`, within a byte. -/
def andR (ms : List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 255
  | r + 1, S => if S.testBit r then andR ms r S &&& ms.getD r 0 else andR ms r S

/-- The intersections for all sets of rows `< r`, by doubling. -/
def atL (ms : List ℕ) : ℕ → List ℕ
  | 0 => [255]
  | r + 1 => atL ms r ++ (atL ms r).map (fun x => x &&& ms.getD r 0)

theorem atL_length (ms : List ℕ) : ∀ r, (atL ms r).length = 2 ^ r
  | 0 => rfl
  | r + 1 => by rw [atL, List.length_append, List.length_map, atL_length ms r, pow_succ]; ring

theorem andR_mod (ms : List ℕ) : ∀ r S, andR ms r S = andR ms r (S % 2 ^ r)
  | 0, _ => rfl
  | r + 1, S => by
    have hb : (S % 2 ^ (r + 1)).testBit r = S.testBit r := by
      rw [Nat.testBit_mod_two_pow]; simp
    have hm : S % 2 ^ (r + 1) % 2 ^ r = S % 2 ^ r := by
      rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ r))]
    rw [andR, andR, hb, andR_mod ms r S, andR_mod ms r (S % 2 ^ (r + 1)), hm]

theorem getD_map_lt {f : ℕ → ℕ} {l : List ℕ} {n : ℕ} (h : n < l.length) :
    (l.map f).getD n 0 = f (l.getD n 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
  simp

theorem foldr_and_lt (c : ℕ → Prop) [DecidablePred c] (ms : List ℕ) :
    ∀ L : List ℕ, L.foldr (fun i acc => if c i then (ms.getD i 0) &&& acc else acc) 255 < 256
  | [] => by show (255 : ℕ) < 256; norm_num
  | i :: L => by
    rw [List.foldr_cons]
    split_ifs
    · exact lt_of_le_of_lt Nat.and_le_right (foldr_and_lt c ms L)
    · exact foldr_and_lt c ms L

theorem atL_getD (ms : List ℕ) : ∀ r S, S < 2 ^ r → (atL ms r).getD S 0 = andR ms r S
  | 0, S, h => by
    have : S = 0 := by simpa using h
    subst this; rfl
  | r + 1, S, h => by
    rw [atL]
    rcases Nat.lt_or_ge S (2 ^ r) with h1 | h1
    · rw [List.getD_append _ _ _ _ (by rw [atL_length]; exact h1), atL_getD ms r S h1, andR]
      have : S.testBit r = false := Nat.testBit_lt_two_pow h1
      rw [this, if_neg (by simp)]
    · have hlen := atL_length ms r
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; exact h1), hlen, getD_map_lt (by rw [hlen]; rw [pow_succ] at h; omega)]
      have h2 : S - 2 ^ r < 2 ^ r := by rw [pow_succ] at h; omega
      rw [atL_getD ms r _ h2, andR]
      have hS : S.testBit r = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have : S / 2 ^ r = 1 := by
          apply Nat.div_eq_of_lt_le <;> rw [pow_succ] at h <;> omega
        simp [this]
      rw [if_pos hS]
      have hm : (S - 2 ^ r) % 2 ^ r = S % 2 ^ r := by
        rw [Nat.mod_eq_of_lt h2]
        have : S % 2 ^ r = S - 2 ^ r := by
          rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2]
        rw [this]
      rw [andR_mod ms r (S - 2 ^ r), hm, ← andR_mod]

theorem andR_lt (ms : List ℕ) : ∀ r S, andR ms r S < 256
  | 0, _ => by show (255 : ℕ) < 256; norm_num
  | r + 1, S => by
    rw [andR]
    split_ifs
    · exact lt_of_le_of_lt Nat.and_le_left (andR_lt ms r S)
    · exact andR_lt ms r S

theorem testBit_andR (ms : List ℕ) : ∀ r S t, t < 8 →
    (andR ms r S).testBit t = (List.range r).all (fun i => !(S.testBit i) || (ms.getD i 0).testBit t)
  | 0, S, t, ht => by
    simp only [andR, List.range_zero, List.all_nil]
    interval_cases t <;> decide
  | r + 1, S, t, ht => by
    rw [andR, List.range_succ, List.all_append, ← testBit_andR ms r S t ht]
    split_ifs with h
    · simp [h, Nat.testBit_and]
    · simp [h]

/-! ### Blocks of a partition -/

/-- The rows of block `k` of `q`, as a bit mask. -/
def bmask (q : T6) (k : ℕ) : ℕ :=
  (if rowAt 0 q = k then 1 else 0) + (if rowAt 1 q = k then 2 else 0) +
    (if rowAt 2 q = k then 4 else 0) + (if rowAt 3 q = k then 8 else 0) +
    (if rowAt 4 q = k then 16 else 0) + (if rowAt 5 q = k then 32 else 0)

theorem bm6_testBit : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ i < 6,
    ((cond b0 1 0) + (cond b1 2 0) + (cond b2 4 0) + (cond b3 8 0) + (cond b4 16 0) +
      (cond b5 32 0) : ℕ).testBit i = [b0, b1, b2, b3, b4, b5].getD i false := by decide

theorem bm6_lt : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    ((cond b0 1 0) + (cond b1 2 0) + (cond b2 4 0) + (cond b3 8 0) + (cond b4 16 0) +
      (cond b5 32 0) : ℕ) < 64 := by decide

theorem bmask_eq (q : T6) (k : ℕ) : bmask q k = (cond (decide (rowAt 0 q = k)) 1 0) +
    (cond (decide (rowAt 1 q = k)) 2 0) + (cond (decide (rowAt 2 q = k)) 4 0) +
    (cond (decide (rowAt 3 q = k)) 8 0) + (cond (decide (rowAt 4 q = k)) 16 0) +
    (cond (decide (rowAt 5 q = k)) 32 0) := by
  unfold bmask
  simp only [cond_eq_ite, decide_eq_true_eq]

theorem bmask_testBit (q : T6) (k : ℕ) {i : ℕ} (hi : i < 6) :
    (bmask q k).testBit i = decide (rowAt i q = k) := by
  rw [bmask_eq, bm6_testBit _ _ _ _ _ _ i hi]
  interval_cases i <;> rfl

theorem bmask_lt (q : T6) (k : ℕ) : bmask q k < 64 := by
  rw [bmask_eq]; exact bm6_lt _ _ _ _ _ _

theorem blk_eq_andR (q : T6) (ms : List ℕ) (k : ℕ) : blk q ms k = andR ms 6 (bmask q k) := by
  apply Nat.eq_of_testBit_eq
  intro t
  rcases Nat.lt_or_ge t 8 with ht | ht
  · rw [testBit_blk q ms k t ht, testBit_andR ms 6 _ t ht]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.all_append,
      List.all_cons, List.all_nil, bmask_testBit q k (show 0 < 6 by norm_num),
      bmask_testBit q k (show 1 < 6 by norm_num), bmask_testBit q k (show 2 < 6 by norm_num),
      bmask_testBit q k (show 3 < 6 by norm_num), bmask_testBit q k (show 4 < 6 by norm_num),
      bmask_testBit q k (show 5 < 6 by norm_num), Bool.beq_eq_decide_eq]
  · have h1 : blk q ms k < 256 := foldr_and_lt _ ms _
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (by
        calc (256 : ℕ) = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (andR_lt ms 6 _) (by
        calc (256 : ℕ) = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht))]

/-- The block masks of a partition. -/
def bms (q : T6) : List ℕ := ((List.range 6).filter (fun k => rowAt k q = k)).map (bmask q)

/-- `N_q` from packed sizes. -/
def nvq (I : ℕ) (bs : List ℕ) : ℕ := bs.foldr (fun b acc => lane 4 I b * acc) 1

theorem Nq_eq_prod (q : T6) (ms : List ℕ) :
    Nq q ms = ((bms q).map fun b => popc (andR ms 6 b)).prod := by
  unfold Nq bms
  simp only [blk_eq_andR, List.range_succ, List.range_zero, List.nil_append,
    List.filter_append, List.filter_cons, List.filter_nil, decide_eq_true_eq]
  split_ifs <;> simp [List.prod_cons, mul_assoc, mul_comm, mul_left_comm]

/-! ### The packed sizes of all intersections -/

/-- The sizes of all `64` intersections, packed four bits each. -/
def itab (ms : List ℕ) : ℕ := pk 4 ((atL ms 6).map fun x => lane 4 PT x)

theorem lane_itab (ms : List ℕ) {S : ℕ} (hS : S < 64) :
    lane 4 (itab ms) S = popc (andR ms 6 S) := by
  have hlen : ((atL ms 6).map fun x => lane 4 PT x).length = 64 := by
    rw [List.length_map, atL_length]; norm_num
  unfold itab
  rw [pk_eq_pkF, lane_pkF _ (by rw [hlen]; exact hS)]
  · rw [getD_map_lt (by rw [atL_length]; norm_num; exact hS), atL_getD ms 6 S (by norm_num; exact hS),
      lane_PT _ (andR_lt ms 6 S)]
  · intro i hi
    rw [hlen] at hi
    rw [getD_map_lt (by rw [atL_length]; norm_num; omega), atL_getD ms 6 i (by norm_num; omega),
      lane_PT _ (andR_lt ms 6 i)]
    have : popc (andR ms 6 i) ≤ 8 := by
      rw [← card_setOf]; unfold setOf; exact (Finset.card_filter_le _ _).trans (by simp)
    omega

theorem nvq_eq (ms : List ℕ) (q : T6) : nvq (itab ms) (bms q) = Nq q ms := by
  rw [Nq_eq_prod]
  have hb : ∀ b ∈ bms q, b < 64 := by
    intro b hb
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hb
    exact bmask_lt q k
  unfold nvq
  generalize bms q = L at hb
  induction L with
  | nil => rfl
  | cons b L ih =>
    rw [List.foldr_cons, List.map_cons, List.prod_cons, ih (fun x hx => hb x (by simp [hx])),
      lane_itab ms (hb b (by simp))]

/-! ### The intersections, packed by doubling -/

theorem pk_append (L : ℕ) : ∀ xs ys : List ℕ, pk L (xs ++ ys) = pk L xs + 2 ^ (L * xs.length) * pk L ys
  | [], ys => by simp [pk]
  | x :: xs, ys => by
    rw [List.cons_append, pk, pk, pk_append L xs ys, List.length_cons, show L * (xs.length + 1)
      = L + L * xs.length by ring, pow_add]
    ring

theorem land_add_two_pow {k a b X Y : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * X) &&& (b + 2 ^ k * Y) = (a &&& b) + 2 ^ k * (X &&& Y) := by
  have hab : (a &&& b) < 2 ^ k := lt_of_le_of_lt Nat.and_le_left ha
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, add_comm a, add_comm b, add_comm (a &&& b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ hab]
  split_ifs <;> simp [Nat.testBit_and]

theorem pk_land (m : ℕ) (hm : m < 256) : ∀ xs : List ℕ, (∀ x ∈ xs, x < 256) →
    pk 8 xs &&& pk 8 (List.replicate xs.length m) = pk 8 (xs.map fun x => x &&& m)
  | [], _ => by simp [pk]
  | x :: xs, h => by
    rw [List.length_cons, List.replicate_succ, pk, pk, List.map_cons, pk,
      land_add_two_pow (by have := h x (by simp); norm_num; omega) (by norm_num; omega),
      pk_land m hm xs (fun y hy => h y (by simp [hy]))]

theorem mul_pk_ones (m : ℕ) : ∀ n, m * pk 8 (List.replicate n 1) = pk 8 (List.replicate n m)
  | 0 => by simp [pk]
  | n + 1 => by
    rw [List.replicate_succ, List.replicate_succ, pk, pk, ← mul_pk_ones m n]
    ring

theorem atL_lt (ms : List ℕ) (r : ℕ) : ∀ x ∈ atL ms r, x < 256 := by
  intro x hx
  obtain ⟨S, hS, rfl⟩ := List.getElem_of_mem hx
  have := atL_getD ms r S (by rw [← atL_length ms r]; exact hS)
  rw [List.getD_eq_getElem _ _ hS] at this
  rw [this]; exact andR_lt ms r S

/-- One doubling step on the packed intersections. -/
def dblT (T m r : ℕ) : ℕ :=
  Nat.add T (Nat.mul (Nat.pow 2 (Nat.mul 8 (Nat.pow 2 r)))
    (Nat.land T (Nat.mul m (pk 8 (List.replicate (2 ^ r) 1)))))

theorem dblT_eq (ms : List ℕ) (hms : ∀ r, ms.getD r 0 < 256) (r : ℕ) :
    dblT (pk 8 (atL ms r)) (ms.getD r 0) r = pk 8 (atL ms (r + 1)) := by
  unfold dblT
  show pk 8 (atL ms r) + 2 ^ (8 * 2 ^ r) * (pk 8 (atL ms r) &&&
    (ms.getD r 0 * pk 8 (List.replicate (2 ^ r) 1))) = _
  rw [atL, pk_append, mul_pk_ones, ← atL_length ms r, pk_land _ (hms r) _ (atL_lt ms r)]

/-! ### The Möbius data -/

/-- The coefficient of orbit `o` at an entry. -/
def mqc (o : ℕ) (c : List ℕ × List ℕ) : ℤ := (c.1.getD o 0 : ℤ) - c.2.getD o 0

/-- The six cone functionals: the five rays and the lower edge of `Q`. -/
def FUN : List (List ℕ) := FL.take 5 ++ [qLL]

/-- `Σₒ aₒ bₒ`. -/
def dotZ (a b : List ℕ) : ℕ := (List.zipWith (· * ·) a b).sum

/-- The twelve lanes of an entry: positive, then negative parts of the six functionals of its
coefficients. -/
def lanesOf (c : List ℕ × List ℕ) : List ℕ :=
  FUN.map (fun F => dotZ c.1 F - dotZ c.2 F) ++ FUN.map (fun F => dotZ c.2 F - dotZ c.1 F)

/-- The partitions with their coefficients and packed data. -/
def EL : List ((T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))) :=
  (PART.zip PEL).zip (MQC.zip MQ6)

/-- An entry is consistent: its blocks, the lengths, and its packed lanes. -/
def entOK (e : (T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))) : Bool :=
  decide (e.2.2.1 = bms e.1.1 ∧ e.2.1.1.length = 32 ∧ e.2.1.2.length = 32 ∧
    e.2.2.2 = pk 96 (lanesOf e.2.1))

theorem el_ok : EL.map (fun e => e.2.2) = MQ6 ∧ EL.all entOK = true := by decide +kernel

/-- The lane sums stay below `2⁹⁶` for counts at most `8⁶`. -/
theorem lane_bound : ∀ i < 12, ((EL.map fun e => (lanesOf e.2.1).getD i 0).sum) * 262144
    < 2 ^ 96 := by decide +kernel

theorem fun_len : FUN.length = 6 ∧ ∀ F ∈ FUN, F.length = 32 := by decide +kernel

/-- The Möbius table from the coefficients. -/
def mobOf (o : ℕ) : List (T6 × List Bool × ℤ) :=
  EL.filterMap fun e => if mqc o e.2.1 = 0 then none else some (e.1.1, e.1.2, mqc o e.2.1)

/-- A Möbius entry with its column written as a list. -/
def entL (x : T6 × List Bool × ℤ) : List ℕ × List Bool × ℤ :=
  ([x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2.1, x.1.2.2.2.2.2], x.2.1, x.2.2)

theorem entL_inj : Function.Injective entL := by
  rintro ⟨⟨a1, a2, a3, a4, a5, a6⟩, b, c⟩ ⟨⟨a1', a2', a3', a4', a5', a6'⟩, b', c'⟩ h
  simp only [entL, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ := h
  rfl

theorem mqc_ok0 : (List.range 16).all
    (fun o => decide ((MOBT.getD o []).map entL = (mobOf o).map entL)) = true := by
  decide +kernel

theorem mqc_ok1 : ((List.range 16).map (· + 16)).all
    (fun o => decide ((MOBT.getD o []).map entL = (mobOf o).map entL)) = true := by
  decide +kernel

theorem mqc_ok {o : ℕ} (ho : o < 32) : MOBT.getD o [] = mobOf o := by
  apply List.map_injective_iff.mpr entL_inj
  rcases Nat.lt_or_ge o 16 with h | h
  · have := List.all_eq_true.mp mqc_ok0 o (List.mem_range.mpr h)
    simpa using this
  · have := List.all_eq_true.mp mqc_ok1 o (List.mem_map.mpr ⟨o - 16, List.mem_range.mpr (by omega),
      by omega⟩)
    simpa using this

theorem sum_filterMap_mob (o : ℕ) (ms : List ℕ) :
    ∀ E : List ((T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))),
    ((E.filterMap fun e => if mqc o e.2.1 = 0 then none else some (e.1.1, e.1.2, mqc o e.2.1)).map
        fun x => x.2.2 * (Nq x.1 ms : ℤ)).sum
      = (E.map fun e => mqc o e.2.1 * (Nq e.1.1 ms : ℤ)).sum
  | [] => rfl
  | e :: E => by
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← sum_filterMap_mob o ms E]
    split_ifs with h
    · simp [h]
    · simp

/-- **The orbit counts from the coefficients.** -/
theorem cntO_eq_mqc (ms : List ℕ) {o : ℕ} (ho : o < 32) :
    cntO o ms = (EL.map fun e => mqc o e.2.1 * (Nq e.1.1 ms : ℤ)).sum := by
  rw [cntO, mqc_ok ho, mobOf, sum_filterMap_mob]

/-! ### The accumulation -/

/-- Lane `i` of four bits, with primitive operations. -/
def lane4 (x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 4 i)) 15

theorem lane4_eq (x i : ℕ) : lane4 x i = lane 4 x i := by
  unfold lane4 lane
  rw [show (15 : ℕ) = 2 ^ 4 - 1 by norm_num]
  rw [show Nat.land (Nat.shiftRight x (Nat.mul 4 i)) (2 ^ 4 - 1)
      = (x >>> (4 * i)) &&& (2 ^ 4 - 1) from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

/-- `nvq` with primitive operations. -/
def nvqF (I : ℕ) (bs : List ℕ) : ℕ := bs.foldr (fun b acc => Nat.mul (lane4 I b) acc) 1

theorem nvqF_eq (I : ℕ) (bs : List ℕ) : nvqF I bs = nvq I bs := by
  unfold nvqF nvq
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [List.foldr_cons, List.foldr_cons, ih, lane4_eq]; rfl

/-- `Σ_q N_q · (packed lanes of q)` over a list of entries. -/
def accS (I : ℕ) : List (List ℕ × ℕ) → ℕ
  | [] => 0
  | x :: L => Nat.add (Nat.mul (nvqF I x.1) x.2) (accS I L)

theorem sum_map_sub_int {α : Type*} (f g : α → ℤ) : ∀ L : List α,
    (L.map f).sum - (L.map g).sum = (L.map fun x => f x - g x).sum
  | [] => by simp
  | x :: L => by
    simp only [List.map_cons, List.sum_cons, ← sum_map_sub_int f g L]
    ring

theorem card_prodS_le (A B C D E F : ℕ) :
    (prodS (setOf A) (setOf B) (setOf C) (setOf D) (setOf E) (setOf F)).card ≤ 262144 := by
  have h8 : ∀ m, (setOf m).card ≤ 8 := fun m => by
    unfold setOf; exact (Finset.card_filter_le _ _).trans (by simp)
  simp only [prodS, Finset.card_product]
  have := Nat.mul_le_mul (h8 A) (Nat.mul_le_mul (h8 B) (Nat.mul_le_mul (h8 C)
    (Nat.mul_le_mul (h8 D) (Nat.mul_le_mul (h8 E) (h8 F)))))
  simpa using this

theorem Nq_le (ms : List ℕ) {q : T6} (hq : foT q = q) : Nq q ms ≤ 262144 := by
  rw [← card_const_eq hq]
  exact (Finset.card_filter_le _ _).trans (card_prodS_le _ _ _ _ _ _)

theorem foT_EL : ∀ e ∈ EL, foT e.1.1 = e.1.1 := by
  intro e he
  have h1 : e.1 ∈ PART.zip PEL := (List.of_mem_zip he).1
  exact foT_of_mem_PART (List.of_mem_zip h1).1

theorem dotZ_eq : ∀ (a b : List ℕ), a.length = 32 → b.length = 32 →
    dotZ a b = ∑ o : Fin 32, a.getD o 0 * b.getD o 0 := by
  intro a b ha hb
  rw [Fin.sum_univ_eq_sum_range (fun o => a.getD o 0 * b.getD o 0)]
  unfold dotZ
  have key : ∀ (a b : List ℕ) (n : ℕ), a.length = n → b.length = n →
      (List.zipWith (· * ·) a b).sum = ∑ o ∈ Finset.range n, a.getD o 0 * b.getD o 0 := by
    intro a b n
    induction a generalizing b n with
    | nil => intro h _; subst h; simp
    | cons x a ih =>
      intro h1 h2
      cases b with
      | nil => simp at h1 h2; omega
      | cons y b =>
        cases n with
        | zero => simp at h1
        | succ n =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
          rw [List.zipWith_cons_cons, List.sum_cons, ih b n h1 h2, Finset.sum_range_succ']
          simp [add_comm]
  exact key a b 32 ha hb

/-- **The six functionals of the orbit counts in lanes.** For `d < 6`, lane `d` minus lane
`6 + d` of `accS (itab ms) MQ6` is `Σₒ cntO o ms · Fₒ` for the functional `F = FUN[d]`. -/
theorem lanes_fun (ms : List ℕ) {d : ℕ} (hd : d < 6) :
    ((lane 96 (accS (itab ms) MQ6) d : ℕ) : ℤ) - (lane 96 (accS (itab ms) MQ6) (6 + d) : ℕ)
      = ∑ o : Fin 32, cntO o ms * ((FUN.getD d []).getD o 0 : ℕ) := by
  obtain ⟨hE, hok⟩ := el_ok
  have hok' : ∀ e ∈ EL, entOK e = true := List.all_eq_true.mp hok
  have hent : ∀ e ∈ EL, e.2.2.1 = bms e.1.1 ∧ e.2.1.1.length = 32 ∧ e.2.1.2.length = 32 ∧
      e.2.2.2 = pk 96 (lanesOf e.2.1) := fun e he => by
    have := hok' e he; simpa only [entOK, decide_eq_true_eq] using this
  have hlen : ∀ e ∈ EL, (lanesOf e.2.1).length = 12 := fun e _ => by
    simp [lanesOf, fun_len.1]
  -- the accumulation as packed lane sums
  have hacc : accS (itab ms) MQ6
      = pkF 96 (fun i => (EL.map fun e => Nq e.1.1 ms * (lanesOf e.2.1).getD i 0).sum) 12 := by
    rw [← hE]
    have : ∀ E : List ((T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))),
        (∀ e ∈ E, e ∈ EL) → accS (itab ms) (E.map fun e => e.2.2)
          = pkF 96 (fun i => (E.map fun e => Nq e.1.1 ms * (lanesOf e.2.1).getD i 0).sum) 12 := by
      intro E hEL
      induction E with
      | nil => simp [accS, pkF_zero]
      | cons e E ih =>
        have he := hent e (hEL e (by simp))
        rw [List.map_cons, accS, ih (fun x hx => hEL x (by simp [hx])), he.2.2.2, nvqF_eq, he.1,
          nvq_eq, pk_eq_pkF, hlen e (hEL e (by simp))]
        show Nq e.1.1 ms * pkF 96 _ 12 + _ = _
        rw [pkF_mul, pkF_add]
        simp
    exact this EL (fun e he => he)
  -- the lanes
  have hlane : ∀ i < 12, lane 96 (accS (itab ms) MQ6) i
      = (EL.map fun e => Nq e.1.1 ms * (lanesOf e.2.1).getD i 0).sum := by
    intro i hi
    rw [hacc, lane_pkF _ hi]
    intro k hk
    calc (EL.map fun e => Nq e.1.1 ms * (lanesOf e.2.1).getD k 0).sum
        ≤ (EL.map fun e => 262144 * (lanesOf e.2.1).getD k 0).sum := by
          apply List.sum_le_sum
          intro e he
          exact Nat.mul_le_mul_right _ (Nq_le ms (foT_EL e he))
      _ = (EL.map fun e => (lanesOf e.2.1).getD k 0).sum * 262144 := by
          rw [mul_comm, List.sum_map_mul_left]
      _ < 2 ^ 96 := lane_bound k hk
  rw [hlane d (by omega), hlane (6 + d) (by omega)]
  -- the functional of the counts, partition by partition
  have hF : (FUN.getD d []).length = 32 := by
    rw [List.getD_eq_getElem _ _ (by rw [fun_len.1]; exact hd)]; exact fun_len.2 _ (List.getElem_mem _)
  rw [Finset.sum_congr rfl (fun o _ => by rw [cntO_eq_mqc ms o.2]), ]
  simp only [Nat.cast_list_sum, List.map_map]
  rw [sum_map_sub_int]
  simp only [Function.comp_apply]
  have : ∀ e ∈ EL, ((Nq e.1.1 ms * (lanesOf e.2.1).getD d 0 : ℕ) : ℤ)
      - ((Nq e.1.1 ms * (lanesOf e.2.1).getD (6 + d) 0 : ℕ) : ℤ)
      = ∑ o : Fin 32, mqc o e.2.1 * (Nq e.1.1 ms : ℤ) * ((FUN.getD d []).getD o 0 : ℕ) := by
    intro e he
    have h1 := (hent e he).2.1
    have h2 := (hent e he).2.2.1
    have g1 : (lanesOf e.2.1).getD d 0 = dotZ e.2.1.1 (FUN.getD d []) - dotZ e.2.1.2 (FUN.getD d []) := by
      unfold lanesOf
      rw [List.getD_append _ _ _ _ (by simp [fun_len.1]; exact hd), List.getD_eq_getElem _ _
        (by simp [fun_len.1]; exact hd), List.getElem_map, List.getD_eq_getElem _ _
        (by rw [fun_len.1]; exact hd)]
    have g2 : (lanesOf e.2.1).getD (6 + d) 0 = dotZ e.2.1.2 (FUN.getD d []) - dotZ e.2.1.1 (FUN.getD d []) := by
      unfold lanesOf
      rw [List.getD_append_right _ _ _ _ (by simp [fun_len.1]), List.getD_eq_getElem _ _
        (by simp [fun_len.1]; omega)]
      simp only [List.getElem_map, List.length_map, fun_len.1, show 6 + d - 6 = d by omega]
      rw [List.getD_eq_getElem _ _ (by rw [fun_len.1]; exact hd)]
    rw [g1, g2]
    have e1 : (((dotZ e.2.1.1 (FUN.getD d []) - dotZ e.2.1.2 (FUN.getD d []) : ℕ) : ℤ)
        - ((dotZ e.2.1.2 (FUN.getD d []) - dotZ e.2.1.1 (FUN.getD d []) : ℕ) : ℤ))
        = (dotZ e.2.1.1 (FUN.getD d []) : ℤ) - dotZ e.2.1.2 (FUN.getD d []) := by omega
    push_cast [Nat.cast_mul]
    rw [← mul_sub, e1, dotZ_eq _ _ h1 hF, dotZ_eq _ _ h2 hF]
    push_cast
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    unfold mqc
    ring
  rw [List.map_congr_left (fun e he => this e he)]
  -- swap the sums
  have swap : ∀ E : List ((T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))),
      (E.map fun e => ∑ o : Fin 32, mqc o e.2.1 * (Nq e.1.1 ms : ℤ) * ((FUN.getD d []).getD o 0 : ℕ)).sum
        = ∑ o : Fin 32, (E.map fun e => mqc o e.2.1 * (Nq e.1.1 ms : ℤ)).sum
          * ((FUN.getD d []).getD o 0 : ℕ) := by
    intro E
    induction E with
    | nil => simp
    | cons e E ih =>
      rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun o _ => ?_
      simp only [List.map_cons, List.sum_cons]
      ring
  exact swap EL

end GridGen.Six
