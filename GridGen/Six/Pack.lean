/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.PatCount
import GridGen.Six.ExCountData

/-!
# Height six: counts of colourings of masks, packed

The orbit counts of the proper colourings of six lists given by bit masks need, for every set
partition `q` of the rows, `N_q`: the product over the blocks of `q` of the sizes of the
intersections of their masks (`Nq`, `GridGen/Six/PatCount.lean`). Here:

* the intersections of the masks over all `63` sets of rows, by doubling (`atL`: the list for
  rows `< r + 1` is the list for rows `< r` followed by its intersections with mask `r`);
* their sizes, packed four bits each into one natural (`itab`, with `PT` for the sizes of
  bytes), so that `N_q` is a product of lanes (`nvq`, `nvq_eq`);
* the same computed by the kernel with primitive operations on packed naturals (`tabF`, `horF`,
  `tab_eq`, `hor_eq`, `nvqF`, `accS`).

Used by the uniform transfer (`GridGen/Six/Uniform.lean`) and the exact certificates
(`GridGen/Six/ExCount.lean`, `GridGen/Six/ExDefs.lean`).
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
      rw [this, ite_eq_right (by simp)]
    · have hlen := atL_length ms r
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; exact h1), hlen, getD_map_lt (by rw [hlen]; rw [pow_succ] at h; omega)]
      have h2 : S - 2 ^ r < 2 ^ r := by rw [pow_succ] at h; omega
      rw [atL_getD ms r _ h2, andR]
      have hS : S.testBit r = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have : S / 2 ^ r = 1 := by
          apply Nat.div_eq_of_lt_le <;> rw [pow_succ] at h <;> omega
        simp [this]
      rw [ite_eq_left hS]
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

/-! ### Primitive versions of the counting -/

/-- `pk 8` of `2^r` ones. -/
def ones8 : ℕ → ℕ
  | 0 => 1
  | 1 => 257
  | 2 => 16843009
  | 3 => 72340172838076673
  | 4 => 1334440654591915542993625911497130241
  | _ => 454086624460063511464984254936031011189294057512315937409637584344757371137

theorem ones8_eq : ∀ r < 6, ones8 r = pk 8 (List.replicate (2 ^ r) 1) := by decide +kernel

/-- One doubling step, primitive. -/
def dblF (T m r : ℕ) : ℕ :=
  Nat.add T (Nat.mul (Nat.pow 2 (Nat.mul 8 (Nat.pow 2 r))) (Nat.land T (Nat.mul m (ones8 r))))

theorem dblF_eq {r : ℕ} (hr : r < 6) (T m : ℕ) : dblF T m r = dblT T m r := by
  unfold dblF dblT; rw [ones8_eq r hr]

/-- Byte `i`. -/
def lane8 (x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 8 i)) 255

theorem lane8_eq (x i : ℕ) : lane8 x i = lane 8 x i := by
  unfold lane8 lane
  rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num]
  rw [show Nat.land (Nat.shiftRight x (Nat.mul 8 i)) (2 ^ 8 - 1)
      = (x >>> (8 * i)) &&& (2 ^ 8 - 1) from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

/-- The packed sizes from the packed intersections, in Horner form from byte `S`. -/
def horF (T : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | S, n + 1 => Nat.add (lane4 PT (lane8 T S)) (Nat.mul 16 (horF T (S + 1) n))

theorem horF_eq (T : ℕ) : ∀ n S, horF T S n = pkF 4 (fun i => lane 4 PT (lane 8 T (S + i))) n
  | 0, _ => rfl
  | n + 1, S => by
    rw [horF, pkF, horF_eq T n (S + 1), lane4_eq, lane8_eq]
    simp only [Nat.add_zero, show (2 : ℕ) ^ 4 = 16 by norm_num]
    congr 2
    exact pkF_congr fun i _ => by rw [show S + 1 + i = S + (i + 1) by ring]

/-- The packed intersections of six masks. -/
def tabF (m0 m1 m2 m3 m4 m5 : ℕ) (k : ℕ → Bool) : Bool :=
  xN (dblF 255 m0 0) fun t1 => xN (dblF t1 m1 1) fun t2 => xN (dblF t2 m2 2) fun t3 =>
  xN (dblF t3 m3 3) fun t4 => xN (dblF t4 m4 4) fun t5 => xN (dblF t5 m5 5) fun t6 => k t6

theorem tab_eq (ms : List ℕ) (hms : ∀ r, ms.getD r 0 < 256) :
    dblF (dblF (dblF (dblF (dblF (dblF 255 (ms.getD 0 0) 0) (ms.getD 1 0) 1) (ms.getD 2 0) 2)
      (ms.getD 3 0) 3) (ms.getD 4 0) 4) (ms.getD 5 0) 5 = pk 8 (atL ms 6) := by
  have h0 : (255 : ℕ) = pk 8 (atL ms 0) := by simp [atL, pk]
  have st : ∀ r < 6, dblF (pk 8 (atL ms r)) (ms.getD r 0) r = pk 8 (atL ms (r + 1)) :=
    fun r hr => by rw [dblF_eq hr, dblT_eq ms hms]
  rw [h0, st 0 (by norm_num), st 1 (by norm_num), st 2 (by norm_num), st 3 (by norm_num),
    st 4 (by norm_num), st 5 (by norm_num)]

theorem hor_eq (ms : List ℕ) : horF (pk 8 (atL ms 6)) 0 64 = itab ms := by
  have hlen : (atL ms 6).length = 64 := by rw [atL_length]; norm_num
  rw [horF_eq, itab, pk_eq_pkF 4, List.length_map, hlen]
  apply pkF_congr
  intro i hi
  rw [zero_add, getD_map_lt (by rw [hlen]; exact hi), pk_eq_pkF 8, lane_pkF _ (by rw [hlen]; exact hi)]
  intro k hk
  rw [hlen] at hk
  have := atL_lt ms 6 ((atL ms 6).getD k 0) (by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hk)]; exact List.getElem_mem _)
  norm_num; exact this

end GridGen.Six
