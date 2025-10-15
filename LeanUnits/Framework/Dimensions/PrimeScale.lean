import Batteries.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanUnits.Framework.Utils
import LeanUnits.Framework.Dimensions.Prime

namespace Units.Dimension.PrimeScale
/--
Encode a string to ℕ
Making sure the encoding is injective.
-/
def string_to_nat (s : String) : ℕ :=
  (s.toList).foldl (fun h c => h * (UInt32.size+1) + (c.toNat + 1)) 0

/--
Helper function to get the digits of a natural number in base 2^32.
-/
def digits (n : ℕ) : List ℕ :=
  let B := UInt32.size + 1
  if n = 0 then [] else digits (n / B) ++ [n % B]
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

theorem string_to_nat_inj : Function.Injective string_to_nat := by
  intro s1 s2 h
  let B : ℕ := UInt32.size + 1
  let dig (c : Char) : ℕ := c.toNat + 1
  let encList (cs : List Char) : ℕ := cs.foldl (fun h c => h * B + dig c) 0
  have encode_eq (s : String) : string_to_nat s = encList s.toList := by rfl
  have base_pos : 0 < B := by decide
  have dig_lt_base (c : Char) : dig c < B := Nat.succ_lt_succ (UInt32.toNat_lt c.val)
  have enc_append (cs : List Char) (c : Char) :
      encList (cs ++ [c]) = encList cs * B + dig c := by
    simp [encList, List.foldl_append, B, dig]
  have mod_of_qmul_add {q r : ℕ} (hr : r < B) : (q * B + r) % B = r := by
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hr, zero_add, Nat.mod_eq_of_lt hr]
  have div_of_qmul_add {q r : ℕ} (hr : r < B) : ( q * B + r) / B = q := by
    rw [mul_comm, Nat.mul_add_div base_pos q r, Nat.div_eq_of_lt hr, add_zero]
  -- The digits we decode from an encoded list cs are exactly the mapped digits
  have digits_enc (cs : List Char) : digits (encList cs) = cs.map dig := by
    refine List.reverseRecOn cs ?_ ?_
    · simp [encList, digits]
    · intro cs c ih
      have hc : dig c < B := dig_lt_base c
      simp [digits, ih, enc_append, mod_of_qmul_add hc, div_of_qmul_add hc,
        List.map_append, B, dig]
  have dig_inj : Function.Injective dig := by
    intro a b h
    rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b, Nat.add_right_cancel h]
  -- Now we can decode both side images back to character lists and conclude equality
  have hdigits : digits (string_to_nat s1) = digits (string_to_nat s2) := by rw [h]
  have hmap s : digits (string_to_nat s) = s.toList.map dig := by rw [encode_eq,
    String.toList, digits_enc]
  have hmaps : s1.toList.map dig = s2.toList.map dig := hdigits.trans (hmap s2) ▸ (hmap s1).symm
  have h_list : s1.toList = s2.toList := List.map_injective_iff.mpr dig_inj hmaps
  exact String.ext h_list -- abuse of definitional equality

/--
Get the next Nat.Primes after n.
-/
def next_prime (n : ℕ) : Nat.Primes :=
  let prime := Nat.find (Nat.exists_infinite_primes n)
  have hprime : Nat.Prime prime := (Nat.find_spec (Nat.exists_infinite_primes n)).2
  ⟨prime, hprime⟩

theorem next_prime_gt (n : ℕ) : n ≤ (next_prime n).1 := by
  exact (Nat.find_spec (Nat.exists_infinite_primes n)).1

/--
Get the n-th Nat.Primes (0-indexed).
For example, nth_prime 0 = 2, nth_prime 1 = 3, nth_prime 2 = 5, etc.
-/
def nth_prime (n : ℕ) (nth : Nat.Primes := ⟨2, Nat.prime_two⟩) : Nat.Primes :=
  if n == 0 then
    nth
  else
    nth_prime (n - 1) (next_prime (nth+1))
termination_by n
decreasing_by
  refine Nat.sub_one_lt ?_
  rename_i h
  rw [beq_iff_eq] at h
  assumption

/--
Get the n-th Nat prime number (0-indexed).
For example, nth_prime 0 = 2, nth_prime 1 = 3, nth_prime 2 = 5, etc.
-/
def nth_prime_nat (n : ℕ) : ℕ := nth_prime n

theorem nth_prime_nat_prime (n : ℕ) : (nth_prime_nat n).Prime := by
  exact (nth_prime n).2

theorem nth_prime_strictmono : StrictMono nth_prime_nat := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold nth_prime_nat
  generalize s : (⟨2, Nat.prime_two⟩ : Nat.Primes) = start
  have hstep : ∀ k (p : Nat.Primes), (nth_prime k p).1 < (nth_prime (k+1) p).1 := by
    intro k p
    induction k generalizing p with
    | zero =>
        have hlt : p < (next_prime (p + 1)).1 :=
          lt_of_lt_of_le (Nat.lt_succ_self p) (next_prime_gt (p + 1))
        simpa [nth_prime] using hlt
    | succ k ih =>
        rw (occs:=[2]) [nth_prime]
        rw [nth_prime]
        exact ih (next_prime ((p : Nat) + 1))
  exact hstep n start

theorem nth_prime_nat_inj : Function.Injective nth_prime_nat :=
  nth_prime_strictmono.injective

/--
Get the prime number associated to a string.
This allows us to assign a unique prime number to each base dimension represented by a string.
We use it to construct the PrimeScale of a dimension.
-/
def prime_from_str (s : String) : ℕ :=
  nth_prime_nat (string_to_nat s)

-- uncomment to see the prime numbers assigned to the base dimensions
-- #eval prime_from_str "L" -- 397
-- theorem L_397 : prime_from_str "L" = 397 := by decide +native
-- #eval prime_from_str "T" -- 443
-- theorem T_443 : prime_from_str "T" = 443 := by decide +native
-- #eval prime_from_str "M" -- 401
-- theorem M_401 : prime_from_str "M" = 401 := by decide +native
-- #eval prime_from_str "I" -- 379
-- theorem I_379 : prime_from_str "I" = 379 := by decide +native
-- #eval prime_from_str "K" -- 389
-- theorem K_389 : prime_from_str "K" = 389 := by decide +native
-- #eval prime_from_str "N" -- 409
-- theorem N_409 : prime_from_str "N" = 409 := by decide +native
-- #eval prime_from_str "J" -- 383
-- theorem J_383 : prime_from_str "J" = 383 := by decide +native

theorem prime_from_str_prime (s : String) : (prime_from_str s).Prime := by
  apply nth_prime_nat_prime

theorem prime_from_str_inj : Function.Injective prime_from_str := by
  exact Function.Injective.comp nth_prime_nat_inj string_to_nat_inj

theorem prime_from_str_ne_zero (s : String) : prime_from_str s ≠ 0 := by
  exact Nat.Prime.ne_zero (prime_from_str_prime s)

theorem prime_from_str_pos (s : String) : 0 < prime_from_str s := by
  exact Nat.Prime.pos (prime_from_str_prime s)

theorem one_le_prime_from_str (s : String) : 1 ≤ prime_from_str s := by
  exact Nat.Prime.one_le (prime_from_str_prime s)

/--
Compute the prime expnentiation for a given string and rational number.
It's used to compute the PrimeScale of a dimension.
-/
noncomputable def prime_pow (s : String) (q : ℚ) : ℝ :=
  (prime_from_str s : ℝ ) ^ (q: ℝ)

/--
prime_pow injective if q≠0
-/
theorem prime_pow_inj_left (s1 s2 : String) (q : ℚ) (h : q ≠ 0) :
  prime_pow s1 q = prime_pow s2 q ↔ s1 = s2 := by
  constructor
  · intro hpow
    have hqR : (q : ℝ) ≠ 0 := by norm_cast
    have hReals : (prime_from_str s1 : ℝ) = (prime_from_str s2 : ℝ) := by
      calc
      (prime_from_str s1 : ℝ) = (prime_from_str s1 : ℝ) ^ 1 := by simp only [pow_one]
      _ = (prime_from_str s1 : ℝ) ^ ((q : ℝ) * (q : ℝ)⁻¹) := by simp [mul_inv_cancel₀ hqR]
      _ = ((prime_from_str s1 : ℝ) ^ (q : ℝ)) ^ ((q : ℝ)⁻¹) := by simp [Real.rpow_mul]
      _ = ((prime_from_str s2 : ℝ) ^ (q : ℝ)) ^ ((q : ℝ)⁻¹) := by
          simpa [prime_pow] using congrArg (fun x => x ^ ((q : ℝ)⁻¹)) hpow
      _ = (prime_from_str s2 : ℝ) ^ ((q : ℝ) * (q : ℝ)⁻¹) := by simp [Real.rpow_mul]
      _ = (prime_from_str s2 : ℝ) ^ 1 := by simp [mul_inv_cancel₀ hqR]
      _ = (prime_from_str s2 : ℝ) := by simp only [pow_one]
    have hNat : prime_from_str s1 = prime_from_str s2 := Nat.cast_injective hReals
    exact prime_from_str_inj hNat
  · intro hs
    rw [hs]

/--
For a fixed base (prime_from_str s : ℝ) > 1, the map q ↦ prime_pow s q is injective on ℚ.
-/
theorem prime_pow_inj_right (s : String) (q1 q2 : ℚ) :
  prime_pow s q1 = prime_pow s q2 ↔ q1 = q2 := by
  constructor
  · intro hpow
    have hp_pos : 0 < (prime_from_str s : ℝ) := by
      have : 0 < prime_from_str s := Nat.pos_of_ne_zero (prime_from_str_ne_zero s)
      norm_cast
    have hp_ne1 : (prime_from_str s : ℝ) ≠ 1 := by
      have : (1 : ℕ) < prime_from_str s := Nat.Prime.one_lt (prime_from_str_prime s)
      have : (1 : ℝ) < (prime_from_str s : ℝ) := by norm_cast
      exact ne_of_gt this
    have hlog_ne : Real.log (prime_from_str s : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hp_pos hp_ne1
    have hlog := congrArg Real.log hpow
    have hqR :
        (q1 : ℝ) * Real.log (prime_from_str s : ℝ)
      = (q2 : ℝ) * Real.log (prime_from_str s : ℝ) := by
      simpa [prime_pow, Real.log_rpow hp_pos] using hlog
    have hq' : (q1 : ℝ) = (q2 : ℝ) := (mul_right_cancel₀ hlog_ne) hqR
    exact_mod_cast hq'
  · intro hq; simp [hq]

theorem prime_pow_inj_nat (s1 s2 : String) {n1 n2 : ℕ} (h1 : n1 ≠ 0) (h2 : n2 ≠ 0) :
    prime_pow s1 n1 = prime_pow s2 n2 ↔ s1 = s2 ∧ n1 = n2 := by
  constructor
  · intro H
    set q1' := (n1-1) with hq1'
    set q2' := (n2-1) with hq2'
    -- using h and h' behind grind
    have hq1 : n1 = q1' + 1 := by grind only [cases Or]
    have hq2 : n2 = q2' + 1 := by grind only [cases Or]
    rw [hq1, hq2,] at H
    have H' : prime_from_str s1 ^ (q1' + 1) = prime_from_str s2 ^ (q2' + 1) := by
      unfold prime_pow at H
      have hq1': (((q1' + 1: ℕ): ℚ): ℝ) = ((q1' + 1:ℕ): ℝ) := by norm_cast
      have hq2': (((q2' + 1: ℕ): ℚ): ℝ) = ((q2' + 1:ℕ): ℝ) := by norm_cast
      rw [hq1', hq2',Real.rpow_natCast,Real.rpow_natCast] at H
      exact_mod_cast H
    have := Nat.Prime.pow_inj (prime_from_str_prime s1) (prime_from_str_prime s2) H'
    exact this.imp (fun h => prime_from_str_inj h) (fun h => by rw [hq1, hq2, h])
  · intro h; rw [h.1, h.2]

theorem prime_pow_inj_int (s1 s2 : String) {z1 z2 : ℤ} (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) :
  prime_pow s1 z1 = prime_pow s2 z2 ↔ s1 = s2 ∧ z1 = z2 := by
  constructor
  · cases z1 with
    | ofNat n1 =>
      cases z2 with
      | ofNat n2 =>
        have h1 : n1 ≠ 0 := by
          intro hn; rw [hn] at h1; contradiction
        have h2 : n2 ≠ 0 := by
          intro hn; rw [hn] at h2; contradiction
        have H := (prime_pow_inj_nat s1 s2 h1 h2).mp
        have hp1 : prime_pow s1 ↑n1 = prime_pow s1 ↑(Int.ofNat n1) := by rfl
        have hp2 : prime_pow s2 ↑n2 = prime_pow s2 ↑(Int.ofNat n2) := by rfl
        rw [hp1, hp2] at H
        intro hEq
        have ⟨hs, hnats⟩ := H hEq
        have hn : Int.ofNat n1 = Int.ofNat n2 := by rw [hnats]
        exact ⟨hs, hn⟩
      | negSucc n2 =>
        intro hEq
        -- prove not possible (left >1, right <1)
        exfalso
        have hp1 : 0 < prime_from_str s1 := Nat.pos_of_ne_zero (prime_from_str_ne_zero s1)
        have hp1R : 0 < (prime_from_str s1 : ℝ) := by norm_cast
        have hp1_gt1 : 1 < (prime_from_str s1 : ℝ) := by
          have : (1 : ℕ) < prime_from_str s1 := Nat.Prime.one_lt (prime_from_str_prime s1)
          norm_cast
        have hn1 : n1 ≠ 0 := by
          intro hn; rw [hn] at h1; contradiction
        have left_gt1 : 1 < prime_pow s1 ↑n1 := by
          rw [prime_pow]
          exact Real.one_lt_rpow hp1_gt1 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn1))
        have hp2 : 0 < prime_from_str s2 := Nat.pos_of_ne_zero (prime_from_str_ne_zero s2)
        have hp2R : 0 < (prime_from_str s2 : ℝ) := by norm_cast
        have hp2_gt1 : 1 < (prime_from_str s2 : ℝ) := by
          have : 1 < prime_from_str s2 := Nat.Prime.one_lt (prime_from_str_prime s2)
          norm_cast
        have right_lt1 : prime_pow s2 ↑(Int.negSucc n2) < 1 := by
          have : (((Int.negSucc n2): ℚ) : ℝ) = - (n2 + 1 : ℝ) := by norm_cast
          rw [prime_pow, this, Real.rpow_neg (le_of_lt hp2R)]
          -- show the positive power is > 1, hence its inverse is < 1
          have pow_pos : 0 < (prime_from_str s2 : ℝ) ^ (n2 + 1 : ℝ) := by positivity
          have pow_gt_one : 1 < (prime_from_str s2 : ℝ) ^ (n2 + 1 : ℝ) :=
            Real.one_lt_rpow hp2_gt1 (by norm_cast; exact Nat.zero_lt_succ n2)
          -- multiply 1 < x by x⁻¹ > 0 to get x⁻¹ < 1
          have h := mul_lt_mul_of_pos_left pow_gt_one (inv_pos_of_pos pow_pos)
          simp [mul_comm, mul_inv_cancel₀ (ne_of_gt pow_pos)] at h
          exact h
        have : (1 : ℝ) < 1 := left_gt1.trans (hEq.trans_lt right_lt1)
        exact lt_irrefl (1 : ℝ) this
    | negSucc n1 =>
      cases z2 with
      | ofNat n2 =>
        intro hEq
        -- prove not possible (left <1, right >1)
        exfalso
        have hp1 : 0 < prime_from_str s1 := Nat.pos_of_ne_zero (prime_from_str_ne_zero s1)
        have hp1R : 0 < (prime_from_str s1 : ℝ) := by norm_cast
        have hp1_gt1 : 1 < (prime_from_str s1 : ℝ) := by
          have : (1 : ℕ) < prime_from_str s1 := Nat.Prime.one_lt (prime_from_str_prime s1)
          norm_cast
        -- left side has negative exponent, hence < 1
        have left_lt1 : prime_pow s1 ↑(Int.negSucc n1) < 1 := by
          have : (((Int.negSucc n1): ℚ) : ℝ) = - (n1 + 1 : ℝ) := by norm_cast
          rw [prime_pow, this, Real.rpow_neg (le_of_lt hp1R)]
          -- show the positive power is > 1, hence its inverse is < 1
          have pow_pos : 0 < (prime_from_str s1 : ℝ) ^ (n1 + 1 : ℝ) :=
            Real.rpow_pos_of_pos hp1R (n1 + 1 : ℝ)
          have pow_gt_one : 1 < (prime_from_str s1 : ℝ) ^ (n1 + 1 : ℝ) :=
            Real.one_lt_rpow hp1_gt1 (by norm_cast; exact Nat.zero_lt_succ n1)
          -- multiply 1 < x by x⁻¹ > 0 to get x⁻¹ < 1
          have h := mul_lt_mul_of_pos_left pow_gt_one (inv_pos_of_pos pow_pos)
          simp [mul_comm, mul_inv_cancel₀ (ne_of_gt pow_pos)] at h
          exact h
        -- right side has positive exponent (and base > 1), hence > 1
        have hp2_gt1 : 1 < (prime_from_str s2 : ℝ) := by
          have : (1 : ℕ) < prime_from_str s2 := Nat.Prime.one_lt (prime_from_str_prime s2)
          norm_cast
        have hn2 : n2 ≠ 0 := by
          intro hn; rw [hn] at h2; contradiction
        have right_gt1 : 1 < prime_pow s2 ↑n2 := by
          rw [prime_pow]
          exact Real.one_lt_rpow hp2_gt1 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn2))
        -- contradiction: 1 < RHS = LHS < 1
        have : (1 : ℝ) < 1 := by
          have h1 : (1 : ℝ) < prime_pow s1 ↑(Int.negSucc n1) := by
            simpa using (lt_of_lt_of_eq right_gt1 hEq.symm)
          exact lt_trans h1 left_lt1
        exact lt_irrefl (1 : ℝ) this
      | negSucc n2 =>
        intro hEq
        have hq1 : ((Int.negSucc n1 : ℚ)) = -((n1 + 1 : ℕ) : ℚ) := by norm_cast
        have hq2 : ((Int.negSucc n2 : ℚ)) = -((n2 + 1 : ℕ) : ℚ) := by norm_cast
        have hs1_ne_zero := prime_from_str_ne_zero s1
        have hs2_ne_zero := prime_from_str_ne_zero s2
        have hEqQ :
          prime_pow s1 (-(n1 + 1 : ℚ)) = prime_pow s2 (-(n2 + 1 : ℚ)) := by
          simpa [hq1, hq2] using hEq
        have hInv :
          (prime_pow s1 (n1 + 1 : ℚ))⁻¹ = (prime_pow s2 (n2 + 1 : ℚ))⁻¹ := by
          have hp1nonneg : 0 ≤ (prime_from_str s1 : ℝ) := by positivity
          have hp2nonneg : 0 ≤ (prime_from_str s2 : ℝ) := by positivity
          have h1 : (((-(n1 + 1) : ℚ)) : ℝ) = -((n1 + 1 : ℚ) : ℝ) := by norm_cast
          have h2 : (((-(n2 + 1) : ℚ)) : ℝ) = -((n2 + 1 : ℚ) : ℝ) := by norm_cast
          rw [prime_pow, prime_pow, h1, h2,
            Real.rpow_neg hp1nonneg, Real.rpow_neg hp2nonneg] at hEqQ
          simpa [prime_pow] using hEqQ
        have hPos : prime_pow s1 (n1 + 1:ℕ) = prime_pow s2 (n2 + 1:ℕ) := by
          simpa [inv_inv] using congrArg (fun x : ℝ => x⁻¹) hInv
        have h1 : n1 + 1 ≠ 0 := Nat.succ_ne_zero n1
        have h2 : n2 + 1 ≠ 0 := Nat.succ_ne_zero n2
        have ⟨hs, hnats⟩ :=
          (prime_pow_inj_nat s1 s2 (Nat.succ_ne_zero n1) (Nat.succ_ne_zero n2)).mp hPos
        have hn: Int.negSucc n1 = Int.negSucc n2 := by
          rw [Nat.succ_injective hnats]
        exact ⟨hs, hn⟩
  · intro h; rw [h.1, h.2]

theorem prime_pow_inj (s1 s2 : String) {q1 q2 : ℚ} (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) :
  prime_pow s1 q1 = prime_pow s2 q2 ↔ s1 = s2 ∧ q1 = q2 := by
  constructor
  · intro hEq
    -- Let m be the multiplication of denominators
    let d1 : ℕ := q1.den
    let d2 : ℕ := q2.den
    have hd1_pos : 0 < d1 := Rat.den_pos q1
    have hd2_pos : 0 < d2 := Rat.den_pos q2
    set m := d1 * d2 with hm
    have hm_pos : 0 < m := by positivity
    have hm_ne_zeroQ : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm_pos)

    -- Raise both sides to the natural power m
    have hPow := congrArg (fun x : ℝ => x ^ m) hEq
    -- (x^a)^m = x^(a*m)
    have hMul : prime_pow s1 (q1 * (m : ℚ)) = prime_pow s2 (q2 * (m : ℚ)) := by
      simpa [prime_pow, Real.rpow_mul] using hPow
    -- Write the integer exponents explicitly
    set z1 : ℤ := q1.num * d2 with hz1
    set z2 : ℤ := q2.num * d1 with hz2

    -- Show q1 * m = z1 and q2 * m = z2 as rationals
    have hq1m_int : (q1 * (m : ℚ)) = (z1 : ℚ) := by
      -- q1 = q1.num / q1.den and m = d1*k1
      have hm : (m : ℚ) = (d1 * d2 : ℕ) := by rw [hm]
      -- Use q1.num_div_den : (q1.num : ℚ) / q1.den = q1
      have hnumden : ((q1.num : ℚ) / q1.den) = q1 := by
        simpa using (Rat.num_div_den q1)
      calc
        q1 * (m : ℚ)
            = ((q1.num : ℚ) / q1.den) * (d1 * d2 : ℕ) := by simp [hnumden, hm, d1]
        _ = ((q1.num : ℚ) * ((q1.den : ℚ)⁻¹)) * (d1 * d2 : ℕ) := by
              simp [div_eq_mul_inv]
        _ = (q1.num : ℚ) * (((q1.den : ℚ)⁻¹) * (d1 * d2 : ℕ)) := by ring
        _ = (q1.num : ℚ) * ((q1.den : ℚ)⁻¹ * d1) * d2 := by
              simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
        _ = (q1.num : ℚ) * 1 * d2 := by
              have hden_cancel : (q1.den: ℚ)⁻¹ * (d1:ℚ) = 1 := by simp [d1]
              simp [hden_cancel]
        _ = (q1.num : ℚ) * d2 := by simp
        _ = (z1 : ℚ) := by simp [hz1, Int.cast_mul]

    have hq2m_int : (q2 * (m : ℚ)) = (z2 : ℚ) := by
      have hm : (m : ℚ) = (d2 * d1 : ℕ) := by rw [mul_comm, hm]
      have hnumden : ((q2.num : ℚ) / q2.den) = q2 := by
        simpa using (Rat.num_div_den q2)
      calc
        q2 * (m : ℚ)
            = ((q2.num : ℚ) / q2.den) * (d2 * d1 : ℕ) := by simp [hnumden, hm, d2]
        _ = ((q2.num : ℚ) * ((q2.den : ℚ)⁻¹)) * (d2 * d1 : ℕ) := by
              simp [div_eq_mul_inv]
        _ = (q2.num : ℚ) * (((q2.den : ℚ)⁻¹) * (d2 * d1 : ℕ)) := by ring
        _ = (q2.num : ℚ) * ((q2.den : ℚ)⁻¹ * d2) * d1 := by
              simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
        _ = (q2.num : ℚ) * 1 * d1 := by
              have hden_cancel : ((q2.den : ℚ)⁻¹) * (d2 : ℚ) = 1 := by simp [d2]
              simp [hden_cancel]
        _ = (q2.num : ℚ) * d1 := by simp
        _ = (z2 : ℚ) := by simp [hz2, Int.cast_mul]

    -- Replace the rational exponents by the integer ones
    have hInt : prime_pow s1 z1 = prime_pow s2 z2 := by
      simpa [hq1m_int, hq2m_int] using hMul

    -- q1*m ≠ 0 and q2*m ≠ 0 ⇒ z1 ≠ 0 and z2 ≠ 0
    have hz1_ne : z1 ≠ 0 := by
      have : (q1 * (m : ℚ)) ≠ 0 := mul_ne_zero h1 hm_ne_zeroQ
      exact_mod_cast (by
        simpa [hq1m_int] using this)
    have hz2_ne : z2 ≠ 0 := by
      have : (q2 * (m : ℚ)) ≠ 0 := mul_ne_zero h2 hm_ne_zeroQ
      exact_mod_cast (by
        simpa [hq2m_int] using this)
    have ⟨hs, hz⟩ := (prime_pow_inj_int s1 s2 hz1_ne hz2_ne).mp hInt
    have hqm : q1 * (m : ℚ) = q2 * (m : ℚ) := by simp [hq1m_int, hq2m_int, hz]
    have hq : q1 = q2 := by exact (mul_right_cancel₀ hm_ne_zeroQ) hqm
    exact ⟨hs, hq⟩
  · intro h; rw [h.1, h.2]

theorem prime_pow_zero {s : String}
  : prime_pow s 0 = 1 := by
  have q_cast : ((0: ℚ) : ℝ) = ((0: ℕ): ℝ) := by norm_cast
  rw [prime_pow, q_cast, Real.rpow_natCast, pow_zero]

theorem prime_pow_add {s : String} (q1 q2 : ℚ) :
      prime_pow s (q1 + q2) = prime_pow s q1 * prime_pow s q2 := by
  have q_cast : ((q1 + q2: ℚ): ℝ) = (q1: ℝ) + (q2: ℝ) := by norm_cast
  have h := prime_from_str_ne_zero s
  repeat rw [prime_pow]
  rw [q_cast, Real.rpow_add]
  positivity

theorem prime_pow_neg {i : String} (q : ℚ) :
  prime_pow i (-q) = (prime_pow i q)⁻¹ := by
  have q_cast : ((-q: ℚ): ℝ) = -(q: ℝ) := by norm_cast
  rw [prime_pow, prime_pow, q_cast, Real.rpow_neg]
  positivity

theorem prime_pow_ne_zero {s : String} (q : ℚ) : prime_pow s q ≠ 0 := by
  have hxNat : 0 < prime_from_str s := Nat.pos_of_ne_zero (prime_from_str_ne_zero s)
  have hx : 0 < (prime_from_str s : ℝ) := by norm_cast
  rw [prime_pow]
  exact ne_of_gt (Real.rpow_pos_of_pos hx (q : ℝ))

theorem one_le_prime_pow {s : String} {q : ℚ} (hq : 0 ≤ q) :
  1 ≤ prime_pow s q := by
  have hx : 1 ≤ (prime_from_str s : ℝ) := by exact_mod_cast one_le_prime_from_str s
  apply Real.one_le_rpow hx
  norm_cast

theorem prime_pow_le_one {s : String} {q : ℚ} (hq : q ≤ 0) :
  prime_pow s q ≤ 1 := by
  have hx : 1 ≤ (prime_from_str s : ℝ) := by exact_mod_cast one_le_prime_from_str s
  apply Real.rpow_le_one_of_one_le_of_nonpos hx
  norm_cast

theorem prime_pow_pos {s : String} {q : ℚ} :
  0 < prime_pow s q := by
  have hx : 0 < (prime_from_str s : ℝ) := by exact_mod_cast prime_from_str_pos s
  apply Real.rpow_pos_of_pos hx

theorem prime_pow_eq_one {s : String} {q : ℚ} (hq : q = 0) :
  prime_pow s q = 1 := by rw [hq, prime_pow_zero]

theorem prime_pow_ne_one {s : String} {q : ℚ} (hq : q ≠ 0) :
  prime_pow s q ≠ 1 := by
  by_contra h
  rw [(@prime_pow_zero s).symm] at h
  have hq' := (prime_pow_inj_right s q 0).mp h
  contradiction

theorem prime_pow_eq_one_iff {s : String} {q : ℚ} :
  prime_pow s q = 1 ↔ q = 0 := by
  constructor
  · intro h
    by_contra hq
    have h1 := @prime_pow_ne_one s q hq
    contradiction
  · exact prime_pow_eq_one

theorem prime_pow_mul_prime_pow_eq_one_iff {s1 s2 : String} {q1 q2 : ℚ} :
  prime_pow s1 q1 * prime_pow s2 q2 = 1 ↔ (s1 = s2 ∧ q1 = -q2) ∨ (q1 = 0 ∧ q2 = 0) := by
  constructor
  · intro h
    by_cases hq1 : q1 = 0
    · right
      exact ⟨hq1, (prime_pow_eq_one_iff.mp (by rw [hq1, prime_pow_zero] at h; simpa using h))⟩
    by_cases hq2 : q2 = 0
    · right
      exact ⟨(prime_pow_eq_one_iff.mp (by rw [hq2, prime_pow_zero] at h; simpa using h)), hq2⟩
    left
    have hInv : prime_pow s1 q1 = (prime_pow s2 q2)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hNeg : prime_pow s1 q1 = prime_pow s2 (-q2) := by
      rw [←prime_pow_neg] at hInv; exact hInv
    replace hq2 : -q2 ≠ 0 := by exact neg_ne_zero.mpr hq2
    exact (prime_pow_inj s1 s2 hq1 hq2).mp hNeg
  · intro h
    cases h with
    | inl h =>
      obtain ⟨hs, hq⟩ := h
      rw [hs, hq, prime_pow_neg, inv_mul_cancel₀]
      apply prime_pow_ne_zero
    | inr h =>
      obtain ⟨hq1, hq2⟩ := h
      rw [hq1, hq2, prime_pow_zero, one_mul]
      exact prime_pow_zero

theorem diff_prime_pow_mul_prime_pow_eq_one_iff {s1 s2 : String} {q1 q2 : ℚ}
  (h : s1 ≠ s2) :
  prime_pow s1 q1 * prime_pow s2 q2 = 1 ↔ (q1 = 0 ∧ q2 = 0) := by
  constructor
  · intro hEq
    rcases (prime_pow_mul_prime_pow_eq_one_iff).mp hEq with ⟨hs, _⟩ | hzero
    · contradiction
    · exact hzero
  · intro ⟨hq1, hq2⟩
    simp only [hq1, hq2, prime_pow_zero, one_mul]

theorem prod_prime_pow_eq_one_iff
  (S : Finset String) (q : String → ℚ) :
  (∏ s ∈ S, prime_pow s (q s)) = 1 ↔ ∀ s ∈ S, q s = 0 := by
  unfold prime_pow
  have h_all_prime : ∀ s ∈ S, (prime_from_str s).Prime := by
    intro s hs; exact prime_from_str_prime s
  exact q_prod_prime_pow_eq_one_iff q h_all_prime prime_from_str_inj

end Units.Dimension.PrimeScale
