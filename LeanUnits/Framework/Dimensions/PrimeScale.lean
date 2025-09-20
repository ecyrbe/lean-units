import Batteries.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanUnits.Framework.Utils

namespace Units.Dimension.PrimeScale
/--
encode_string map different strings to different natural numbers
-/
def string_to_nat (s : String) : Nat :=
  (s.toList).foldl (fun h c => h * (UInt32.size+1) + (c.toNat + 1)) 0

def digits (n : Nat) : List Nat :=
  let B := UInt32.size + 1
  if n = 0 then [] else digits (n / B) ++ [n % B]
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

-- proof that different strings are mapped to different natural numbers
theorem string_to_nat_inj : Function.Injective string_to_nat := by
  intro s1 s2 h
  let B : Nat := UInt32.size + 1
  let dig (c : Char) : Nat := c.toNat + 1
  let encList (cs : List Char) : Nat := cs.foldl (fun h c => h * B + dig c) 0
  have encode_eq (s : String) : string_to_nat s = encList s.toList := by rfl
  have base_pos : 0 < B := by decide
  have dig_lt_base (c : Char) : dig c < B := Nat.succ_lt_succ (UInt32.toNat_lt c.val)
  have enc_append (cs : List Char) (c : Char) :
      encList (cs ++ [c]) = encList cs * B + dig c := by
    simp [encList, List.foldl_append, B, dig]
  have mod_of_qmul_add {q r : Nat} (hr : r < B) : (q * B + r) % B = r := by
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hr, zero_add, Nat.mod_eq_of_lt hr]
  have div_of_qmul_add {q r : Nat} (hr : r < B) : ( q * B + r) / B = q := by
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


noncomputable def prime_from_str (s : String) : Nat :=
  Nat.nth Nat.Prime (string_to_nat s)

theorem prime_from_str_prime (s : String) : (prime_from_str s).Prime := by
  simp only [prime_from_str, Nat.prime_nth_prime]

theorem prime_from_str_inj : Function.Injective prime_from_str := by
  exact Function.Injective.comp (Nat.nth_injective Nat.infinite_setOf_prime) string_to_nat_inj

theorem prime_from_str_ne_zero (s : String) : prime_from_str s ≠ 0 := by
  exact Nat.Prime.ne_zero (prime_from_str_prime s)

noncomputable def prime_pow (s : String) (q : ℚ) : ℝ :=
  (prime_from_str s : ℝ ) ^ (q: ℝ)

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

end Units.Dimension.PrimeScale
