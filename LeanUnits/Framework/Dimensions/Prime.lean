import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Associated

theorem base_dvd_prod_exp
  {ι} [DecidableEq ι] {S : Finset ι} {sp} {f_base : ι → ℕ} {f_exp : ι → ℕ}
  (sp_in_S : sp ∈ S) (h_exp_pos : 0 < f_exp sp) :
  f_base sp ∣ ∏ s ∈ S, (f_base s) ^ (f_exp s) := by
  set prime_pow := fun s => (f_base s) ^ (f_exp s)
  -- The factor for sp appears in the product, hence its power divides the product.
  have h_factor_div :
      prime_pow sp ∣ ∏ s ∈ S, prime_pow s := by
      apply Finset.dvd_prod_of_mem (f:=prime_pow) sp_in_S
  have h_base_div_factor : f_base sp ∣ (f_base sp) ^ (f_exp sp) := by
    apply dvd_pow_self
    exact ne_of_gt h_exp_pos
  exact dvd_trans h_base_div_factor h_factor_div

theorem z_prod_prime_pow_eq_one_iff
  {ι} [DecidableEq ι] {S : Finset ι} (f_prime : ι → ℕ) (f_exp : ι → ℤ)
    (h_primes : ∀ s ∈ S, Nat.Prime (f_prime s))
    (h_f_prime_inj : Function.Injective f_prime) :
    ((∏ s ∈ S, (f_prime s : ℝ) ^ (f_exp s)) = 1) ↔ (∀ p ∈ S, f_exp p = 0) := by
constructor
· intro h_prod s hs
  let S_pos := S.filter (0 ≤ f_exp ·)
  let S_neg := S.filter (f_exp · < 0)
  have h_S_union : S = S_pos ∪ S_neg := by
    ext x
    by_cases h0 : 0 ≤ f_exp x <;> aesop
  set N := ∏ s ∈ S, (f_prime s : ℝ) ^ (f_exp s) with h_N_def
  let N_pos := ∏ s ∈ S_pos, (f_prime s: ℝ) ^ (f_exp s)
  let N_pos' := ∏ s ∈ S_pos, (f_prime s) ^ (f_exp s).toNat
  let N_neg := ∏ s ∈ S_neg, (f_prime s: ℝ) ^ (- f_exp s)
  let N_neg' := ∏ s ∈ S_neg, (f_prime s) ^ (- f_exp s).toNat
  set prime_pow := fun s => (f_prime s : ℝ) ^ (f_exp s)

  have h_pos_cast : N_pos = N_pos' := by
    -- pointwise nonnegativity for exponents of elements in S_pos
    have h_nonneg : ∀ s ∈ S_pos, 0 ≤ f_exp s := by
      intro s hs_pos
      rw [Finset.mem_filter] at hs_pos
      exact (And.right hs_pos)
    -- cast each nonnegative integer exponent
    have h_fn_cast : ∀ s ∈ S_pos, (f_exp s).toNat = f_exp s := by
      intro s hs_pos
      have hs_nonneg : 0 ≤ f_exp s := h_nonneg s hs_pos
      exact Int.toNat_of_nonneg hs_nonneg
      -- Rewrite each factor using h_fn_cast, then pull the casts out of the product.
    have h_each :
        ∀ s ∈ S_pos,
          (f_prime s : ℝ) ^ (f_exp s) =
            (((f_prime s) ^ (f_exp s).toNat : ℕ) : ℝ) := by
        intro s hs
        have hs_nonneg : 0 ≤ f_exp s := h_nonneg s hs
        have : f_exp s = (Int.toNat (f_exp s)) := (Int.toNat_of_nonneg hs_nonneg).symm
        rw (occs:=[1]) [this]
        norm_cast
    have h1 :
        ∏ s ∈ S_pos, (f_prime s : ℝ) ^ (f_exp s)
          = ∏ s ∈ S_pos, (((f_prime s) ^ (f_exp s).toNat : ℕ) : ℝ) := by
        refine Finset.prod_congr rfl ?_
        intro s hs
        exact h_each s hs
    have h2 :
        ∏ s ∈ S_pos, (((f_prime s) ^ (f_exp s).toNat : ℕ) : ℝ)
          = ((∏ s ∈ S_pos, (f_prime s) ^ (f_exp s).toNat : ℕ) : ℝ) := by
        norm_cast
    exact h1.trans h2

  have h_neg_cast : N_neg = N_neg' := by
    -- pointwise positivity for exponents of elements in S_neg
    have h_pos : ∀ s ∈ S_neg, 0 < - f_exp s := by
      intro s hs_neg
      rw [Finset.mem_filter] at hs_neg
      exact neg_pos.mpr hs_neg.right
    -- cast each positive integer exponent
    have h_fn_cast : ∀ s ∈ S_neg, (- f_exp s).toNat = - f_exp s := by
      intro s hs_neg
      have hs_pos : 0 < - f_exp s := h_pos s hs_neg
      exact Int.toNat_of_nonneg (le_of_lt hs_pos)
      -- Rewrite each factor using h_fn_cast, then pull the casts out of the product.
    have h_each :
        ∀ s ∈ S_neg,
          (f_prime s : ℝ) ^ (- f_exp s) =
            (((f_prime s) ^ (- f_exp s).toNat : ℕ) : ℝ) := by
        intro s hs
        have hs_pos : 0 < - f_exp s := h_pos s hs
        have : - f_exp s = (Int.toNat (- f_exp s)) := (Int.toNat_of_nonneg (le_of_lt hs_pos)).symm
        rw (occs:=[1]) [this]
        norm_cast
    have h1 :
        ∏ s ∈ S_neg, (f_prime s : ℝ) ^ (- f_exp s)
          = ∏ s ∈ S_neg, (((f_prime s) ^ (- f_exp s).toNat : ℕ) : ℝ) := by
        refine Finset.prod_congr rfl ?_
        intro s hs
        exact h_each s hs
    have h2 :
        ∏ s ∈ S_neg, (((f_prime s) ^ (- f_exp s).toNat : ℕ) : ℝ)
          = ((∏ s ∈ S_neg, (f_prime s) ^ (- f_exp s).toNat : ℕ) : ℝ) := by
        norm_cast
    exact h1.trans h2

  have h_dis : Disjoint S_pos S_neg := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha_pos ha_neg
    obtain ⟨_, ha_nonneg⟩ := Finset.mem_filter.mp ha_pos
    obtain ⟨_, ha_neg_lt⟩ := Finset.mem_filter.mp ha_neg
    exact (not_lt_of_ge ha_nonneg) ha_neg_lt

  have h_N_div : N = N_pos/ N_neg := by
    have h_prod_split : N = (∏ s ∈ S_pos, prime_pow s) * ∏ s ∈ S_neg, prime_pow s := by
      rw [← Finset.prod_union h_dis, ←h_S_union]
    -- Rewrite the product over S_neg using inverses
    have h_prod_neg :
      (∏ s ∈ S_neg, prime_pow s)
        = (∏ s ∈ S_neg, (f_prime s : ℝ) ^ (- f_exp s))⁻¹ := by
      -- Each factor with negative exponent becomes the inverse of the positive exponent
      have h_each :
        ∀ s ∈ S_neg,
      prime_pow s =
        ((f_prime s : ℝ) ^ (- f_exp s))⁻¹ := by
        intro s hs
        simp [prime_pow]
      have h_congr :
        (∏ s ∈ S_neg, prime_pow s)
      = ∏ s ∈ S_neg, ((f_prime s : ℝ) ^ (- f_exp s))⁻¹ := by
        refine Finset.prod_congr rfl ?_
        intro s hs
        simpa using h_each s hs
      have h_inv :
        (∏ s ∈ S_neg, ((f_prime s : ℝ) ^ (- f_exp s))⁻¹)
      = (∏ s ∈ S_neg, (f_prime s : ℝ) ^ (- f_exp s))⁻¹ := by
        simp
      exact h_congr.trans h_inv
    -- Assemble: N = N_pos * (N_neg)⁻¹ = N_pos / N_neg
    have : N = N_pos / N_neg := by
      simpa [N_pos, N_neg, h_prod_neg, div_eq_mul_inv] using h_prod_split
    exact this

  have n_neg_ne_zero: N_neg ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs_neg
    have hs_in_S : s ∈ S := (Finset.mem_filter.mp hs_neg).1
    have s_prime := h_primes s hs_in_S
    have h_base_ne_zero : (f_prime s : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.Prime.ne_zero s_prime)
    have h_pow_ne_zero :
      (f_prime s : ℝ) ^ (- f_exp s) ≠ 0 := by
      simpa using zpow_ne_zero (- f_exp s) h_base_ne_zero
    exact h_pow_ne_zero

  have h_eq : N_pos = N_neg := by
    have h_one : N_pos / N_neg = 1 := by rw [←h_N_div]; exact h_prod
    apply congr_arg (·* N_neg) at h_one
    field_simp at h_one
    exact h_one

  have h_eq' : N_pos' = N_neg' := by
    simpa [h_pos_cast, h_neg_cast] using h_eq

  rcases lt_trichotomy (f_exp s) 0 with h_neg | h_zero | h_pos
  · -- Case: f_exp s < 0
    have h_s_in_neg : s ∈ S_neg := by
      rw [Finset.mem_filter]
      exact ⟨hs, h_neg⟩
    have h_s_not_in_pos : s ∉ S_pos := by
      rw [Finset.mem_filter]
      intro h_con
      obtain ⟨_, h_nonneg⟩ := h_con
      exact not_lt_of_ge h_nonneg h_neg
    have h_s_dvd_Nneg : (f_prime s) ∣ N_neg' := by
      apply base_dvd_prod_exp h_s_in_neg (f_base:= f_prime) (f_exp:=fun n => (- f_exp n).toNat)
      simp only [Int.lt_toNat, CharP.cast_eq_zero, Int.neg_pos, h_neg]
    have h_s_dvd_Npos : (f_prime s) ∣ N_pos' := by
      rw [h_eq']
      exact h_s_dvd_Nneg
    have h_not_s_dvd_Npos' : ¬ (f_prime s) ∣ N_pos' := by
      unfold N_pos'
      intro h_dvd
      -- p := f_prime s is prime
      have s_prime := h_primes s hs
      have s_prime' := (@Nat.prime_iff (f_prime s)).mp s_prime
      -- From p ∣ product, obtain a factor where it divides
      have h_exists := (Prime.dvd_finset_prod_iff (S:=S_pos) s_prime'
        fun t => (f_prime t) ^ (f_exp t).toNat).mp h_dvd
      rcases h_exists with ⟨t, ht_pos, h_div_t_pow⟩
      -- Extract that t ∈ S
      have ht_in_S : t ∈ S := (Finset.mem_filter.mp ht_pos).1
      -- Deal with the exponent cases
      by_cases h_exp_zero : (f_exp t).toNat = 0
      · -- Then that factor is 1, impossible for a prime divisor
        have : (f_prime t) ^ (f_exp t).toNat = 1 := by simp [h_exp_zero]
        have : f_prime s ∣ 1 := by simpa [this] using h_div_t_pow
        have : f_prime s = 1 := Nat.dvd_one.mp this
        exact (Nat.Prime.ne_one s_prime) this
      · -- Positive exponent: prime dividing a power ⇒ divides the base
        have h_div_base : f_prime s ∣ f_prime t :=
          (Nat.Prime.dvd_of_dvd_pow s_prime) h_div_t_pow
        have t_prime := h_primes t ht_in_S
        -- Divides a prime ⇒ equality
        have h_eq : f_prime s = f_prime t := by
          have h_cases := (Nat.dvd_prime t_prime).1 h_div_base
          rcases h_cases with h_one | h_eq
          · exact False.elim ((Nat.Prime.ne_one s_prime) h_one)
          · exact h_eq
        -- Injectivity gives index equality
        have ht_eq : s = t := h_f_prime_inj h_eq
        -- Then s ∈ S_pos, contradiction
        have hs_in_S_pos : s ∈ S_pos := by simpa [ht_eq] using ht_pos
        exact h_s_not_in_pos hs_in_S_pos
    contradiction
  · -- Case: f_exp s = 0
    exact h_zero
  · -- Case: f_exp s > 0 , symmetric to the f_exp s < 0 case
    have h_s_in_pos : s ∈ S_pos := by
      rw [Finset.mem_filter]
      exact ⟨hs, le_of_lt h_pos⟩
    have h_s_not_in_neg : s ∉ S_neg := by
      rw [Finset.mem_filter]
      intro h_con
      obtain ⟨_, h_neg_lt⟩ := h_con
      exact not_lt_of_ge (le_of_lt h_pos) h_neg_lt
    have h_s_dvd_Npos : (f_prime s) ∣ N_pos' := by
      apply base_dvd_prod_exp h_s_in_pos (f_base:= f_prime) (f_exp:=fun n => (f_exp n).toNat)
      simp only [Int.lt_toNat, CharP.cast_eq_zero, h_pos]
    have h_s_dvd_Nneg : (f_prime s) ∣ N_neg' := by
      rw [←h_eq']
      exact h_s_dvd_Npos
    have h_not_s_dvd_Nneg' : ¬ (f_prime s) ∣ N_neg' := by
      unfold N_neg'
      intro h_dvd
      -- p := f_prime s is prime
      have s_prime := h_primes s hs
      have s_prime' := (@Nat.prime_iff (f_prime s)).mp s_prime
      -- From p ∣ product, obtain a factor where it divides
      have h_exists := (Prime.dvd_finset_prod_iff (S:=S_neg) s_prime'
        fun t => (f_prime t) ^ (- f_exp t).toNat).mp h_dvd
      rcases h_exists with ⟨t, ht_neg, h_div_t_pow⟩
      -- Extract that t ∈ S
      have ht_in_S : t ∈ S := (Finset.mem_filter.mp ht_neg).1
      -- Deal with the exponent cases
      by_cases h_exp_zero : (- f_exp t).toNat = 0
      · -- Then that factor is 1, impossible for a prime divisor
        have : (f_prime t) ^ (- f_exp t).toNat = 1 := by simp [h_exp_zero]
        have : f_prime s ∣ 1 := by simpa [this] using h_div_t_pow
        have : f_prime s = 1 := Nat.dvd_one.mp this
        exact (Nat.Prime.ne_one s_prime) this
      · -- Positive exponent: prime dividing a power ⇒ divides the base
        have h_div_base : f_prime s ∣ f_prime t :=
          (Nat.Prime.dvd_of_dvd_pow s_prime) h_div_t_pow
        have t_prime := h_primes t ht_in_S
        -- Divides a prime ⇒ equality
        have h_eq : f_prime s = f_prime t := by
          have h_cases := (Nat.dvd_prime t_prime).1 h_div_base
          rcases h_cases with h_one | h_eq
          · exact False.elim ((Nat.Prime.ne_one s_prime) h_one)
          · exact h_eq
        -- Injectivity gives index equality
        have ht_eq : s = t := h_f_prime_inj h_eq
        -- Then s ∈ S_neg, contradiction
        have hs_in_S_neg : s ∈ S_neg := by simpa [ht_eq] using ht_neg
        exact h_s_not_in_neg hs_in_S_neg
    contradiction
· intro h_all
  apply Finset.prod_eq_one
  intro s hs
  have h_pow: (f_prime s : ℝ) ^ (0: ℤ) = (f_prime s: ℝ) ^ (0: ℝ) := by norm_cast
  rw [h_all s hs,h_pow, Real.rpow_zero]

theorem q_prod_prime_pow_eq_one_iff
  {ι} [DecidableEq ι] {S : Finset ι} {f_prime : ι → ℕ} (f_exp : ι → ℚ)
    (h_primes : ∀ s ∈ S, Nat.Prime (f_prime s))
    (h_f_prime_inj : Function.Injective f_prime) :
    ((∏ s ∈ S, (f_prime s : ℝ) ^ (f_exp s: ℝ)) = 1) ↔ (∀ p ∈ S, f_exp p = 0) := by
  constructor
  · intro h_prod s hs
    set prime_pow := fun s => (f_prime s : ℝ) ^ (f_exp s: ℝ)
    let f_den := fun s => (f_exp s).den
    let D := ∏ s ∈ S, f_den s
    have prime_pow_exp_D :∀ s∈S, (prime_pow s) ^ D = (f_prime s : ℝ) ^ ((f_exp s * D: ℚ):ℝ) := by
      intro s hs
      rw [Rat.cast_mul, Rat.cast_natCast, Real.rpow_mul, Real.rpow_natCast]
      have h_pos: 0 < f_prime s := Nat.Prime.pos (h_primes s hs)
      have h_cast_pos : (0:ℝ) < (f_prime s : ℝ) := by exact_mod_cast h_pos
      exact le_of_lt h_cast_pos
    have h_exp_int : ∀ s ∈ S, (f_exp s * D) = (f_exp s * D).num := by
      intro s hs
      set q : ℚ := f_exp s
      have hdvd : q.den ∣ D := by
        simpa [D, q, f_den] using Finset.dvd_prod_of_mem (f := f_den) hs
      have hDcast : (D : ℚ) = ((q.den * (D / q.den) : ℕ) : ℚ) := by
        have hnat : q.den * (D / q.den) = D := Nat.mul_div_cancel' hdvd
        exact_mod_cast hnat.symm
      have hzq : (q : ℚ) * D = ((q.num * (D / q.den : ℕ) : ℤ) : ℚ) := by
        calc
        (q : ℚ) * D
          = (q : ℚ) * ((q.den * (D / q.den) : ℕ) : ℚ) := by rw [hDcast]
        _ = ((q : ℚ) * (q.den : ℚ)) * (D / q.den) := by grind
        _ = (q.num : ℚ) * (D / q.den) := by rw [Rat.mul_den_eq_num, div_eq_mul_inv]
        _ = ((q.num * (D / q.den : ℕ) : ℤ) : ℚ) := by norm_cast
      have hnum : ((q : ℚ) * D).num = q.num * (D / q.den : ℕ) := by
        simpa [hzq] using Rat.num_intCast (q.num * (D / q.den : ℕ) : ℤ)
      have : (q : ℚ) * D = (((q : ℚ) * D).num : ℚ) := by
        simpa [hnum] using hzq
      simpa [q] using this
    have h_prime_pow_exp_D' :
      ∀ s ∈ S, (prime_pow s) ^ D = (f_prime s : ℝ) ^ ((f_exp s * D).num : ℝ) := by
      intro s hs
      rw [prime_pow_exp_D s hs]
      rw (occs:=[1]) [h_exp_int s hs]
      have h_cast: (((f_exp s * D).num:ℚ):ℝ) = ((f_exp s * D).num:ℝ) := by norm_cast
      rw [h_cast]
    have h_prod_int : (∏ s ∈ S, prime_pow s) ^ D = ∏ s ∈ S, prime_pow s ^ D := by
      rw [Finset.prod_pow]
    rw [h_prod,one_pow] at h_prod_int
    have h_prod_int' :
      ∏ s ∈ S, prime_pow s ^ D = ((∏ s ∈ S, (f_prime s ) ^ (f_exp s * D).num):ℝ) := by
      refine Finset.prod_congr rfl ?_
      intro s hs
      exact_mod_cast h_prime_pow_exp_D' s hs
    rw [h_prod_int'] at h_prod_int
    have h_f_exp_D_num_eq_zero: ∀ s ∈ S, (f_exp s * D).num = 0 := by
      apply (z_prod_prime_pow_eq_one_iff f_prime (fun s => (f_exp s * D).num)
        h_primes h_f_prime_inj).mp h_prod_int.symm
    have hD_ne_zero_nat : D ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro t ht
      dsimp [f_den]
      exact ne_of_gt (Rat.den_pos (f_exp t))
    have hD_ne_zero_q : (D : ℚ) ≠ 0 := by exact_mod_cast hD_ne_zero_nat
    have h_f_exp_imp: ∀ s ∈ S, (f_exp s * D).num = 0 → f_exp s = 0 := by
      intro s hs hnum
      have hmul0 : f_exp s * (D : ℚ) = 0 := by
          simpa [hnum] using (h_exp_int s hs)
      rcases mul_eq_zero.mp hmul0 with h | h
      · exact h
      · contradiction
    exact h_f_exp_imp s hs (h_f_exp_D_num_eq_zero s hs)
  · intro h_all
    apply Finset.prod_eq_one
    intro s hs
    have h_pow: (f_prime s : ℝ) ^ ((0: ℚ): ℝ) = (f_prime s: ℝ) ^ (0: ℝ) := by
      have : (0: ℚ) = (0: ℝ) := by norm_cast
      rw [this]
    rw [h_all s hs,h_pow, Real.rpow_zero]
