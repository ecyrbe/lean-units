import LeanUnits.Framework.Dimensions.Basic

namespace Units.Dimension.PrimeScale

theorem base_ne_zero (s : String) : Dimension.ofString s ≠ 0 := by
  have h_zero: 0 = Dimension.dimensionless := by rfl
  rw [h_zero]
  unfold Dimension.ofString Dimension.dimensionless
  intro h
  simpa [DFinsupp.single_eq_zero] using congrArg Dimension._impl h

theorem smul_ne_zero (d : Dimension) (q : ℚ) (hd : d ≠ 0) (hq : q ≠ 0) : q • d ≠ 0 := by
  intro h
  replace h := congrArg (fun x => q⁻¹ • x) h
  simp only at h
  rw [smul_zero, smul_smul, inv_mul_cancel₀ hq, one_smul] at h
  contradiction

theorem scaler_zero : PrimeScale (0 : Dimension) = 1 := by
  exact DFinsupp.prod_zero_index

theorem scaler_one : PrimeScale (1 : Dimension) = 1 := by
  have one_eq_zero : (1 : Dimension) = 0 := by rfl
  rw [one_eq_zero,scaler_zero]

theorem scaler_add (d1 d2 : Dimension) : PrimeScale (d1 + d2) = PrimeScale d1 * PrimeScale d2 := by
  exact DFinsupp.prod_add_index @prime_pow_zero @prime_pow_add

theorem scaler_mul (d1 d2 : Dimension) : PrimeScale (d1 * d2) = PrimeScale d1 * PrimeScale d2 := by
  rw [HMul.hMul, instHMul]
  simp [scaler_add]

theorem scaler_neg' (d : Dimension) :
  PrimeScale (-d) = d._impl.prod (fun i q => prime_pow i (-q))  := by
  exact DFinsupp.prod_neg_index @prime_pow_zero

theorem scaler_neg (d : Dimension) :
  PrimeScale (-d) = (PrimeScale d)⁻¹ := by
  rw [scaler_neg']
  unfold PrimeScale
  rw [←DFinsupp.prod_inv]
  congr
  ext i q
  rw [prime_pow_neg]

theorem scaler_inv (d : Dimension) :
  PrimeScale (d⁻¹) = (PrimeScale d)⁻¹ := by
  rw [Inv.inv, instInv]
  simp [scaler_neg]

theorem scaler_sub (d1 d2 : Dimension) :
  PrimeScale (d1 - d2) = PrimeScale d1 / PrimeScale d2 := by
  rw [sub_eq_add_neg, scaler_add, scaler_neg, div_eq_mul_inv]

theorem scaler_div (d1 d2 : Dimension) :
  PrimeScale (d1 / d2) = PrimeScale d1 / PrimeScale d2 := by
  rw [HDiv.hDiv, instHDiv]
  simp [scaler_sub]

theorem scaler_nsmul (d : Dimension) (n : ℕ) :
  PrimeScale (n • d) = (PrimeScale d) ^ n := by
  induction' n with n ih
  · rw [zero_nsmul, scaler_zero, pow_zero]
  · rw [succ_nsmul, scaler_add, ih, pow_succ]

theorem scaler_npow (d : Dimension) (n : ℕ) :
  PrimeScale (d ^ n) = (PrimeScale d) ^ n := by
  rw [HPow.hPow, instHPow]
  simp [scaler_nsmul]

theorem scaler_zsmul (d : Dimension) (n : ℤ) :
  PrimeScale (n • d) = (PrimeScale d) ^ n := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, natCast_zsmul, scaler_nsmul, zpow_natCast]
  | negSucc n => rw [negSucc_zsmul, scaler_neg, scaler_nsmul, zpow_negSucc]

theorem scaler_zpow (d : Dimension) (n : ℤ) :
  PrimeScale (d ^ n) = (PrimeScale d) ^ n := by
  rw [HPow.hPow, instHPow]
  simp [scaler_zsmul]

end Units.Dimension.PrimeScale
