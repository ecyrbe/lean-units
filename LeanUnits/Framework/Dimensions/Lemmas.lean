import LeanUnits.Framework.Dimensions.Basic

namespace Units.Dimension


theorem base_is_base (s : String) : IsBase (Dimension.ofString s) := by use s

theorem base_ne_zero (d : Dimension) (h : IsBase d) : d ≠ 0 := by
  obtain ⟨s, rfl⟩ := h
  have h_zero: 0 = Dimension.dimensionless := by rfl
  rw [h_zero]
  unfold Dimension.ofString Dimension.dimensionless
  intro h
  simpa [DFinsupp.single_eq_zero] using congrArg Dimension._impl h

theorem smul_ne_zero {d : Dimension} {q : ℚ} (hd : d ≠ 0) (hq : q ≠ 0) : q • d ≠ 0 := by
  intro h
  replace h : q⁻¹ • q • d = q⁻¹ • 0 := by rw [h]
  rw [smul_zero, smul_smul, inv_mul_cancel₀ hq, one_smul] at h
  contradiction

theorem neg_ne_zero {d : Dimension} (hd : d ≠ 0) : -d ≠ 0 := by
  intro h
  exact hd (neg_eq_zero.mp h)

theorem sub_ne_zero_of_ne {d1 d2 : Dimension} (h : d1 ≠ d2) : d1 - d2 ≠ 0 := by
  intro h0
  have h1 := congrArg (fun x => x + d2) h0
  simp [sub_eq_add_neg, add_comm, add_left_comm] at h1
  exact h h1

theorem add_ne_zero_of_ne_neg {d1 d2 : Dimension} (h : d1 ≠ -d2) : d1 + d2 ≠ 0 := by
  intro h0
  have : d1 = -d2 := by
    have h1 := congrArg (fun x => x + -d2) h0
    simp [add_comm, add_assoc] at h1
    exact h1
  exact h this

theorem smul_eq_zero_iff {d : Dimension} {q : ℚ} :
  q • d = 0 ↔ q = 0 ∨  d = 0 := by
  constructor
  · intro h
    by_contra h'
    have hq : q ≠ 0 := (not_or.mp h').1
    have hd : d ≠ 0 := (not_or.mp h').2
    exact (smul_ne_zero hd hq) h
  · intro hd
    cases hd with
    | inl hq => rw [hq, zero_smul]
    | inr hd => rw [hd, smul_zero]

theorem smul_ne_zero_iff {d : Dimension} {q : ℚ} :
  q • d ≠ 0 ↔ q ≠ 0 ∧ d ≠ 0 := by
  simpa [not_or] using (not_congr smul_eq_zero_iff)

namespace PrimeScale

/-!
PrimeScale lemmas
-/

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
