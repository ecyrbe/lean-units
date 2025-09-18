import LeanUnits.Framework.Dimensions.Basic

namespace Units.Dimension

/--
Negation of a non-zero dimension is non-zero.
-/
theorem neg_ne_zero {d : Dimension} (hd : d ≠ 0) : -d ≠ 0 := by
  intro h
  exact hd (neg_eq_zero.mp h)

/--
Subtraction of two different dimensions is non-zero.
-/
theorem sub_ne_zero_of_ne {d1 d2 : Dimension} (h : d1 ≠ d2) : d1 - d2 ≠ 0 := by
  intro h0
  have h1 := congrArg (fun x => x + d2) h0
  simp [sub_eq_add_neg, add_comm, add_left_comm] at h1
  exact h h1

/--
Addition of two dimensions that are not negatives of each other is non-zero.
-/
theorem add_ne_zero_of_ne_neg {d1 d2 : Dimension} (h : d1 ≠ -d2) : d1 + d2 ≠ 0 := by
  intro h0
  have : d1 = -d2 := by
    have h1 := congrArg (fun x => x + -d2) h0
    simp [add_comm, add_assoc] at h1
    exact h1
  exact h this

/--
Multiplying a dimension by a rational is zero
iff either the dimension is zero or the rational is zero
-/
theorem smul_eq_zero_iff {d : Dimension} {q : ℚ} :
  q • d = 0 ↔ q = 0 ∨  d = 0 := by
  constructor
  · intro h
    by_contra h'
    have hq : q ≠ 0 := (not_or.mp h').1
    have hd : d ≠ 0 := (not_or.mp h').2
    exact (smul_ne_zero hq hd) h
  · intro hd
    cases hd with
    | inl hq => rw [hq, zero_smul]
    | inr hd => rw [hd, smul_zero]

/--
Multiplying a dimension by a rational is non-zero
iff both the dimension and the rational are non-zero
-/
theorem smul_ne_zero_iff {d : Dimension} {q : ℚ} :
  q • d ≠ 0 ↔ q ≠ 0 ∧ d ≠ 0 := by
  simp only [not_congr smul_eq_zero_iff, not_or, ne_eq]

/--
Dimension built from a string identifier is a base dimension.
-/
theorem base_is_base (s : String) : IsBase (Dimension.ofString s) := by use s

/--
Base dimensions are single dimensions.
-/
theorem IsBase.to_single {d : Dimension} (h : IsBase d) : IsSingle d := by
  obtain ⟨s, rfl⟩ := h
  use s, 1
  constructor
  · norm_num
  · rfl

/--
Single dimensions are non-zero.
-/
theorem IsSingle.ne_zero {d : Dimension} (h : IsSingle d) : d ≠ 0 := by
  obtain ⟨s, q, hq, rfl⟩ := h
  have h_zero: 0 = Dimension.dimensionless := by rfl
  rw [h_zero, Dimension.dimensionless]
  intro h
  apply congrArg Dimension._impl at h
  simp only [DFinsupp.single_eq_zero] at h
  contradiction

/--
Base dimensions are non-zero.
-/
theorem IsBase.ne_zero (d : Dimension) (h : IsBase d) : d ≠ 0 := h.to_single.ne_zero

/--
Scalar multiplication of a single dimension by a non-zero rational is a single dimension.
-/
theorem IsSingle.smul {d : Dimension} (h : IsSingle d) (q : ℚ) (hq : q ≠ 0) :
  IsSingle (q • d) := by
  obtain ⟨s, r, hr, rfl⟩ := h
  use s, q • r
  constructor
  · apply mul_ne_zero hq hr
  · rw [DFinsupp.single_smul]
    rfl

/--
companion to `IsSingle.smul`, giving the names and exponents of the dimensions
-/
theorem IsSingle.smul_name_exponent {d : Dimension} (h : IsSingle d) (q : ℚ) (hq : q ≠ 0) :
  (h.smul q hq).name = h.name ∧ (h.smul q hq).exponent = q • h.exponent := by
  set hsmul := h.smul q hq
  obtain ⟨hq,hd⟩:= h.name_exponent_spec
  obtain ⟨hqsmul,hdsmul⟩:= hsmul.name_exponent_spec
  have hsmul_simp : ∀ s: String, ∀ r r': ℚ,
    (r' • ({ _impl := fun₀ | s => r }: Dimension)) = { _impl := r' • fun₀ | s => r } :=
      by intros; rfl
  have hsmul'_simp : ∀ s: String, ∀ r r': ℚ,
    ({ _impl := r' • fun₀ | s => r }: Dimension) = { _impl := fun₀ | s => r' • r } :=
      by intros; rw [DFinsupp.single_smul]
  rw (occs := [1]) [hd] at hdsmul
  simp only [hsmul_simp, hsmul'_simp, mk.injEq] at hdsmul
  have hcases := (DFinsupp.single_eq_single_iff _ _ _ _).mp hdsmul.symm
  constructor <;> cases hcases <;> rename_i h' <;> obtain ⟨hname, hexp⟩ := h' <;> try contradiction
  · exact hname
  · rw [heq_iff_eq] at hexp
    exact hexp

/--
Negation of a single dimension is a single dimension.
-/
theorem IsSingle.neg {d : Dimension} (h : IsSingle d) : IsSingle (-d) := by
  have h_neg : -d = (-1: ℚ) • d := by module
  rw [h_neg]
  exact IsSingle.smul h (-1) (by norm_num)

/--
companion to `IsSingle.neg`, giving the names and exponents of the dimensions
-/
theorem IsSingle.neg_name_exponent {d : Dimension} (h : IsSingle d) :
  h.neg.name = h.name ∧ h.neg.exponent = -h.exponent := by
  set hneg := h.neg
  obtain ⟨hq,hd⟩:= h.name_exponent_spec
  obtain ⟨hqneg,hdneg⟩:= hneg.name_exponent_spec
  have hneg_simp :
    ∀ s: String, ∀ q: ℚ, -({ _impl := fun₀ | s => q }: Dimension) = { _impl := -fun₀ | s => q } :=
      by intros; rfl
  have hneg'_simp :
    ∀ s: String, ∀ q: ℚ, ({ _impl := -fun₀ | s => q }: Dimension) = { _impl := fun₀ | s => -q } :=
      by intros; rw [DFinsupp.single_neg]
  rw (occs := [1]) [hd] at hdneg
  simp only [hneg_simp, hneg'_simp, mk.injEq] at hdneg
  have hcases := (DFinsupp.single_eq_single_iff _ _ _ _).mp hdneg.symm
  constructor <;> cases hcases <;> rename_i h' <;> obtain ⟨hname, hexp⟩ := h' <;> try contradiction
  · exact hname
  · rw [heq_iff_eq] at hexp
    exact hexp

/--
Negation of a base dimension is a single dimension.
-/
theorem IsBase.neg (d : Dimension) (h : IsBase d) : IsSingle (-d) := h.to_single.neg

/--
Scalar multiplication of a base dimension by a non-zero rational is a single dimension.
-/
theorem IsBase.smul (d : Dimension) (h : IsBase d) (q : ℚ) (hq : q ≠ 0) : IsSingle (q • d) :=
  h.to_single.smul q hq

/--
Addition of two single dimensions that have different names or that don't have
exponents negative of each other is non-zero.
-/
theorem IsSingle.add_ne_zero {d1 d2 : Dimension}
  (h1 : IsSingle d1) (h2 : IsSingle d2) (h : h1.name ≠ h2.name ∨ h1.exponent ≠ -h2.exponent) :
  d1 + d2 ≠ 0 := by
  intro hd
  apply congrArg Dimension._impl at hd
  replace hd : d1._impl + d2._impl = 0 := by exact hd
  replace hd : d1._impl = -d2._impl := by apply congrArg (· - d2._impl) at hd; simp at hd; exact hd
  obtain ⟨hq1, hd1⟩ := h1.name_exponent_spec
  obtain ⟨hq2, hd2⟩ := h2.name_exponent_spec
  rw [hd1, hd2] at hd
  simp only at hd
  rw [←DFinsupp.single_neg] at hd
  have hcases := (DFinsupp.single_eq_single_iff _ _ _ _).mp hd
  cases hcases <;> rename_i h'
  · cases h <;> rename_i h
    · exact h h'.1
    · obtain ⟨hname, hexp⟩ := h'
      rw [heq_iff_eq] at hexp
      contradiction
  · cases h'; contradiction

/--
Subtraction of two single dimensions that have different names or exponents is non-zero.
-/
theorem IsSingle.sub_ne_zero {d1 d2 : Dimension}
  (h1 : IsSingle d1) (h2 : IsSingle d2) (h : h1.name ≠ h2.name ∨ h1.exponent ≠ h2.exponent) :
  d1 - d2 ≠ 0 := by
  have h2_neg_name : h2.name = h2.neg.name := h2.neg_name_exponent.1.symm
  have h2_neg_exponent : h2.exponent = -h2.neg.exponent := by rw [h2.neg_name_exponent.2, neg_neg]
  rw [h2_neg_name, h2_neg_exponent ] at h
  rw [sub_eq_add_neg]
  exact IsSingle.add_ne_zero h1 h2.neg h

/--
Multiplying a single dimension by a non-zero rational is non-zero.
-/
theorem IsSingle.smul_ne_zero {d : Dimension} {q : ℚ}
  (hd : IsSingle d) (hq : q ≠ 0) : q • d ≠ 0 :=
  _root_.smul_ne_zero hq hd.ne_zero

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
