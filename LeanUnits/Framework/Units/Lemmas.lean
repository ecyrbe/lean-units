import LeanUnits.Framework.Units.Basic
import LeanUnits.Framework.SimpSets

namespace Units.Unit

@[unit_set]
theorem mul_eq_add (u1 u2 : Unit) : u1 * u2 = u1 + u2 := rfl
@[unit_set]
theorem div_eq_sub (u1 u2 : Unit) : u1 / u2 = u1 - u2 := rfl
@[unit_set]
theorem inv_eq_neg (u : Unit) : u⁻¹ = -u := rfl
@[unit_set]
theorem zpow_eq_zsmul (u : Unit) (n : ℤ) :  u ^ n = n • u := rfl
@[unit_set]
theorem npow_eq_nsmul (u : Unit) (n : ℕ) :  u ^ n = n • u := rfl

theorem equiv_refl {u : Unit} : u ≈ u := Setoid.refl u

theorem equiv_symm {u1 u2 : Unit} (h : u1 ≈ u2) : u2 ≈ u1 := Setoid.symm h

theorem equiv_trans {u1 u2 u3 : Unit} (h1 : u1 ≈ u2) (h2 : u2 ≈ u3) : u1 ≈ u3 := Setoid.trans h1 h2

@[dimension_set]
theorem base_unit_dim_eq_dim (d : Dimension) (s : String) :
  (defineUnit s d).dimension = d := by
  rw [defineUnit, dimension]
  apply DFinsupp.sum_single_index
  repeat rw [Prod.snd_zero]

@[dimension_set]
theorem base_unit_dim_eq_self' (d : Dimension) (s : String) :
  𝒟 (defineUnit s d) = d :=
  base_unit_dim_eq_dim d s

@[dimension_set]
theorem derived_unit_dim_eq_dim (u : Unit) (s : String) (c : Conversion) :
  (defineDerivedUnit s u c).dimension = u.dimension := by
  rw [defineDerivedUnit, dimension]
  apply DFinsupp.sum_single_index
  repeat rw [Prod.snd_zero]

@[dimension_set]
theorem derived_unit_dim_eq_self' (u : Unit) (s : String) (c : Conversion) :
  𝒟 (defineDerivedUnit s u c) =  𝒟 u :=
  derived_unit_dim_eq_dim u s c

@[dimension_set]
theorem add_unit_dim {u1 u2 : Unit} :
  (u1 + u2).dimension = u1.dimension + u2.dimension := by
  rw [dimension, dimension, dimension]
  apply DFinsupp.sum_add_index
  · intro
    repeat rw [Prod.snd_zero]
  · intros
    repeat rw [Prod.snd_add]

@[dimension_set]
theorem sub_unit_dim {u1 u2 : Unit} :
  (u1 - u2).dimension = u1.dimension - u2.dimension := by
  rw [dimension, dimension, dimension]
  apply DFinsupp.sum_sub_index
  intros
  repeat rw [Prod.snd_sub]

@[dimension_set]
theorem neg_unit_dim {u : Unit} :
  (-u).dimension = -u.dimension := by
  rw [←zero_sub, sub_unit_dim, sub_eq_neg_self]
  rfl

@[dimension_set]
theorem nsmul_unit_dim (c : ℕ) (u : Unit) :
  (c • u).dimension = c • u.dimension := by
  induction c with
  | zero =>
    repeat rw [zero_nsmul]
    rfl
  | succ c ih =>
    simp [succ_nsmul, add_unit_dim, ih]

@[dimension_set]
theorem zsmul_unit_dim (c : ℤ) (u : Unit) :
  (c • u).dimension = c • u.dimension := by
  cases c with
  | ofNat n =>
      simp only [Int.ofNat_eq_coe, natCast_zsmul, nsmul_unit_dim n u]
  | negSucc n =>
      simp only [negSucc_zsmul, neg_unit_dim, nsmul_unit_dim]

@[conv_set]
theorem base_unit_conv_eq_conv (d : Dimension) (s : String) :
  (defineUnit s d).conversion = 0 := by
  rw [defineUnit, conversion]
  apply DFinsupp.sum_single_index
  rw [Prod.snd_zero, Prod.fst_zero]

theorem conv_zero_eq_conv_identity : Conversion.identity = 0 := rfl

@[conv_set]
theorem conv_div_zero (c : Conversion) :
  c.div 0 = c := by
  simp [←conv_zero_eq_conv_identity,Conversion.div, Conversion.inv,
      Conversion.mul, Conversion.identity]

@[conv_set]
theorem derived_unit_conv_eq_conv (u : Unit) (s : String) (c : Conversion) :
  (defineDerivedUnit s u c).conversion = c/u.conversion := by
  rw [defineDerivedUnit, conversion]
  apply DFinsupp.sum_single_index
  rw [Prod.snd_zero, Prod.fst_zero]

@[conv_set]
theorem add_unit_conv {u1 u2 : Unit} :
  (u1 + u2).conversion = u1.conversion + u2.conversion := by
  rw [conversion, conversion, conversion]
  apply DFinsupp.sum_add_index
  · intro
    rw [Prod.snd_zero, Prod.fst_zero]
  · intros
    rw [Prod.snd_add, Prod.fst_add]

@[conv_set]
theorem sub_unit_conv {u1 u2 : Unit} :
  (u1 - u2).conversion = u1.conversion - u2.conversion := by
  rw [conversion, conversion, conversion]
  apply DFinsupp.sum_sub_index
  intros
  rw [Prod.snd_sub, Prod.fst_sub]

@[conv_set]
theorem neg_unit_conv {u : Unit} :
  (-u).conversion = -u.conversion := by
  rw [←zero_sub, sub_unit_conv, sub_eq_neg_self]
  rfl

@[conv_set]
theorem nsmul_unit_conv (c : ℕ) (u : Unit) :
  (c • u).conversion = c • u.conversion := by
  induction c with
  | zero =>
    repeat rw [zero_nsmul]
    rfl
  | succ c ih =>
    simp [succ_nsmul, add_unit_conv, ih]

@[conv_set]
theorem zsmul_unit_conv (c : ℤ) (u : Unit) :
  (c • u).conversion = c • u.conversion := by
  cases c with
  | ofNat n =>
      simp only [Int.ofNat_eq_coe, natCast_zsmul, nsmul_unit_conv n u]
  | negSucc n =>
      simp only [negSucc_zsmul, neg_unit_conv, nsmul_unit_conv]

end Units.Unit
