import LeanUnits.Framework.Units.Basic

namespace Units.Unit

theorem equiv_refl {u : Unit} : u ≈ u := Setoid.refl u

theorem equiv_symm {u1 u2 : Unit} (h : u1 ≈ u2) : u2 ≈ u1 := Setoid.symm h

theorem equiv_trans {u1 u2 u3 : Unit} (h1 : u1 ≈ u2) (h2 : u2 ≈ u3) : u1 ≈ u3 := Setoid.trans h1 h2

theorem eq_imp_equiv {μ} [Setoid μ] {u1 u2 : μ} (h : u1 = u2) : u1 ≈ u2 := by
  rw [h]
  exact Setoid.refl u2

@[simp]
theorem base_unit_dim_eq_dim (d : Dimension) (s : String) :
  (defineUnit s d).dimension = d := by
  rw [defineUnit, dimension]
  apply DFinsupp.sum_single_index
  repeat rw [Prod.snd_zero]

@[simp]
theorem base_unit_dim_eq_self' (d : Dimension) (s : String) :
  𝒟 (defineUnit s d) = d :=
  base_unit_dim_eq_dim d s

@[simp]
theorem derived_unit_dim_eq_dim (u : Unit) (s : String) (c : Conversion) :
  (defineDerivedUnit s u c).dimension = u.dimension := by
  rw [defineDerivedUnit, dimension]
  apply DFinsupp.sum_single_index
  repeat rw [Prod.snd_zero]

@[simp]
theorem derived_unit_dim_eq_self' (u : Unit) (s : String) (c : Conversion) :
  𝒟 (defineDerivedUnit s u c) =  𝒟 u :=
  derived_unit_dim_eq_dim u s c

@[simp]
theorem add_unit_dim {u1 u2 : Unit} :
  (u1 + u2).dimension = u1.dimension + u2.dimension := by
  rw [dimension, dimension, dimension]
  apply DFinsupp.sum_add_index
  · intro
    repeat rw [Prod.snd_zero]
  · intros
    repeat rw [Prod.snd_add]

@[simp]
theorem sub_unit_dim {u1 u2 : Unit} :
  (u1 - u2).dimension = u1.dimension - u2.dimension := by
  rw [dimension, dimension, dimension]
  apply DFinsupp.sum_sub_index
  intros
  repeat rw [Prod.snd_sub]

@[simp]
theorem neg_unit_dim {u : Unit} :
  (-u).dimension = -u.dimension := by
  rw [←zero_sub, sub_unit_dim, sub_eq_neg_self]
  rfl

@[simp]
theorem nsmul_unit_dim (c : ℕ) (u : Unit) :
  (c • u).dimension = c • u.dimension := by
  induction' c with c ih
  · repeat rw [zero_nsmul]
    rfl
  · simp [succ_nsmul, add_unit_dim, ih]

@[simp]
theorem zsmul_unit_dim (c : ℤ) (u : Unit) :
  (c • u).dimension = c • u.dimension := by
  cases c with
  | ofNat n =>
      simp only [Int.ofNat_eq_coe, natCast_zsmul, nsmul_unit_dim n u]
  | negSucc n =>
      simp only [negSucc_zsmul, neg_unit_dim, nsmul_unit_dim]

@[simp]
theorem base_unit_conv_eq_conv (d : Dimension) (s : String) :
  (defineUnit s d).conversion = 0 := by
  rw [defineUnit, conversion]
  apply DFinsupp.sum_single_index
  rw [Prod.snd_zero, Prod.fst_zero]

theorem conv_zero_eq_conv_identity : Conversion.identity = 0 := rfl

-- @[simp]
-- theorem conv_div_zero (c : Conversion) :
--   c.div 0 = c := by
--   simp [←conv_zero_eq_conv_identity,Conversion.div, Conversion.inv,
--       Conversion.mul, Conversion.identity]

-- @[simp]
-- theorem zero_div_conv (c : Conversion) {h : c.offset = 0} :
--   Conversion.div 0 c = -c := by
--   simp [Conversion.div, Conversion.inv, Conversion.mul, ←conv_zero_eq_conv_identity,
--     Conversion.identity, h, Conversion.instNeg, Conversion.neg]


-- @[simp]
-- theorem derived_unit_conv_eq_conv (u : Unit) (s : String) (c : Conversion) :
--   (defineDerivedUnit s u c).conversion = c-u.conversion := by
--   rw [defineDerivedUnit, conversion]
--   apply DFinsupp.sum_single_index
--   rw [Prod.snd_zero, Prod.fst_zero]

@[simp]
theorem add_unit_conv {u1 u2 : Unit} :
  (u1 + u2).conversion = u1.conversion + u2.conversion := by
  rw [conversion, conversion, conversion]
  apply DFinsupp.sum_add_index
  · intro
    rw [Prod.snd_zero, Prod.fst_zero]
  · intros
    rw [Prod.snd_add, Prod.fst_add]

@[simp]
theorem sub_unit_conv {u1 u2 : Unit} :
  (u1 - u2).conversion = u1.conversion - u2.conversion := by
  rw [conversion, conversion, conversion]
  apply DFinsupp.sum_sub_index
  intros
  rw [Prod.snd_sub, Prod.fst_sub]

@[simp]
theorem neg_unit_conv {u : Unit} :
  (-u).conversion = -u.conversion := by
  rw [←zero_sub, sub_unit_conv, sub_eq_neg_self]
  rfl

@[simp]
theorem nsmul_unit_conv (c : ℕ) (u : Unit) :
  (c • u).conversion = c • u.conversion := by
  induction' c with c ih
  · repeat rw [zero_nsmul]
    rfl
  · simp [succ_nsmul, add_unit_conv, ih]

@[simp]
theorem zsmul_unit_conv (c : ℤ) (u : Unit) :
  (c • u).conversion = c • u.conversion := by
  cases c with
  | ofNat n =>
      simp only [Int.ofNat_eq_coe, natCast_zsmul, nsmul_unit_conv n u]
  | negSucc n =>
      simp only [negSucc_zsmul, neg_unit_conv, nsmul_unit_conv]

end Units.Unit
