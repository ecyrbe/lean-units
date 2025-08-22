import LeanUnits.Dimensions.Base.Basic

namespace Units.Dimension.Base

theorem eq_name (b₁ b₂ : Base) : b₁ = b₂ → b₁.name = b₂.name := by
  intro h_eq
  rw [h_eq]

theorem neq_name (b₁ b₂ : Base) : b₁.name ≠ b₂.name → b₁ ≠ b₂ := by
  aesop

theorem eq_iff (b₁ b₂ : Base) : b₁ = b₂ ↔ b₁.name = b₂.name ∧ b₁.exponent = b₂.exponent := by
    aesop

theorem neq_iff (b₁ b₂ : Base) : b₁ ≠ b₂ ↔ b₁.name ≠ b₂.name ∨ b₁.exponent ≠ b₂.exponent := by
    have h_eq := eq_iff b₁ b₂
    apply not_congr at h_eq
    rw [not_and_or] at h_eq
    exact h_eq

theorem merge.eq_some_iff (b : String) (e₁ e₂ : ℚ) : (merge b e₁ e₂).isSome ↔ e₁ + e₂ ≠ 0 := by
  unfold merge
  constructor
  · intro h_eq
    aesop
  · intro h
    split
    · contradiction
    · simp

theorem merge.eq_none_iff (b : String) (e₁ e₂ : ℚ) : merge b e₁ e₂ = none ↔ e₁ + e₂ = 0 := by
  unfold merge
  constructor
  · intro h_eq
    simp at h_eq
    exact h_eq
  · intro h
    simp [h]

theorem merge.eq_some_imp_name_eq (b : String) (e₁ e₂ : ℚ) :
  ∀ z, merge b e₁ e₂ = some z → z.name = b := by
  intro z h
  unfold merge at h
  split at h
  · simp at h
  · injection h with h'
    rw [h'.symm]

theorem merge.eq_some_imp_exponent_eq_add (b : String) (e₁ e₂ : ℚ) :
  ∀ z, merge b e₁ e₂ = some z → z.exponent = e₁ + e₂ := by
  intro z h
  unfold merge at h
  split at h
  · simp at h
  · injection h with h'
    rw [h'.symm]

theorem merge.comm (b : String) (e₁ e₂ : ℚ) : merge b e₁ e₂ = merge b e₂ e₁ := by
  unfold merge
  by_cases h : e₁ + e₂ = 0
  · simp only [h, add_comm]
  · simp only [h, add_comm]

end Units.Dimension.Base
