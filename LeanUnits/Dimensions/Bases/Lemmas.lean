import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Data.String.Basic
import Lean
import LeanUnits.Dimensions.Base.Basic
import LeanUnits.Dimensions.Base.Lemmas
import LeanUnits.Dimensions.Bases.Basic

namespace Units.Dimension.Bases

namespace Sorted

theorem nil : Sorted [] := by
  unfold Sorted
  exact List.Pairwise.nil

theorem cons {b : Base} {l : Bases} :
  Sorted (b::l) ↔ (∀ b' ∈ l, b.name < b'.name) ∧ Sorted l := by
  unfold Sorted
  exact List.pairwise_cons

end Sorted


theorem name_eq_imp_nodup_iff_nodup {a b : Base} (l : Bases) :
  a.name = b.name → (Nodup (a::l) ↔ Nodup (b::l)) := by
  intro h_eq
  unfold Nodup
  simp only [List.pairwise_cons, h_eq]

theorem name_eq_imp_sorted_iff_sorted {a b : Base} (l : Bases) :
  a.name = b.name → (Sorted (a::l) ↔ Sorted (b::l)) := by
  intro h_eq
  unfold Sorted
  simp only [List.pairwise_cons, h_eq]

theorem base_neq_imp_nodup (l : Bases) :
  (∀ a b : Base, a ∈ l → b ∈ l → a.name ≠ b.name) → Nodup l := by
  intro h
  unfold Nodup
  induction l with
  | nil => trivial
  | cons x xs xh => simp_all

theorem sorted_imp_nodup (l : Bases) : Sorted l → Nodup l := by
  unfold Sorted Nodup
  intro h
  exact List.Pairwise.imp ne_of_lt h

theorem base_eq_iff_sorted_name_eq {l : Bases} (h_sorted : Sorted l) (b₁ b₂ : Base) :
  b₁ ∈ l → b₂ ∈ l → (b₁ = b₂ ↔ b₁.name = b₂.name) := by
  intro h_b1 h_b2
  constructor
  · intro h_eq; rw [h_eq]
  · intro h_name_eq
    induction l with
    | nil => cases h_b1
    | cons x xs ih =>
      rw [Sorted.cons] at h_sorted
      have hxlt : ∀ b' ∈ xs, x.name < b'.name := h_sorted.1
      have hs : Sorted xs := h_sorted.2
      simp [List.mem_cons] at h_b1 h_b2
      cases h_b1 with
      | inl hb1eq =>
        subst hb1eq
        cases h_b2 with
        | inl hb2eq =>
          subst hb2eq
          rfl
        | inr hb2in =>
          have : b₁.name < b₂.name := hxlt b₂ hb2in
          have : b₁.name < b₁.name := by rw [← h_name_eq] at this; assumption
          exact False.elim ((lt_irrefl _) this)
      | inr hb1in =>
        cases h_b2 with
        | inl hb2eq =>
          subst hb2eq
          have : b₂.name < b₁.name := hxlt b₁ hb1in
          have : b₂.name < b₂.name := by rw [h_name_eq] at this; assumption
          exact False.elim ((lt_irrefl _) this)
        | inr hb2in =>
          exact ih hs hb1in hb2in

theorem eq_of_sorted_of_same_elements {l1 l2 : Bases} (h1 : Sorted l1) (h2 : Sorted l2)
    (h : ∀ b, b ∈ l1 ↔ b ∈ l2) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
      cases l2 with
      | nil => rfl
      | cons y ys =>
        specialize h y
        simp only [List.not_mem_nil, List.mem_cons, true_or, iff_true] at h
  | cons x xs xh =>
      induction l2 with
      | nil =>
        specialize h x
        simp only [List.mem_cons, true_or, List.not_mem_nil, iff_false, not_true_eq_false] at h
      | cons y ys yh =>
        rw [List.cons_eq_cons]
        rw [Sorted.cons] at h1 h2
        have h_x_eq_y : x = y := by
              have h_x : x ∈ x :: xs := by simp
              have h_y : y ∈ y :: ys := by simp
              have h_x_in_y_ys : x ∈ y :: ys := by rw [←h]; exact h_x
              have h_y_in_x_xs : y ∈ x :: xs := by rw [h]; exact h_y
              simp only [List.mem_cons] at h_x_in_y_ys h_y_in_x_xs
              cases h_x_in_y_ys with
              | inl h_x_eq_y => exact h_x_eq_y
              | inr h_x_in_ys =>
                cases h_y_in_x_xs with
                | inl h_y_eq_x => exact h_y_eq_x.symm
                | inr h_y_in_xs => exact False.elim (lt_asymm (h1.1 y h_y_in_xs) (h2.1 x h_x_in_ys))
        constructor
        · assumption
        · have h_xs_ys : ∀ (b : Base), b ∈ xs ↔ b ∈ ys := by
            intro b
            specialize h b
            rw [h_x_eq_y] at h
            by_cases h_bx : b = x
            · rw [h_bx, h_x_eq_y]
              constructor
              · intro h_y_in_xs
                rw [←h_x_eq_y] at h_y_in_xs
                have h_x_lt_x : x.name < x.name := h1.1 x h_y_in_xs
                exact False.elim (lt_irrefl _ h_x_lt_x)
              · intro h_x_in_ys
                rw [←h_x_eq_y] at h_x_in_ys
                have h_y_lt_x : y.name < x.name := h2.1 x h_x_in_ys
                have h_x_lt_x : x.name < x.name := by rw [←h_x_eq_y] at h_y_lt_x; assumption
                exact False.elim (lt_irrefl _ h_x_lt_x)
            · simpa [h_x_eq_y.symm,h_bx] using h
          exact xh h1.2 h2.2 h_xs_ys

theorem exponentOf_eq_exp {l : Bases} (h_sorted : Sorted l) (b : Base)
  (h_mem : b ∈ l) : exponentOf b.name l = b.exponent := by
  induction l with
  | nil => cases h_mem
  | cons x xs ih =>
    rw [Bases.Sorted.cons] at h_sorted
    rw [List.mem_cons] at h_mem
    cases h_mem with
    | inl h_eq =>
      subst h_eq
      unfold exponentOf
      simp only [decide_true, List.find?_cons_of_pos]
    | inr h_in =>
      have hxne : x.name ≠ b.name := by
        exact ne_of_lt (h_sorted.1 b h_in)
      have h_tail := ih h_sorted.2 h_in
      unfold exponentOf at h_tail ⊢
      simp only [List.find?, hxne, decide_false, h_tail]

theorem exponentOf_eq_zero {l : Bases} (name : String)
  (h : ∀ b ∈ l, b.name ≠ name) : exponentOf name l = 0 := by
  induction l with
  | nil =>
    simp [exponentOf]
  | cons x xs ih =>
    have hx : x.name ≠ name := h x (by simp)
    have hxs : ∀ b ∈ xs, b.name ≠ name := by
      intro b hb; exact h b (by simp [hb])
    specialize ih hxs
    unfold exponentOf
    simp_all only [List.mem_cons, not_false_eq_true, decide_false,
      Bool.false_eq_true, List.find?_cons_of_neg]
    exact ih

theorem exponentOf_eq_zero_iff {l : Bases} (name : String) :
  exponentOf name l = 0 ↔ ∀ b ∈ l, b.name ≠ name := by
  constructor
  · intro h
    induction l with
    | nil =>
        intro b hb; cases hb
    | cons x xs ih =>
        have hx : x.name ≠ name := by
          intro hx
          have h' := h
          simp [exponentOf, List.find?, hx] at h'
          exact x.not_zero h'
        have h_tail : exponentOf name xs = 0 := by
          simpa [exponentOf, List.find?, hx] using h
        intro b hb
        simp [List.mem_cons] at hb
        cases hb with
        | inl hb =>
            subst hb; exact hx
        | inr hb =>
            exact ih h_tail b hb
  · intro h
    exact exponentOf_eq_zero name h

theorem exponentOf_neq_zero_iff {l : Bases} (name : String) (h_sorted : Sorted l) :
  exponentOf name l ≠ 0 ↔ ∃ b ∈ l, b.name = name := by
  constructor
  · intro h
    have : ¬ (∀ b ∈ l, b.name ≠ name) := by
      intro all
      have hz : exponentOf name l = 0 :=
        (exponentOf_eq_zero_iff (l:=l) name).mpr all
      contradiction
    push_neg at this
    assumption
  · intro ⟨b, hb_mem, hb_name⟩
    have hb' := exponentOf_eq_exp h_sorted b hb_mem
    have : exponentOf name l = b.exponent := by simpa [hb_name] using hb'
    simpa [this] using b.not_zero

theorem exponentOf_head {xs : Bases} {x : Base} (name : String) (h_sorted : Sorted (x::xs))
  (h : x.name = name) : exponentOf name (x::xs) = x.exponent := by
  have x_in_x_xs : x ∈ x :: xs := by simp
  have h_exp := exponentOf_eq_exp h_sorted x x_in_x_xs
  rw [h] at h_exp
  exact h_exp

theorem exponentOf_eq_imp_mem (l : Bases) (h_sorted : Sorted l) (b : Base)
  (h : exponentOf b.name l = b.exponent) : b ∈ l := by
  induction l with
  | nil =>
    unfold exponentOf at h
    simp at h
    exact False.elim (b.not_zero (by simp [h]))
  | cons x xs ih =>
    have h_tail_sorted : Sorted xs := by
      rw [Sorted.cons] at h_sorted
      exact h_sorted.2
    unfold exponentOf at h
    by_cases hname : x.name = b.name <;> simp [List.find?, hname] at h
    · have hb : x = b := (Base.eq_iff x b).mpr ⟨hname, h⟩
      simp [hb]
    · have hb_tail : b ∈ xs := ih h_tail_sorted h
      exact List.mem_cons_of_mem x hb_tail

theorem exponentOf_eq_iff (l₁ l₂ : Bases) (h₁ : Sorted l₁) (h₂ : Sorted l₂) :
  (∀ name , exponentOf name l₁ = exponentOf name l₂) ↔ l₁ = l₂ := by
  constructor
  · intro h
    apply Bases.eq_of_sorted_of_same_elements h₁ h₂
    intro b
    constructor
    · intro h_mem
      have : exponentOf b.name l₁ = b.exponent := exponentOf_eq_exp h₁ b h_mem
      rw [h b.name] at this
      exact exponentOf_eq_imp_mem l₂ h₂ b this
    · intro h_mem
      have : exponentOf b.name l₂ = b.exponent := exponentOf_eq_exp h₂ b h_mem
      rw [← h b.name] at this
      exact exponentOf_eq_imp_mem l₁ h₁ b this
  · intro h
    subst h
    intro name
    rfl

@[simp]
theorem exponentOf_cons_eq (x : Base) (xs : Bases) (name : String) (h : x.name = name) :
  exponentOf name (x::xs) = x.exponent := by
  simp only [exponentOf, List.find?, h, decide_true]

@[simp]
theorem exponentOf_cons_neq (x : Base) (xs : Bases) (name : String) (h : x.name ≠ name) :
  exponentOf name (x::xs) = exponentOf name xs := by
  simp only [exponentOf, List.find?, h, decide_false]

/-- empty merge is identity -/
@[simp]
theorem merge_nil_self_eq_self (l : Bases) : merge [] l = l := by
  simp only [merge]

/-- merge with empty list is identity -/
@[simp]
theorem merge_self_nil_eq_self (l : Bases) : merge l [] = l := by
  unfold merge
  aesop

theorem merge_cons_no_dup (b₁ b₂ l₁ l₂) (h_no_dup : b₁.name ≠ b₂.name) : merge (b₁::l₁) (b₂::l₂) =
  if b₁.name < b₂.name then b₁ :: merge l₁ (b₂::l₂) else b₂ :: merge (b₁::l₁) l₂ := by
  simp only [merge, ↓reduceIte, h_no_dup]

@[simp]
theorem merge_cons_lower (b₁ b₂ l₁ l₂)
  (h_no_dup : b₁.name ≠ b₂.name)
  (h_lower : b₁.name < b₂.name) :
  merge (b₁::l₁) (b₂::l₂) = b₁ :: merge l₁ (b₂::l₂) := by
  rw [merge_cons_no_dup, if_pos h_lower]
  exact h_no_dup

@[simp]
theorem merge_cons_upper (b₁ b₂ l₁ l₂)
  (h_no_dup : b₁.name ≠ b₂.name)
  (h_upper : ¬ b₁.name < b₂.name) :
  merge (b₁::l₁) (b₂::l₂) = b₂ :: merge (b₁::l₁) l₂ := by
  rw [merge_cons_no_dup, if_neg h_upper]
  exact h_no_dup

theorem merge_one_cons (b₁ b₂ l₂) (h_no_dup : b₁.name ≠ b₂.name) :
  merge [b₁] (b₂::l₂) =
    if b₁.name < b₂.name then
      b₁ :: b₂ :: l₂
    else
      b₂ :: merge [b₁] l₂ := by
  simp only [merge, ↓reduceIte, h_no_dup]

theorem merge_mem (l₁ l₂ : Bases) (b : Base) :
  b ∈ merge l₁ l₂ →
    (∃ b', (b' ∈ l₁ ∨ b' ∈ l₂) ∧ b'.exponent = b.exponent ∧
    b'.name = b.name)
    ∨
    (∃ b₁ b₂, b₁ ∈ l₁ ∧ b₂ ∈ l₂ ∧ b₁.exponent + b₂.exponent = b.exponent ∧
    b₁.name = b.name ∧
    b₂.name = b.name) := by
  induction l₁ generalizing l₂ with
  | nil => aesop
  | cons x xs xh =>
    induction l₂ with
    | nil => aesop
    | cons y ys yh =>
      unfold merge
      by_cases h : x.name = y.name
      -- x.name = y.name
      · cases h_base_merge: Base.merge x.name x.exponent y.exponent with
        | none =>
          specialize xh ys
          simp only [h, if_pos]
          intro h_b_in_merge
          have h_exp := xh h_b_in_merge
          cases h_exp with
          | inl h_either =>
            obtain ⟨b', h_b'_in_xs|h_b'_in_ys, h_name⟩ := h_either
            · left
              use b'
              constructor
              · left
                exact List.mem_cons_of_mem x h_b'_in_xs
              · exact h_name
            · left
              use b'
              constructor
              · right
                exact List.mem_cons_of_mem y h_b'_in_ys
              · exact h_name
          | inr h_b_sum =>
            obtain ⟨b₁, b₂, h_b₁_in_xs, h_b₂_in_ys, h_sum⟩ := h_b_sum
            right
            use b₁, b₂
            constructor
            · exact List.mem_cons_of_mem x h_b₁_in_xs
            · constructor
              · exact List.mem_cons_of_mem y h_b₂_in_ys
              · exact h_sum
        | some z =>
          rw [if_pos h, List.mem_cons]
          intro h_b_in_merge
          cases h_b_in_merge with
          | inl h_b_eq_z =>
            have h_z_exp := Base.merge.eq_some_imp_exponent_eq_add x.name x.exponent y.exponent z
            have h_z_name := Base.merge.eq_some_imp_name_eq x.name x.exponent y.exponent z
            right
            use x, y
            constructor
            · exact List.mem_cons_self
            · constructor
              · exact List.mem_cons_self
              · rw [h_b_eq_z]
                constructor
                · exact Eq.symm (h_z_exp h_base_merge)
                · constructor
                  · exact Eq.symm (h_z_name h_base_merge)
                  · rw [← h]; exact Eq.symm (h_z_name h_base_merge)
          | inr h_b_in_merge =>
            specialize xh ys
            have h_exp := xh h_b_in_merge
            cases h_exp with
            | inl h_either =>
              obtain ⟨b', h_b'_in_xs|h_b'_in_ys, h_name⟩ := h_either
              · left
                use b'
                constructor
                · left
                  exact List.mem_cons_of_mem x h_b'_in_xs
                · exact h_name
              · left
                use b'
                constructor
                · right
                  exact List.mem_cons_of_mem y h_b'_in_ys
                · exact h_name
            | inr h_b_sum =>
              obtain ⟨b₁, b₂, h_b₁_in_xs, h_b₂_in_ys, h_sum⟩ := h_b_sum
              right
              use b₁, b₂
              constructor
              · exact List.mem_cons_of_mem x h_b₁_in_xs
              · constructor
                · exact List.mem_cons_of_mem y h_b₂_in_ys
                · exact h_sum
      -- x.name ≠ y.name
      · by_cases h_lt : x.name < y.name
        -- x.name < y.name
        · simp only [if_neg h, if_pos h_lt, List.mem_cons]
          intro h_b_in_merge
          cases h_b_in_merge with
          | inl h_b_eq_x =>
            left
            use x
            constructor
            · left; left; rfl
            · rw [h_b_eq_x]
              constructor <;> rfl
          | inr h_b_in_merge =>
            specialize xh (y :: ys)
            apply xh at h_b_in_merge
            cases h_b_in_merge with
            | inl h_either =>
              obtain ⟨b', h_b'_in_xs|h_b'_in_ys, h_name⟩ := h_either
              · left
                use b'
                constructor
                · left; right; assumption
                · exact h_name
              · left
                use b'
                constructor
                · right; rw [List.mem_cons] at h_b'_in_ys; assumption
                · exact h_name
            | inr h_b_sum =>
              obtain ⟨b₁, b₂, h_b₁_in_xs, h_b₂_in_ys, h_sum⟩ := h_b_sum
              right
              use b₁, b₂
              constructor
              · right; exact h_b₁_in_xs
              · constructor
                · rw [List.mem_cons] at h_b₂_in_ys
                  exact h_b₂_in_ys
                · exact h_sum
        -- x.name > y.name
        · simp only [if_neg h, if_neg h_lt]
          intro h_b_in_merge
          rw [List.mem_cons] at h_b_in_merge
          cases h_b_in_merge with
          | inl h_b_eq_y =>
            left
            use y
            constructor
            · right; exact List.mem_cons_self
            · rw [h_b_eq_y]
              constructor <;> rfl
          | inr h_b_in_merge =>
            apply yh at h_b_in_merge
            cases h_b_in_merge with
            | inl h_either =>
              obtain ⟨b', h_b'_in_x_xs|h_b'_in_ys, h_exp⟩ := h_either
              · rw [List.mem_cons] at h_b'_in_x_xs
                cases h_b'_in_x_xs with
                | inl h_b'_eq_x =>
                  left
                  use x
                  constructor
                  · left; exact List.mem_cons_self
                  · rw [←h_b'_eq_x]; exact h_exp
                | inr h_b'_in_xs =>
                  left
                  use b'
                  constructor
                  · left; exact List.mem_cons_of_mem x h_b'_in_xs
                  · exact h_exp
              · left
                use b'
                constructor
                · right; exact List.mem_cons_of_mem y h_b'_in_ys
                · exact h_exp
            | inr h_b_sum =>
              obtain ⟨b₁, b₂, h_b₁_in_xs, h_b₂_in_ys, h_sum⟩ := h_b_sum
              right
              use b₁, b₂
              constructor
              · exact h_b₁_in_xs
              · constructor
                · exact List.mem_cons_of_mem y h_b₂_in_ys
                · exact h_sum

/-- lemma about membership of merged bases, to handle sorted proof -/
theorem merge_mem_name (l₁ l₂ : Bases) (b : Base) :
  b ∈ merge l₁ l₂ → ∃ b', (b' ∈ l₁ ∨ b' ∈ l₂) ∧ b'.name = b.name := by
  have h := merge_mem l₁ l₂ b
  intro h_b
  specialize h h_b
  aesop

/-- Two merges of sorted exponent list are sorted -/
theorem merge_sorted (l₁ l₂ : Bases) (h₁ : Sorted l₁) (h₂ : Sorted l₂) : Sorted (merge l₁ l₂) := by
  induction l₁ generalizing l₂ with
  | nil => simp_all only [merge]
  | cons x xs xh =>
    induction l₂ with
    | nil => simp_all only [merge]
    | cons y ys yh =>
      unfold merge
      by_cases h : x.name = y.name
      -- x.name = y.name
      · cases h_base_merge: Base.merge x.name x.exponent y.exponent with
        | none =>
          have h_sorted: Sorted (merge xs ys) := by
            specialize xh ys
            rw [Sorted.cons] at h₁ h₂
            exact xh h₁.2 h₂.2
          simp only [h, if_pos, h_sorted]
        | some z =>
          have z_eq_x : z.name = x.name := by
            apply Base.merge.eq_some_imp_name_eq x.name x.exponent y.exponent
            exact h_base_merge
          have z_eq_y : z.name = y.name := by
            rw [h.symm]
            exact z_eq_x
          have h₃: Sorted (z :: xs) := by
            rw [name_eq_imp_sorted_iff_sorted xs z_eq_x]
            exact h₁
          have h₄ : Sorted (z :: ys) := by
            rw [name_eq_imp_sorted_iff_sorted ys z_eq_y]
            exact h₂
          simp only [h, if_pos]
          have h_sorted: Sorted (merge xs ys) := by
            specialize xh ys
            rw [Sorted.cons] at h₁ h₂
            exact xh h₁.2 h₂.2
          unfold Sorted at ⊢ h₃ h₄
          rw [List.pairwise_cons] at ⊢ h₃ h₄
          constructor
          · intro b h_b
            apply merge_mem_name at h_b
            obtain ⟨b', h_b', h_name⟩ := h_b
            cases h_b' with
            | inl h_b'_in_xs =>
              rw [←h_name]
              exact h₃.1 b' h_b'_in_xs
            | inr h_b'_in_ys =>
              rw [←h_name]
              exact h₄.1 b' h_b'_in_ys
          · exact h_sorted
      -- x.name ≠ y.name
      · by_cases h_lt : x.name < y.name
        -- x.name < y.name
        · simp [h, h_lt]
          rw [Sorted.cons]
          constructor
          · intro b h_b
            apply merge_mem_name at h_b
            obtain ⟨b', h_b', h_name⟩ := h_b
            cases h_b' with
            | inl h_b'_in_xs =>
              rw [←h_name]
              unfold Sorted at h₁
              rw [List.pairwise_cons] at h₁
              exact h₁.1 b' h_b'_in_xs
            | inr h_b'_in_y_ys =>
              rw [←h_name]
              unfold Sorted at h₂
              rw [List.pairwise_cons] at h₂
              rw [List.mem_cons] at h_b'_in_y_ys
              cases h_b'_in_y_ys with
              | inl h_b'_eq_y =>
                rw [h_b'_eq_y]
                exact h_lt
              | inr h_b'_in_ys =>
                apply lt_trans h_lt
                exact h₂.1 b' h_b'_in_ys
          · specialize xh (y :: ys)
            rw [Sorted.cons] at h₁
            exact xh h₁.2 h₂
        -- x.name > y.name
        · simp [h, h_lt]
          rw [Sorted.cons]
          constructor
          · intro b h_b
            apply merge_mem_name at h_b
            obtain ⟨b', h_b', h_name⟩ := h_b
            cases h_b' with
            | inl h_b'_in_x_xs =>
              have h_lt' : y.name < x.name := by
                exact lt_of_le_of_ne (le_of_not_gt h_lt) (Ne.symm h)
              rw [←h_name]
              unfold Sorted at h₁
              rw [List.pairwise_cons] at h₁
              rw [List.mem_cons] at h_b'_in_x_xs
              cases h_b'_in_x_xs with
              | inl h_b'_eq_x =>
                rw [h_b'_eq_x]
                exact h_lt'
              | inr h_b'_in_xs =>
                apply lt_trans h_lt'
                exact h₁.1 b' h_b'_in_xs
            | inr h_b'_in_ys =>
              rw [←h_name]
              unfold Sorted at h₂
              rw [List.pairwise_cons] at h₂
              exact h₂.1 b' h_b'_in_ys
          · rw [Sorted.cons] at h₂
            exact yh h₂.2

/-- Merge of two base lists are nodup -/
theorem merge_nodup (l₁ l₂ : Bases) (h₁ : Sorted l₁) (h₂ : Sorted l₂) : Nodup (merge l₁ l₂) :=
  sorted_imp_nodup (merge l₁ l₂) (merge_sorted l₁ l₂ h₁ h₂)

/--
If two lists of bases have no duplicated base names inter-between them,
then all their members are preserved when merging them.
This is not true in general, as merging two lists with the same base name
will result in a single base with the sum of their exponents.
-/
theorem merge_mem_no_dup (l₁ l₂ : Bases) (b : Base)
 (no_dup : ∀ b₁ b₂ : Base, b₁∈l₁ → b₂∈l₂ → b₁.name ≠ b₂.name) :
  b ∈ l₁ ∨ b ∈ l₂ ↔ b ∈ merge l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons x xs xh =>
      induction l₂ with
      | nil => simp
      | cons y ys yh =>
        have x_ne_y : x.name ≠ y.name := by simp [no_dup]
        specialize xh (y::ys)
        rw [merge_cons_no_dup x y xs ys x_ne_y]
        aesop


/-- Merges are commutative -/
theorem merge_comm (l₁ l₂ : Bases) : merge l₁ l₂ = merge l₂ l₁ := by
  induction l₁ generalizing l₂ with
   | nil => simp
   | cons x xs xh =>
      induction l₂ with
      | nil => simp
      | cons y ys yh =>
        unfold merge
        by_cases h : x.name = y.name
        · rw [Base.merge.comm, xh]
          simp only [h, if_pos]
        · have h₃ : y.name ≠ x.name := Ne.symm h
          by_cases h₄ : x.name < y.name
          · simp only [h, h₃, h₄, not_lt_of_gt, ↓reduceIte, xh]
          · simp only [h, h₃, h₄, lt_of_le_of_ne (le_of_not_gt h₄) h₃, ↓reduceIte, yh]

/--
Used to simplify proofs about merge associativity.
-/
theorem exponentOf_merge (l₁ l₂ : Bases) (h₁ : Sorted l₁) (h₂ : Sorted l₂) (name : String) :
    exponentOf name (merge l₁ l₂) = exponentOf name l₁ + exponentOf name l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp [exponentOf]
  | cons x xs IHxs =>
    induction l₂ with
    | nil =>
      simp [exponentOf]
    | cons y ys IHys =>
      obtain ⟨hx_min, hx_sorted⟩ := Sorted.cons.mp h₁
      obtain ⟨hy_min, hy_sorted⟩ := Sorted.cons.mp h₂
      unfold merge
      by_cases h : x.name = y.name
      · cases h_merge: Base.merge y.name x.exponent y.exponent with
        | none =>
          simp only [h, if_pos,h_merge]
          by_cases h_x_name : name = x.name
          · have h_y_name : name = y.name := by rw [h] at h_x_name; exact h_x_name
            rw [exponentOf_cons_eq x xs name h_x_name.symm]
            rw [exponentOf_cons_eq y ys name h_y_name.symm]
            rw [IHxs ys hx_sorted hy_sorted]
            have h_exp_xs_eq_zero: exponentOf name xs = 0 := by
              apply exponentOf_eq_zero
              intro b hb_in_xs
              have : x.name < b.name := hx_min b hb_in_xs
              rw [←h_x_name] at this
              exact Ne.symm (ne_of_lt this)
            have h_exp_ys_eq_zero: exponentOf name ys = 0 := by
              apply exponentOf_eq_zero
              intro b hb_in_ys
              have : y.name < b.name := hy_min b hb_in_ys
              rw [←h_y_name] at this
              exact Ne.symm (ne_of_lt this)
            rw [h_exp_xs_eq_zero, h_exp_ys_eq_zero, add_zero]
            exact Eq.symm ((Base.merge.eq_none_iff y.name x.exponent y.exponent).mp h_merge)
          · rw [exponentOf_cons_neq x xs name (Ne.symm h_x_name)]
            rw [exponentOf_cons_neq y ys name (by rw [←h]; exact Ne.symm h_x_name)]
            exact IHxs ys hx_sorted hy_sorted
        | some z =>
          simp only [h, if_pos,h_merge]
          have z_eq_x : z.name = x.name := by
            apply Base.merge.eq_some_imp_name_eq x.name x.exponent y.exponent z
            rw [h]
            exact h_merge
          by_cases h_x_name : name = x.name
          · have h_y_name : name = y.name := by rw [h] at h_x_name; exact h_x_name
            have h_z_name : name = z.name := by rw [h_x_name]; exact z_eq_x.symm
            rw [exponentOf_cons_eq x xs name h_x_name.symm]
            rw [exponentOf_cons_eq y ys name h_y_name.symm]
            rw [exponentOf_cons_eq z (merge xs ys) name h_z_name.symm]
            exact Base.merge.eq_some_imp_exponent_eq_add y.name x.exponent y.exponent z h_merge
          · rw [exponentOf_cons_neq x xs name (Ne.symm h_x_name)]
            rw [exponentOf_cons_neq y ys name (by rw [←h]; exact Ne.symm h_x_name)]
            rw [← z_eq_x] at h_x_name
            rw [exponentOf_cons_neq z (merge xs ys) name (Ne.symm h_x_name)]
            exact IHxs ys hx_sorted hy_sorted
      · by_cases hlt : x.name < y.name
        · simp [h, hlt]
          by_cases h_x_name : name = x.name
          · rw [exponentOf_cons_eq x xs name h_x_name.symm]
            have h_neq_y : name ≠ y.name := by
              rw [h_x_name]
              exact h
            rw [exponentOf_cons_neq y ys name h_neq_y.symm]
            rw [exponentOf_cons_eq x (merge xs (y::ys)) name h_x_name.symm]
            have h_exp_ys_eq_zero: exponentOf name ys = 0 := by
              apply exponentOf_eq_zero
              intro b hb_in_ys
              have : name < b.name := by
                calc name = x.name := h_x_name
                  _ < y.name := hlt
                  _ < b.name := hy_min b hb_in_ys
              exact Ne.symm (ne_of_lt this)
            rw [h_exp_ys_eq_zero, add_zero]
          · rw [exponentOf_cons_neq x xs name (Ne.symm h_x_name)]
            rw [exponentOf_cons_neq x (merge xs (y::ys)) name (Ne.symm h_x_name)]
            exact IHxs (y::ys) hx_sorted (Sorted.cons.mpr ⟨hy_min, hy_sorted⟩)
        · simp [h, hlt]
          by_cases h_y_name : name = y.name
          · rw [exponentOf_cons_eq y ys name h_y_name.symm]
            have h_neq_x : name ≠ x.name := by
              rw [h_y_name]
              exact Ne.symm h
            rw [exponentOf_cons_neq x xs name h_neq_x.symm]
            rw [exponentOf_cons_eq y (merge (x::xs) ys) name h_y_name.symm]
            have h_exp_xs_eq_zero: exponentOf name xs = 0 := by
              apply exponentOf_eq_zero
              intro b hb_in_xs
              have : name < b.name := by
                calc name = y.name := h_y_name
                  _ ≤ x.name := le_of_not_gt hlt
                  _ < b.name := hx_min b hb_in_xs
              exact Ne.symm (ne_of_lt this)
            rw [h_exp_xs_eq_zero, zero_add]
          · rw [exponentOf_cons_neq y ys name (Ne.symm h_y_name)]
            rw [exponentOf_cons_neq y (merge (x::xs) ys) name (Ne.symm h_y_name)]
            exact IHys hy_sorted

/-- Merges are associative for sorted lists. -/
theorem merge_assoc (l₁ l₂ l₃ : Bases)
    (h₁ : Sorted l₁) (h₂ : Sorted l₂) (h₃ : Sorted l₃) :
    merge (merge l₁ l₂) l₃ = merge l₁ (merge l₂ l₃) := by
  have sorted12 := merge_sorted l₁ l₂ h₁ h₂
  have sorted23 := merge_sorted l₂ l₃ h₂ h₃
  have left_sorted := merge_sorted (merge l₁ l₂) l₃ sorted12 h₃
  have right_sorted := merge_sorted l₁ (merge l₂ l₃) h₁ sorted23
  apply (exponentOf_eq_iff (merge (merge l₁ l₂) l₃) (merge l₁ (merge l₂ l₃))
        left_sorted right_sorted).mp
  intro name
  have h_left := exponentOf_merge (merge l₁ l₂) l₃ sorted12 h₃ name
  have h_right := exponentOf_merge l₁ (merge l₂ l₃) h₁ sorted23 name
  have h12 := exponentOf_merge l₁ l₂ h₁ h₂ name
  have h23 := exponentOf_merge l₂ l₃ h₂ h₃ name
  simp [h12, h23] at h_left h_right
  rw [h_left, h_right]
  rw [add_assoc]

end Units.Dimension.Bases
