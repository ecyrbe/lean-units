import Mathlib.Data.Nat.Basic
import Batteries.WF



namespace Units
variable {m n k : ℕ} {p q : ℕ → Prop}

namespace NatFind

/-! ### `Nat.find` -/

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

private def wf_lbp : WellFounded (@lbp p) :=
  ⟨let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc lbp k from fun _ => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun _ kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

/-- Find the smallest `n` satisfying `p n`. Returns a subtype. -/
private def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  go H 0 fun _ h => absurd h (Nat.not_lt_zero _)
where
  go (H : ∃ n, p n) (k : Nat) (hk : ∀ n < k, ¬p n) : { n // p n ∧ ∀ m < n, ¬p m } :=
    if pk : p k then ⟨k, pk, hk⟩
    else
      have : ∀ n ≤ k, ¬p n := fun n h =>
        Or.elim (Nat.lt_or_eq_of_le h) (hk n) fun e => by rw [e]; exact pk
      go H (k + 1) fun n h => this n <| Nat.le_of_succ_le_succ h
  termination_by (wf_lbp H).wrap k
  decreasing_by exact ⟨rfl, this⟩

/--
Alternative definition of `Nat.find` using tail recursion.
-/
def find : ℕ :=
  (findX H).1

theorem find_spec : p (find H) :=
  (findX H).2.left


end NatFind

end Units
