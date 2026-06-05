import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open BigOperators

theorem sum_range_id (n : ℕ) :
  ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
    induction n with
    | zero => norm_num
    -- ih = induction hypothesis
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring_nf -- expand everything and put it into a canonical algebraic form
      omega
