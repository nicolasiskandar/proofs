import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

theorem pigeonhole_using_mathlib {α β : Type}
  [Fintype α] [Fintype β]
  (f : α → β)
  (h : Fintype.card β < Fintype.card α) :
  ∃ x y : α, x ≠ y ∧ f x = f y := by
  exact Fintype.exists_ne_map_eq_of_card_lt (α := α) (β := β) f h


open Finset

theorem pigeonhole_manual {α β : Type}
  [Fintype α] [Fintype β]
  (f : α → β)
  (h : Fintype.card β < Fintype.card α) :
  ∃ x y : α, x ≠ y ∧ f x = f y := by

  classical

  -- assume the opposite no collision
  by_contra hf

  -- derive ¬collision → injective
  have inj : Function.Injective f := by
    intro x y hxy -- x y : α, hxy : f x = f y
    by_contra hne -- assume the opposite → x ≠ y
    have := hf ⟨x, y, hne, hxy⟩ -- so there exists a collision
    exact this -- Hence f is injective

  -- injective function from α → β implies card α ≤ card β
  -- derive cardinality constraint
  have hcard : Fintype.card α ≤ Fintype.card β :=
    Fintype.card_le_of_injective f inj

  -- contradiction
  exact (not_lt_of_ge hcard) h
