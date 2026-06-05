import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open BigOperators

theorem prime_outside_finset (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∃ p, Nat.Prime p ∧ p ∉ S := by

  set N := S.prod (fun p => p) + 1 with hN_def

  -- Every prime in S is at least 1
  -- → their product is at least 1
  -- → therefore product + 1 ≥ 2
  have hN_ge : N ≥ 2 := by
    rw [hN_def]
    apply Nat.succ_le_succ
    apply Finset.one_le_prod
    intro p hp
    exact (hS p hp).one_le

  -- Any natural number > 1 has a prime divisor
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hN_ge)

  -- let q be the prime, prove q ∉ S
  refine ⟨q, hq_prime, ?_⟩
  -- assume q ∈ S, prove contradiction
  intro hq_in_S

  -- if a number appears as a factor in a product
  -- then it divides the product
  have hq_dvd_prod : q ∣ S.prod (fun p => p) :=
    Finset.dvd_prod_of_mem (fun p => p) hq_in_S

  -- prove that q ∣ 1
  -- since q ∣ product ∧ q ∣ product + 1
  -- → q ∣ 1
  have hq_dvd_one : q ∣ 1 := by
    rw [hN_def] at hq_dvd
    exact (Nat.dvd_add_right hq_dvd_prod).mp hq_dvd

  -- Every prime natural number is ≥ 2
  have hq_ge : q ≥ 2 := hq_prime.two_le
  -- Since q ∣ 1 → q ≤ 1 → contradiction
  have : q ≤ 1 := Nat.le_of_dvd (by norm_num) hq_dvd_one
  omega
