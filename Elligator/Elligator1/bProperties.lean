/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Elligator.FiniteFieldBasic
public import Elligator.Elligator1.Variables

@[expose] public section

/-!
# b Properties

In this file we introduce some generally helpful lemmas for `b`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

-- Original-Reference: Theorem 4
section bProperties

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

lemma two_pow_b_le_q (q_mod_4_congruent_3 : q % 4 = 3) : 2^(@b q) ≤ q := by
    apply Nat.pow_log_le_self
    grind

lemma q_lt_two_pow_b_succ : q < 2^((@b q) + 1) :=
  Nat.lt_pow_succ_log_self (by decide) _

lemma two_pow_b_gt_q_over_two
  (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)
  :
  2^(@b q) > q / 2 := by
    let h1 := two_pow_b_le_q q_mod_4_congruent_3
    let h2 := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold b
    let h3 := @q_lt_two_pow_b_succ q
    have h4 : 2^(@b q) > q / 2 ↔ q < 2^((@b q) + 1) := by grind
    apply h4.mpr
    grind

lemma half_q_lt_two_pow_b :
    (q - 1) / 2 < 2^(@b q) := by
      rw [ Nat.div_lt_iff_lt_mul (by norm_num), mul_comm];
      rw [← pow_succ']
      apply lt_of_le_of_lt (Nat.sub_le _ _)
      exact Nat.lt_pow_succ_log_self (by norm_num) q
