/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables

/-!
# b Properties

In this file we introduce some generally helpful lemmas for `b`.

## References

See [Bernstein2013a], Section 3.4, Theorem 4.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

@[blueprint "lemma:two_pow_b_le_q"
  (title := "$2 ^ b \\leq q$")
  (statement := /--
  With $b = \lfloor \log_2 q \rfloor$ we have $2 ^ b \leq q$; hence the integers
  $0, 1, \ldots, 2 ^ b - 1$ are distinct in $\mathbb{F}_q$.
  -/)]
lemma two_pow_b_le_q (hq_mod : q % 4 = 3) : 2 ^ (@b q) ≤ q := by
  apply Nat.pow_log_le_self
  intro hqzero
  rw [hqzero] at hq_mod
  contradiction

lemma q_lt_two_pow_b_succ : q < 2 ^ ((@b q) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

lemma two_pow_b_gt_q_div_two : 2 ^ (@b q) > q / 2 := by
  have h_lt : q < 2 ^ ((@b q) + 1) := q_lt_two_pow_b_succ
  have h_double : 2 ^ ((@b q) + 1) = 2 * 2 ^ (@b q) := pow_succ' 2 _
  omega

lemma half_q_lt_two_pow_b : (q - 1) / 2 < 2 ^ (@b q) := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num), mul_comm]
  rw [← pow_succ']
  apply lt_of_le_of_lt (Nat.sub_le _ _)
  exact Nat.lt_pow_succ_log_self (by norm_num) q

end Elligator.Elligator1
