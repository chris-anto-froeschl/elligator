/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.sProperties

/-!
# c Variable Properties

In this file we introduce some generally helpful lemmas for `c` as introduced
in `Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma c_ne_zero
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (c s) ≠ 0 := by
    change 2 / s^2 ≠ 0
    apply div_ne_zero
    · apply two_ne_zero hq_card hq_mod
    · rw [pow_two]
      apply mul_ne_zero hs_ne_zero hs_ne_zero

omit [Fintype F] in
lemma c_ne_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) ≠ 1 := by
  change 2 / s^2 ≠ 1
  apply div_ne_one_of_ne
  apply Ne.symm
  apply s_pow_two_ne_two sq_ne_pm_two

omit [Fintype F] in
lemma c_ne_neg_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) ≠ -1 := by
  change 2 / s^2 ≠ -1
  intro h
  have h' : s^2 = -2 := by grind
  apply s_pow_two_ne_neg_two sq_ne_pm_two at h'
  exact h'

omit [Fintype F] in
lemma c_add_one_ne_zero (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) + 1 ≠ 0 := by
  intro h
  change 2 / s^2 + 1 = 0 at h
  have h1 : (-1 : F) + 1 = 0 := by norm_num
  rw [← h1] at h
  apply add_right_cancel_iff.1 at h
  have h2 : s^2 = -2 := by grind
  apply s_pow_two_ne_neg_two sq_ne_pm_two at h2
  exact h2

omit [Fintype F] in
lemma c_sub_one_ne_zero (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) - 1 ≠ 0 := by
  apply sub_ne_zero.2
  exact c_ne_one sq_ne_pm_two

@[blueprint "lemma:c_h"
  (title := "$c(c - 1)(c + 1) \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $c = 2/s^2$ satisfies
  $$
  c(c - 1)(c + 1) \neq 0 .
  $$
  -/)]
lemma c_h
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let c := c s
  c * (c - 1) * (c + 1) ≠ 0 := by
    change (2 / s^2) * ((2 / s^2) - 1) * ((2 / s^2) + 1) ≠ 0
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact c_ne_zero hs_ne_zero hq_card hq_mod
      · exact c_sub_one_ne_zero sq_ne_pm_two
    · exact c_add_one_ne_zero sq_ne_pm_two

lemma s_pow_two_eq_two_div_c
  (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) : s^2 = 2 / (c s) := by
  change s^2 = 2 / (2 / s^2)
  ring_nf
  rw [inv_inv, mul_assoc]
  rw [inv_mul_cancel₀ (two_ne_zero hq_card hq_mod), mul_one]

end Elligator.Elligator1
