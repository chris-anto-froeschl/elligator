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

See [bernstein2013a] chapter 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

@[blueprint "lemma:c_ne_zero"]
lemma c_ne_zero
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : (c s) ≠ 0 := by
    change 2 / s^2 ≠ 0
    apply div_ne_zero
    · apply two_ne_zero q_h1 q_h2 q_h3
    · rw [pow_two]
      apply mul_ne_zero s_h1 s_h1

omit [Fintype F] in
@[blueprint "lemma:c_ne_one"]
lemma c_ne_one (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) ≠ 1 := by
  change 2 / s^2 ≠ 1
  apply div_ne_one_of_ne
  apply Ne.symm
  apply s_pow_two_ne_two s_h2

omit [Fintype F] in
@[blueprint "lemma:c_ne_neg_one"]
lemma c_ne_neg_one (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) ≠ -1 := by
  change 2 / s^2 ≠ -1
  intro h
  have h' : s^2 = -2 := by grind
  apply s_pow_two_ne_neg_two s_h2 at h'
  exact h'

omit [Fintype F] in
@[blueprint "lemma:c_add_one_ne_zero"]
lemma c_add_one_ne_zero (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) + 1 ≠ 0 := by
  intro h
  change 2 / s^2 + 1 = 0 at h
  have h1 : (-1 : F) + 1 = 0 := by norm_num
  rw [← h1] at h
  apply add_right_cancel_iff.1 at h
  have h2 : s^2 = -2 := by grind
  apply s_pow_two_ne_neg_two s_h2 at h2
  exact h2

omit [Fintype F] in
@[blueprint "lemma:c_sub_one_ne_zero"]
lemma c_sub_one_ne_zero (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) - 1 ≠ 0 := by
  apply sub_ne_zero.2
  exact c_ne_one s_h2

@[blueprint "lemma:c_h"]
lemma c_h
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let c := c s
  c * (c - 1) * (c + 1) ≠ 0 := by
    change (2 / s^2) * ((2 / s^2) - 1) * ((2 / s^2) + 1) ≠ 0
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact c_ne_zero s_h1 q_h1 q_h2 q_h3
      · exact c_sub_one_ne_zero s_h2
    · exact c_add_one_ne_zero s_h2

@[blueprint "lemma:c_pow_two_ne_zero"]
lemma c_pow_two_ne_zero
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : (c s)^2 ≠ (0 : F) := by
    rw [pow_two]
    apply mul_ne_zero
    · exact (c_ne_zero s_h1 q_h1 q_h2 q_h3)
    · exact (c_ne_zero s_h1 q_h1 q_h2 q_h3)

@[blueprint "lemma:s_pow_two_eq_two_over_c"]
lemma s_pow_two_eq_two_over_c
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : s^2 = 2 / (c s) := by
    change s^2 = 2 / (2 / s^2)
    ring_nf
    rw [inv_inv]
    rw [mul_assoc]
    rw [inv_mul_cancel₀ (two_ne_zero q_h1 q_h2 q_h3), mul_one]

end Elligator.Elligator1
