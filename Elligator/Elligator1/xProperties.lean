/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Elligator.FiniteFieldBasic
public import Elligator.LegendreSymbol
public import Elligator.EdwardsCurve
public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.sProperties
public import Elligator.Elligator1.cProperties
public import Elligator.Elligator1.uProperties
public import Elligator.Elligator1.vProperties
public import Elligator.Elligator1.XProperties
public import Elligator.Elligator1.YProperties

@[expose] public section

/-!
# x Variable Properties

In this file we introduce some generally helpful lemmas for `x` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section xProperties

variable {F : Type*} [Field F] [Fintype F]

lemma x_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  x_of_t ≠ (0 : F) := by
    let c_of_s := c s
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change (c_of_s - 1) * s * X_of_t * (1 + X_of_t) / Y_of_t ≠ 0
    apply div_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · intro h1
            have h1_1 : c_of_s = 1 := by
              rw [← add_left_inj 1] at h1
              rw [zero_add] at h1
              have h1_1_1 : (1 : F) - (1 : F) = 0 := by ring
              rw [add_comm] at h1
              rw [← add_sub_assoc] at h1
              rw [add_comm 1 c_of_s] at h1
              rw [add_sub_assoc] at h1
              rw [h1_1_1, add_zero] at h1
              exact h1
            have h1_2 : c_of_s ≠ 1 := c_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
            contradiction
          · apply s_h1
        · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
      · apply one_add_X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

lemma x_comparison
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let x1 := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  x2 = x1 := by
    intro t1 t2 h2_2 x1 x2
    let c_of_s := c s
    let r_of_s := r s
    let X1 := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y1 := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y2 := Y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have X_pow_three_ne_zero : X1^3 ≠ 0 := by
      apply pow_ne_zero 3 (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)
    calc
      x2 = (c_of_s - 1) * s * X2 * (1 + X2) / Y2 := by
        change (c_of_s - 1) * s * X2 * (1 + X2) / Y2 = (c_of_s - 1) * s * X2 * (1 + X2) / Y2
        rfl
      _ = (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1^3) := by
        unfold X2
        rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        unfold Y2
        rw [Y_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        change (c_of_s - 1) * s * (1 / X1) * (1 + 1 / X1) / (Y1 / X1^3) = (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1 ^ 3)
        ring_nf
      _ = (c_of_s - 1) * s * X1 * (1 + X1) / Y1 := by
        have h2_12_1 : X1^3 / X1^3 = 1 := by
          apply div_self X_pow_three_ne_zero
        rw [← mul_one ((c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1 ^ 3))]
        nth_rw 5 [← h2_12_1]
        rw [← mul_div_mul_comm]
        have h2_12_2 : (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) * X1 ^ 3 = (c_of_s - 1) * s * X1 * (1 + X1) := by
          calc
            (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) * X1 ^ 3 = (c_of_s - 1) * s * X1^3 / X1 * (1 + 1 / X1) := by
              repeat rw [mul_assoc]
              rw [mul_comm (1 + 1 / X1) (X1^3)]
              rw [← mul_assoc]
              rw [← mul_assoc, mul_one, div_mul_eq_mul_div]
              ring_nf
            _ = (c_of_s - 1) * s * X1^2 * (1 + 1 / X1) := by
              have h2_12_2_1 : X1^3 = X1^2 * X1 := by ring_nf
              rw [h2_12_2_1, mul_div_assoc, mul_div_assoc]
              rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
              rw [mul_one]
            _ = (c_of_s - 1) * s * X1 * (1 + X1) := by
              have h2_12_2_1 : X1^2 * (1 + 1 / X1) = X1 * (1 + X1) := by
                rw [pow_two, mul_assoc, mul_add, ← mul_div_assoc]
                rw [mul_one]
                rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
                nth_rw 1 [add_comm]
              rw [mul_assoc ((c_of_s - 1) * s), h2_12_2_1]
              repeat rw [← mul_assoc]
        have h2_12_3 : (Y1 / X1 ^ 3 * X1 ^ 3) = Y1 := by
          rw [mul_comm, ← mul_div_assoc, mul_comm]
          rw [mul_div_assoc, div_self X_pow_three_ne_zero]
          simp
        rw [h2_12_2, h2_12_3]
      _ = x1 := by
        unfold x1 x
        simp
        rfl

lemma x_y_eq_zero_sign_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (x_eq_zero : point.val.1 = 0)
  :
  point.val = ((0 : F), (1 : F)) ∨ point.val = ((0 : F), (-1 : F)) := by
    let d_of_s := d s
    let x := point.val.1
    let y := point.val.2
    unfold E_over_F at point
    change (x, y) = (0, 1) ∨ (x, y) = (0, -1)
    change x = 0 at x_eq_zero
    rw [← x_eq_zero]
    have h1 : x^2 + y^2 = 1 + d_of_s * x^2 * y^2 := by
      exact point.prop
    rw [x_eq_zero] at h1
    simp at h1
    rcases h1 with h | h
    · rw [← h]
      left
      rfl
    · rw [← h]
      right
      rfl
