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
public import Elligator.Elligator1.dProperties
public import Elligator.Elligator1.uProperties
public import Elligator.Elligator1.vProperties
public import Elligator.Elligator1.XProperties
public import Elligator.Elligator1.YProperties
public import Elligator.Elligator1.xProperties

@[expose] public section

/-!
# y Variable Properties

In this file we introduce some generally helpful lemmas for `y` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section yProperties

variable {F : Type*} [Field F] [Fintype F]

-- Chapter 3.2 Theorem 1
lemma Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  Y_of_t ^2 = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t := by
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let v_ne_zero := v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    intro r_of_s X_of_t Y_of_t
    have h1 : X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t = χ_of_v_of_t * v_of_t := by
      calc
      X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t) := by
        change (χ_of_v_of_t * u_of_t) ^ 5 + (r_of_s ^ 2 - 2) * (χ_of_v_of_t * u_of_t) ^ 3 + (χ_of_v_of_t * u_of_t) = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t)
        rw [mul_pow (χ_of_v_of_t) (u_of_t) 5]
        rw [mul_pow (χ_of_v_of_t) (u_of_t) 3]
        have h1_1 : Odd 5 := by
          apply Nat.odd_iff.2
          norm_num
        have h1_2 : Odd 3 := by
          apply Nat.odd_iff.2
          norm_num
        rw [LegendreSymbol.χ_of_a_pow_n_eq_χ_a v_of_t ⟨5, h1_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3]
        rw [LegendreSymbol.χ_of_a_pow_n_eq_χ_a v_of_t ⟨3, h1_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3]
        change χ_of_v_of_t * u_of_t^5 + (r_of_s ^ 2 - 2) * (χ_of_v_of_t * u_of_t^3) + (χ_of_v_of_t * u_of_t) = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t)
        ring_nf
      _ = χ_of_v_of_t * v_of_t := by
        change χ_of_v_of_t * v_of_t = χ_of_v_of_t * v_of_t
        rfl
    have h2 := LegendreSymbol.χ_a_mul_a_IsSquare v_of_t v_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    have h3 : (χ_of_v_of_t * v_of_t)^((q + 1) / 2) = χ_of_v_of_t * v_of_t := by
      apply LegendreSymbol.square_of_a ⟨(χ_of_v_of_t * v_of_t), h2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_sum := LegendreSymbol.χ (u_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3
    have h4 : Y_of_t^2 = χ_of_v_of_t * v_of_t := by
      calc
        Y_of_t^2 = (χ_of_v_of_t * v_of_t)^((q + 1) / 2) * χ_of_v_of_t^2 * χ_of_sum^2 := by
          change ((χ_of_v_of_t * v_of_t)^((q + 1) / 4) * χ_of_v_of_t * χ_of_sum)^2 = (χ_of_v_of_t * v_of_t)^((q + 1) / 2) * χ_of_v_of_t^2 * χ_of_sum^2
          ring_nf
          rw [← field_cardinality]
          rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two q field_cardinality q_mod_4_congruent_3]
        _ = (χ_of_v_of_t * v_of_t)^((q + 1) / 2) * 1 := by
          rw [LegendreSymbol.χ_of_a_even_pow_n_eq_one v_of_t v_ne_zero ⟨2, even_two⟩ q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_of_a_even_pow_n_eq_one (u_of_t^2 + 1 / c_of_s^2) (v_h1_third_factor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t) ⟨2, even_two⟩ q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [mul_one]
        _ = χ_of_v_of_t * v_of_t := by rw [h3, mul_one]
    rw [h1]
    exact h4

lemma y_divisor_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  (r_of_s * X_of_t + (1 + X_of_t)^2) ≠ 0 := by
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    intro r_of_s
    intro X_of_t
    intro h
    have h1 : r_of_s * X_of_t = -(1 + X_of_t)^2 := by
      rw [← add_left_inj ((1 + X_of_t)^2)]
      have h1_1 : -((1 + X_of_t)^2) + ((1 + X_of_t)^2) = 0 := by
        rw [neg_add_eq_zero.2]
        ring
      rw [h1_1]
      exact h
    have h2 : (r_of_s^2 + 4 * r_of_s) * X_of_t^2 = X_of_t^4 - 2 * X_of_t^2 + 1 := by
      ring_nf
      repeat rw [pow_two]
      repeat rw [← mul_assoc]
      rw [mul_assoc r_of_s r_of_s X_of_t]
      nth_rw 2 [mul_comm r_of_s X_of_t]
      rw [← mul_assoc]
      rw [h1]
      rw [mul_assoc (-(1 + X_of_t)^2) r_of_s X_of_t]
      rw [h1]
      grind
    have h3 : Y_of_t^2 = -(1 + X_of_t)^2 * X_of_t^2 * (s + 2 / s)^2 := by
      calc
        Y_of_t^2 = X_of_t * (X_of_t^4 + (r_of_s^2 - 2) * X_of_t^2 + 1) := by
          rw [mul_add, mul_one]
          rw [mul_add]
          rw [Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
          ring_nf
          change X_of_t - X_of_t ^ 3 * 2 + X_of_t ^ 3 * r_of_s ^ 2 + X_of_t ^ 5 = X_of_t - X_of_t ^ 3 * 2 + X_of_t ^ 3 * r_of_s ^ 2 + X_of_t ^ 5
          rfl
        _ = X_of_t^3 * (2 * r_of_s^2 + 4 * r_of_s) := by
          rw [sub_mul (r_of_s^2) 2 (X_of_t^2)]
          nth_rw 1 [pow_two]
          nth_rw 1 [pow_two]
          rw [← mul_assoc, mul_assoc r_of_s r_of_s X_of_t, mul_comm r_of_s X_of_t]
          rw [← mul_assoc]
          rw [h1, mul_assoc (-(1 + X_of_t)^2) r_of_s X_of_t, h1]
          rw [← neg_one_mul]
          have h3_1 : (-1 : F) * (-1) = 1 := by ring
          nth_rw 1 [mul_comm (-1) ((1 + X_of_t)^2), ← mul_assoc, mul_assoc ((1 + X_of_t)^2) (-1) (-1)]
          rw [h3_1, mul_one]
          have h3_2 : 2 + 2 = 4 := by norm_num
          rw [← pow_add (1 + X_of_t) 2 2]
          rw [h3_2]
          rw [← add_sub_assoc, add_comm (X_of_t^4) ((1 + X_of_t)^4)]
          rw [add_sub_assoc ((1 + X_of_t)^4) (X_of_t^4)]
          rw [add_assoc ((1 + X_of_t)^4) (X_of_t^4 - 2 * X_of_t^2) (1 : F)]
          rw [← h2]
          have h3_3 : -r_of_s * X_of_t = (1 + X_of_t)^2 := by
            rw [← neg_one_mul]
            rw [← mul_right_inj' (FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
            rw [← mul_assoc, ← mul_assoc, h3_1, one_mul, neg_one_mul]
            exact h1
          rw [← h3_2, pow_add (1 + X_of_t) 2 2, ← h3_3]
          rw [← pow_two]
          ring_nf
        _ = r_of_s * X_of_t * X_of_t^2 * (2 * r_of_s + 4) := by ring_nf
        _ = -(1 + X_of_t)^2 * X_of_t^2 * (s + 2 / s)^2 := by
          rw [← h1]
          change r_of_s * X_of_t * X_of_t ^ 2 * (2 * (c_of_s + 1 / c_of_s) + 4) = r_of_s * X_of_t * X_of_t ^ 2 * (s + 2 / s) ^ 2
          change r_of_s * X_of_t * X_of_t ^ 2 * (2 * (2 / s^2 + 1 / (2 / s^2)) + 4) = r_of_s * X_of_t * X_of_t ^ 2 * (s + 2 / s) ^ 2
          have h3_4 : (2 * (2 / s^2 + 1 / (2 / s^2)) + 4) = (s + 2 / s)^2 := by
            ring_nf
            rw [inv_inv, mul_inv_cancel₀ s_h1, one_mul]
            rw [mul_assoc _ 2⁻¹ 2]
            rw [inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
            ring_nf
          rw [h3_4]
    have h4 : IsSquare (-1 : F) := by
      have h4_1 : Y_of_t^2 / ((1 + X_of_t) * X_of_t * (s + 2 / s))^2 = -1 := by
        rw [← neg_one_mul] at h3
        rw [mul_assoc (-1) ((1 + X_of_t)^2) (X_of_t^2)] at h3
        rw [← mul_pow (1 + X_of_t) (X_of_t) 2] at h3
        rw [mul_assoc (-1) (((1 + X_of_t) * X_of_t)^2) _] at h3
        rw [← mul_pow (((1 + X_of_t) * X_of_t))] at h3
        have h4_1_1 : ((1 + X_of_t) * X_of_t * (s + 2 / s))^2 ≠ 0 := by
          apply pow_ne_zero 2
          apply mul_ne_zero
          · apply mul_ne_zero
            · apply one_add_X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          · intro h4_1_2
            rw [← mul_right_inj' s_h1] at h4_1_2
            ring_nf at h4_1_2
            rw [mul_inv_cancel₀ s_h1, one_mul] at h4_1_2
            rw [add_comm] at h4_1_2
            have h4_1_2_1 : s^2 + 2 = 0 := by
              exact h4_1_2
            have h4_1_2_2 : (s^2 - 2) * (s^2 + 2) = 0 := by
              rw [h4_1_2_1, mul_zero]
            contradiction
        rw [← div_left_inj' h4_1_1] at h3
        rw [mul_div_assoc] at h3
        rw [div_self h4_1_1, mul_one] at h3
        exact h3
      have h4_2 : (Y_of_t / ((1 + X_of_t) * X_of_t * (s + 2 / s)))^2 = -1 := by
        rw [← div_pow] at h4_1
        exact h4_1
      rw [← h4_2]
      rw [pow_two]
      apply IsSquare.mul_self
    have h5 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h4
      rw [field_cardinality] at h4
      exact h4
    contradiction

lemma y_add_one_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  y_of_t + 1 ≠ (0 : F) := by
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    intro y_of_t
    intro h
    have h1 : y_of_t = -1 := by
      rw [← add_left_inj (-1)] at h
      have h1_1 : (1 : F) + (-1 : F) = 0 := by ring
      rw [add_assoc] at h
      rw [h1_1] at h
      rw [add_zero, zero_add] at h
      exact h
    have h2 : (r_of_s * X_of_t - (1 + X_of_t)^2) / (r_of_s * X_of_t + (1 + X_of_t)^2) = -1 := by
      change y_of_t = -1
      exact h1
    have h3 : r_of_s * X_of_t - (1 + X_of_t)^2 = -(r_of_s * X_of_t + (1 + X_of_t)^2) := by
      have h3_1 : (r_of_s * X_of_t + (1 + X_of_t)^2) ≠ 0 := y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
      rw [← div_left_inj' h3_1]
      rw [← neg_one_mul]
      rw [mul_div_assoc]
      rw [div_self h3_1]
      rw [mul_one]
      exact h2
    have h4 : r_of_s * X_of_t = 0 := by
      rw [← add_left_inj (r_of_s * X_of_t + (1 + X_of_t) ^ 2)] at h3
      ring_nf at h3
      rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3
      rw [mul_div_assoc] at h3
      rw [div_self (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3
      ring_nf at h3
      exact h3
    have h5 : r_of_s * X_of_t ≠ 0 := by
      apply mul_ne_zero
      · apply r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    contradiction

-- Chapter 3.2 Theorem 1
lemma u_mul_v_mul_X_mul_Y_mul_x_mul_y_add_one_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  u_of_t * v_of_t * X_of_t  * Y_of_t * x_of_t * (y_of_t + 1) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · apply u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
      · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    · apply y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

-- Chapter 3.2 Theorem 1
lemma x_pow_two_add_y_pow_two_eq_one_add_d_mul_x_pow_two_mul_y_pow_two
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  x_of_t^2 + y_of_t^2 = 1 + d_of_s * x_of_t^2 * y_of_t^2 := by
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    intro x_of_t y_of_t d_of_s
    have h1 : (c_of_s - 1)^2 * s^2 = 2 * (r_of_s - 2):=
      calc
        (c_of_s - 1)^2 * s^2 = (c_of_s - 1)^2 * (2 / c_of_s) := by
          have h1_1 : s^2 = 2 / c_of_s := by
            change s^2 = 2 / (2 / s^2)
            ring_nf
            rw [inv_inv]
            rw [mul_assoc]
            rw [inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one]
          rw [h1_1]
        _ = 2 * (r_of_s - 2) := by
          rw [sub_pow_two, mul_one, one_pow 2]
          rw [add_mul, sub_mul]
          rw [← mul_div_assoc]
          rw [one_mul]
          rw [mul_comm, pow_two, ← mul_assoc]
          rw [mul_div_assoc, div_self (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one]
          nth_rw 4 [← mul_one 2]
          rw [add_comm, ← add_sub_assoc]
          rw [mul_div_assoc, ← mul_add 2 (1 / c_of_s) c_of_s, add_comm]
          change 2 * r_of_s - 2 * c_of_s * (2 / c_of_s) = 2 * (r_of_s - 2)
          ring_nf
          rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
          ring_nf
    have h2 : Y_of_t^2 * (1 - x_of_t^2) = X_of_t * (r_of_s * X_of_t - (1 + X_of_t)^2)^2 := by
      calc
        Y_of_t^2 * (1 - x_of_t^2) = Y_of_t^2 - (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2 := by
          change Y_of_t^2 * (1 - (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) / Y_of_t)^2) = Y_of_t^2 - (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2
          rw [mul_sub, mul_one]
          have h2_1 : Y_of_t^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          rw [div_pow, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self h2_1]
          ring_nf
       _ = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t - 2 * (r_of_s - 2) * X_of_t^2 * (1 + X_of_t)^2 := by
          rw [h1, Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X  t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
       _ = X_of_t * (r_of_s * X_of_t - (1 + X_of_t)^2)^2 := by
          ring_nf
    let h3 := neg_d_eq_r_add_two_over_r_sub_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h4 : -d_of_s * (c_of_s - 1)^2 * s^2 = 2 * (r_of_s + 2) := by
      rw [h3, mul_assoc, h1]
      rw [mul_comm, ← mul_div_assoc, mul_assoc, mul_comm (r_of_s - 2) (r_of_s + 2), ← mul_assoc]
      have h4_1 : r_of_s - 2 ≠ 0 := by
        intro h4_1_1
        have h4_1_2 : (c_of_s - 1) ^ 2 * s ^ 2 = 0 := by
          rw [h4_1_1, mul_zero] at h1
          exact h1
        have h4_1_3 : (c_of_s - 1) ^ 2 * s ^ 2 ≠ 0 := by
          apply mul_ne_zero
          · apply pow_ne_zero 2
            exact c_sub_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
          · apply pow_ne_zero 2
            apply s_h1
        contradiction
      rw [mul_div_assoc, div_self h4_1, mul_one]
    have h5 : Y_of_t^2 * (1 - d_of_s * x_of_t^2) = X_of_t * (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by
      calc
        Y_of_t^2 * (1 - d_of_s * x_of_t^2) = Y_of_t^2 - d_of_s * (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2 := by
          change Y_of_t^2 * (1 - d_of_s * (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) / Y_of_t)^2) = Y_of_t^2 - d_of_s * (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2
          rw [mul_sub, mul_one]
          have h2_1 : Y_of_t^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          rw [div_pow, ← mul_assoc, mul_comm (Y_of_t^2), ← mul_div_assoc, mul_assoc]
          rw [mul_comm (Y_of_t ^ 2) (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) ^ 2)]
          rw [← mul_assoc, mul_div_assoc, div_self h2_1]
          ring_nf
       _ = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t + 2 * (r_of_s + 2) * X_of_t^2 * (1 + X_of_t)^2 := by
          rw [← neg_add_eq_sub, ← neg_one_mul]
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [neg_one_mul]
          rw [add_comm]
          rw [h4]
          rw [Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X   t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
       _ = X_of_t * (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by
          grind
    have h6 : (1 - d_of_s * x_of_t^2) ≠ 0 := by
      intro h6_1
      have h6_2 : IsSquare d_of_s := by
        rw [← add_right_inj (d_of_s * x_of_t^2), add_comm] at h6_1
        have h6_2_1 : 1 - d_of_s * x_of_t ^ 2 + d_of_s * x_of_t ^ 2 = 1 := by ring
        rw [add_zero, h6_2_1] at h6_1
        have h6_2_2 : x_of_t^2 ≠ 0 := by
          rw [pow_two]
          apply mul_ne_zero
          · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
        rw [← div_left_inj' h6_2_2] at h6_1
        rw [mul_div_assoc, div_self h6_2_2, mul_one] at h6_1
        rw [← mul_one 1, ← pow_two, ← div_pow _ _ 2] at h6_1
        rw [← h6_1, pow_two]
        apply IsSquare.mul_self
      have h6_3 : ¬IsSquare d_of_s := by exact d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      contradiction
    have h7 : Y_of_t^2 * (1 - d_of_s * x_of_t^2) ≠ 0 := by
      apply mul_ne_zero
      · rw [pow_two]
        apply mul_ne_zero
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
      · exact h6
    have h8 : (1 - x_of_t^2) / (1 - d_of_s * x_of_t^2) = y_of_t^2 := by
      calc
        (1 - x_of_t^2) / (1 - d_of_s * x_of_t^2) = (r_of_s * X_of_t - (1 + X_of_t)^2)^2 / (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by
          have h8_1 : Y_of_t^2 / Y_of_t^2 = 1 := by
            have h7_2 : Y_of_t^2 ≠ 0 := by
              rw [pow_two]
              apply mul_ne_zero
              · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
              · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            rw [div_self h7_2]
          nth_rw 1 [← one_mul (1 - x_of_t ^ 2), ← h8_1]
          rw [mul_div_assoc, ← mul_div_mul_comm]
          rw [h2, h5]
          rw [mul_div_mul_comm X_of_t _ X_of_t _]
          rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
          rw [one_mul]
        _ = y_of_t^2 := by
          rw [← div_pow _ _ 2]
          change y_of_t^2 = y_of_t^2
          rfl
    rw [← mul_right_inj' h6] at h8
    rw [← mul_div_assoc, mul_comm, mul_div_assoc, div_self h6, mul_one] at h8
    rw [sub_mul, one_mul] at h8
    rw [← add_left_inj (x_of_t^2)] at h8
    rw [← add_left_inj (y_of_t^2 * x_of_t^2 * d_of_s)] at h8
    ring_nf at h8
    symm at h8
    rw [mul_assoc (d_of_s) (x_of_t ^ 2) (y_of_t ^ 2), mul_comm (d_of_s) (x_of_t ^ 2 * y_of_t ^ 2)]
    exact h8
