/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.sProperties
public import Elligator.Elligator1.cProperties
public import Elligator.Elligator1.dProperties
public import Elligator.Elligator1.EdwardsCurve
public import Elligator.Elligator1.uProperties
public import Elligator.Elligator1.vProperties
public import Elligator.Elligator1.XProperties
public import Elligator.Elligator1.YProperties
public import Elligator.Elligator1.xProperties

/-!
# y Variable Properties

In this file we introduce some generally helpful lemmas for `y` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma helper_eq
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let r := r s
  let X := X t s
  let Y := Y t s q
  Y^2 = X^5 + (r^2 - 2) * X^3 + X := by
    intro r X Y
    let c := c s
    let u := u t
    let v := v t s
    let χ_of_v := χ v
    let v_ne_zero := v_ne_zero s_h1 q_h1 q_h2 q_h3 t
    have h1 : X^5 + (r^2 - 2) * X^3 + X = χ_of_v * v := by
      calc
      X^5 + (r^2 - 2) * X^3 + X = χ_of_v * (u^5 + (r^2 - 2) * u^3 + u) := by
        change (χ_of_v * u)^5 + (r^2 - 2) * (χ_of_v * u)^3 + (χ_of_v * u)
          = χ_of_v * (u^5 + (r^2 -2 ) * u^3 + u)
        rw [mul_pow (χ_of_v) (u) 5, mul_pow (χ_of_v) (u) 3]
        rw [χ_of_a_pow_n_eq_χ_a v ⟨5, by trivial⟩ q_h1 q_h2 q_h3]
        rw [χ_of_a_pow_n_eq_χ_a v ⟨3, by trivial⟩ q_h1 q_h2 q_h3]
        change χ_of_v * u^5 + (r^2 - 2) * (χ_of_v * u^3) + (χ_of_v * u)
          = χ_of_v * (u^5 + (r^2 -2 ) * u^3 + u)
        ring_nf
      _ = χ_of_v * v := by rfl
    have h2 := χ_a_mul_a_IsSquare v_ne_zero q_h1 q_h2 q_h3
    have h3 : (χ_of_v * v)^((q + 1) / 2) = χ_of_v * v := a_pow_q_add_one_over_two_eq_a h2 q_h1 q_h3
    let χ_of_sum := χ (u^2 + 1 / c^2)
    have h4 : Y^2 = χ_of_v * v := by
      calc
        Y^2 = (χ_of_v * v)^((q + 1) / 2) * χ_of_v^2 * χ_of_sum^2 := by
          change ((χ_of_v * v)^((q + 1) / 4) * χ_of_v * χ_of_sum)^2
            = (χ_of_v * v)^((q + 1) / 2) * χ_of_v^2 * χ_of_sum^2
          ring_nf
          rw [one_add_q_over_four_mul_two_eq_one_add_q_over_two q_h3]
        _ = (χ_of_v * v)^((q + 1) / 2) * 1 := by
          rw [χ_of_a_even_pow_n_eq_one v_ne_zero ⟨2, even_two⟩ q_h1 q_h3]
          rw [χ_of_a_even_pow_n_eq_one
            (v_h1_third_factor_ne_zero s_h1 q_h1 q_h2 q_h3 t) ⟨2, even_two⟩ q_h1 q_h3]
          rw [mul_one]
        _ = χ_of_v * v := by rw [h3, mul_one]
    rw [h1]
    exact h4

lemma y_divisor_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let r := r s;
  let X := X t s
  (r * X + (1 + X)^2) ≠ 0 := by
    let Y := Y t s q
    let c := c s
    intro r X h
    have h1 : r * X = -(1 + X)^2 := by grind
    have h2 : (r^2 + 4 * r) * X^2 = X^4 - 2 * X^2 + 1 := by grind
    have h3 : Y^2 = -(1 + X)^2 * X^2 * (s + 2 / s)^2 := by
      calc
        Y^2 = X * (X^4 + (r^2 - 2) * X^2 + 1) := by grind [helper_eq]
        _ = X^3 * (2 * r^2 + 4 * r) := by grind
        _ = r * X * X^2 * (2 * r + 4) := by grind
        _ = -(1 + X)^2 * X^2 * (s + 2 / s)^2 := by
          rw [← h1]
          change r * X * X^2 * (2 * (2 / s^2 + 1 / (2 / s^2)) + 4) = r * X * X^2 * (s + 2 / s)^2
          have h' : (2 * (2 / s^2 + 1 / (2 / s^2)) + 4) = (s + 2 / s)^2 := by
            ring_nf
            rw [inv_inv, mul_inv_cancel₀ s_h1, one_mul, mul_assoc]
            rw [inv_mul_cancel₀ (two_ne_zero q_h1 q_h3)]
            ring_nf
          rw [h']
    have h4 : IsSquare (-1 : F) := by
      have h4_1 : Y^2 / ((1 + X) * X * (s + 2 / s))^2 = -1 := by
        rw [← neg_one_mul, mul_assoc (-1) ((1 + X)^2) (X^2)] at h3
        rw [← mul_pow (1 + X) (X) 2, mul_assoc (-1) (((1 + X) * X)^2) _] at h3
        rw [← mul_pow (((1 + X) * X))] at h3
        have h4_1_1 : ((1 + X) * X * (s + 2 / s))^2 ≠ 0 := by
          apply pow_ne_zero 2
          apply mul_ne_zero
          · apply mul_ne_zero
            · apply one_add_X_ne_zero s_h1 q_h1 q_h2 q_h3 t
            · apply X_ne_zero s_h1 q_h1 q_h2 q_h3 t
          · grind
        rw [← div_left_inj' h4_1_1, mul_div_assoc, div_self h4_1_1, mul_one] at h3
        exact h3
      have h4_2 : (Y / ((1 + X) * X * (s + 2 / s)))^2 = -1 := by
        rw [← div_pow] at h4_1
        exact h4_1
      rw [← h4_2, pow_two]
      apply IsSquare.mul_self
    have h5 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h4
      rw [q_h1] at h4
      exact h4
    contradiction

lemma y_add_one_ne_zero
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let y := y t s
  y + 1 ≠ (0 : F) := by
    let r := r s;
    let X := X t s
    intro y h
    have h1 : y = -1 := by grind
    have h2 : (r * X - (1 + X)^2) / (r * X + (1 + X)^2) = -1 := by
      change y = -1
      exact h1
    have h3 : r * X - (1 + X)^2 = -(r * X + (1 + X)^2) := by grind
    have h4 : r * X = 0 := by
      rw [← add_left_inj (r * X + (1 + X)^2)] at h3
      ring_nf at h3
      rw [← div_left_inj' (two_ne_zero q_h1 q_h3), mul_div_assoc] at h3
      rw [div_self (two_ne_zero q_h1 q_h3)] at h3
      ring_nf at h3
      exact h3
    have h5 : r * X ≠ 0 := by
      apply mul_ne_zero (r_ne_zero s_h1 q_h1 q_h2 q_h3) (X_ne_zero s_h1 q_h1 q_h2 q_h3 t)
    contradiction

lemma variable_mul_ne_zero'
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let u := u t
  let v := v t s
  let X := X t s
  let Y := Y t s q
  let x := x t s q
  let y := y t s
  u * v * X  * Y * x * (y + 1) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · apply u_ne_zero t
            · apply v_ne_zero s_h1 q_h1 q_h2 q_h3 t
          · apply X_ne_zero s_h1 q_h1 q_h2 q_h3 t
        · apply Y_ne_zero s_h1 q_h1 q_h2 q_h3 t
      · apply x_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 t
    · apply y_add_one_ne_zero s_h1 q_h1 q_h2 q_h3 t

lemma curve_equation
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let x := x t s q
  let y := y t s
  let d := d s
  x^2 + y^2 = 1 + d * x^2 * y^2 := by
    let c := c s
    let d := d s;
    let r := r s;
    let X := X t s
    let Y := Y t s q
    intro x y d
    have h1 : (c - 1)^2 * s^2 = 2 * (r - 2):=
      calc
        (c - 1)^2 * s^2 = (c - 1)^2 * (2 / c) := by grind [s_pow_two_eq_two_over_c]
        _ = 2 * (r - 2) := by
          rw [sub_pow_two, mul_one, one_pow 2, add_mul, sub_mul]
          rw [← mul_div_assoc, one_mul, mul_comm, pow_two, ← mul_assoc]
          rw [mul_div_assoc, div_self (c_ne_zero s_h1 q_h1 q_h3), mul_one]
          nth_rw 4 [← mul_one 2]
          rw [add_comm, ← add_sub_assoc, mul_div_assoc, ← mul_add 2 (1 / c) c, add_comm]
          change 2 * r - 2 * c * (2 / c) = 2 * (r - 2)
          ring_nf
          rw [mul_inv_cancel₀ (c_ne_zero s_h1 q_h1 q_h3)]
          ring_nf
    have h2 : Y^2 * (1 - x^2) = X * (r * X - (1 + X)^2)^2 := by
      calc
        Y^2 * (1 - x^2) = Y^2 - (c - 1)^2 * s^2 * X^2 * (1 + X)^2 := by
          change Y^2 * (1 - (((c - 1) * s * X * (1 + X)) / Y)^2)
            = Y^2 - (c - 1)^2 * s^2 * X^2 * (1 + X)^2
          rw [mul_sub, mul_one]
          have h2_1 : Y^2 ≠ 0 := pow_two_ne_zero (Y_ne_zero s_h1 q_h1 q_h2 q_h3 t)
          grind
       _ = X^5 + (r^2 - 2) * X^3 + X - 2 * (r - 2) * X^2 * (1 + X)^2 := by
          rw [h1, helper_eq t s_h1 q_h1 q_h2 q_h3]
       _ = X * (r * X - (1 + X)^2)^2 := by ring_nf
    have h4 : -d * (c - 1)^2 * s^2 = 2 * (r + 2) := by
      rw [neg_d_eq_r_add_two_over_r_sub_two s_h1 q_h1 q_h2 q_h3, mul_assoc, h1]
      rw [mul_comm, ← mul_div_assoc, mul_assoc, mul_comm (r - 2) (r + 2), ← mul_assoc]
      have h4_1 : r - 2 ≠ 0 := by
        intro h4_1_1
        have h4_1_2 : (c - 1)^2 * s^2 = 0 := by grind
        have h4_1_3 : (c - 1)^2 * s^2 ≠ 0 := by
          apply mul_ne_zero
          · exact pow_two_ne_zero (c_sub_one_ne_zero s_h2)
          · exact pow_two_ne_zero s_h1
        contradiction
      rw [mul_div_assoc, div_self h4_1, mul_one]
    have h5 : Y^2 * (1 - d * x^2) = X * (r * X + (1 + X)^2)^2 := by
      calc
        Y^2 * (1 - d * x^2) = Y^2 - d * (c - 1)^2 * s^2 * X^2 * (1 + X)^2 := by
          change Y^2 * (1 - d * (((c - 1) * s * X * (1 + X)) / Y)^2)
            = Y^2 - d * (c - 1)^2 * s^2 * X^2 * (1 + X)^2
          rw [mul_sub, mul_one]
          have h2_1 : Y^2 ≠ 0 := pow_two_ne_zero (Y_ne_zero s_h1 q_h1 q_h2 q_h3 t)
          rw [div_pow, ← mul_assoc, mul_comm (Y^2)]
          grind
       _ = X^5 + (r^2 - 2) * X^3 + X + 2 * (r + 2) * X^2 * (1 + X)^2 := by grind [helper_eq]
       _ = X * (r * X + (1 + X)^2)^2 := by grind
    have h6 : (1 - d * x^2) ≠ 0 := by
      intro h6_1
      have h6_2 : IsSquare d := by
        rw [← add_right_inj (d * x^2), add_comm] at h6_1
        have h6_2_1 : 1 - d * x^2 + d * x^2 = 1 := by ring
        rw [add_zero, h6_2_1] at h6_1
        have h6_2_2 : x^2 ≠ 0 := pow_two_ne_zero (x_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 t)
        rw [← div_left_inj' h6_2_2] at h6_1
        rw [mul_div_assoc, div_self h6_2_2, mul_one] at h6_1
        rw [← mul_one 1, ← pow_two, ← div_pow _ _ 2] at h6_1
        rw [← h6_1, pow_two]
        apply IsSquare.mul_self
      have h6_3 : ¬IsSquare d := by exact d_nonsquare s_h2 q_h1 q_h3
      contradiction
    have h7 : Y^2 * (1 - d * x^2) ≠ 0 := by
      apply mul_ne_zero
      · exact pow_two_ne_zero (Y_ne_zero s_h1 q_h1 q_h2 q_h3 t)
      · exact h6
    have h8 : (1 - x^2) / (1 - d * x^2) = y^2 := by
      calc
        (1 - x^2) / (1 - d * x^2) = (r * X - (1 + X)^2)^2 / (r * X + (1 + X)^2)^2 := by
          have h8_1 : Y^2 / Y^2 = 1 := by
            have h7_2 : Y^2 ≠ 0 := pow_two_ne_zero (Y_ne_zero s_h1 q_h1 q_h2 q_h3 t)
            rw [div_self h7_2]
          nth_rw 1 [← one_mul (1 - x^2), ← h8_1]
          rw [mul_div_assoc, ← mul_div_mul_comm, h2, h5]
          rw [mul_div_mul_comm X _ X _, div_self (X_ne_zero s_h1 q_h1 q_h2 q_h3 t), one_mul]
        _ = y^2 := by
          rw [← div_pow _ _ 2]
          change y^2 = y^2
          rfl
    grind

end Elligator.Elligator1
