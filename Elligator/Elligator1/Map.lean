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
public import Elligator.Elligator1.yProperties

@[expose] public section

/-!
# Map

In this file we collect the main results regarding the map of Elligator 1.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3 theorem 1.
-/

namespace Elligator.Elligator1

section Map

variable {F : Type*} [Field F] [Fintype F]

theorem u_defined :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, (1 + t.val) ≠ 0 := by
    intro t
    exact FiniteFieldBasic.one_add_t_ne_zero t

theorem Y_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, (c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)^2 ≠ 0 := by
    intro t
    exact c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

theorem x_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ≠ 0 := by
    intro t
    exact Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

theorem y_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ((r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
  * (X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
  + (1 + (X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3))^2)
  ≠ 0 := by
    intro t
    exact y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

-- Chapter 3.2 Theorem 1
theorem map_fulfills_helper_equation
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
    intro r_of_s X_of_t Y_of_t
    exact Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Chapter 3.2 Theorem 1
theorem variable_mul_ne_zero
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
  exact u_mul_v_mul_X_mul_Y_mul_x_mul_y_add_one_ne_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Chapter 3.2 Theorem 1
theorem map_fulfills_curve_equation
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
  have d_h : d_of_s ≠ 0 ∧ d_of_s ≠ 1 := by exact d_ne_zero_and_d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  edwards_curve_equation x_of_t y_of_t ⟨d_of_s, d_h⟩ q field_cardinality q_prime_power q_mod_4_congruent_3 := by
    intro x_of_t y_of_t d_of_s
    exact x_pow_two_add_y_pow_two_eq_one_add_d_mul_x_pow_two_mul_y_pow_two t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

/-- In the situation of Theorem 1, the decoding function for the complete
Edwards curve E : x² + y² = 1 + dx²y² is the function ϕ : Fq → E(Fq) defined as follows: ϕ(±1) = (0, 1); if t ∉ {±1} then ϕ(t) = (x, y).

Original: Chapter "3.2 The map": Definition 2
-/
noncomputable def ϕ
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : {P : F × F // P ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3} :=
  open scoped Classical in let P := if h : t ≠ 1 ∧ t ≠ -1
    then (x ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3, y ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
    else (0, 1)
  have P_in_E_over_F : P ∈ (E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) := by
    unfold E_over_F
    rw [Set.mem_setOf_eq]
    unfold P
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · rw [dif_pos h1]
      exact map_fulfills_curve_equation ⟨t, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · rw [dif_neg h1]
      unfold edwards_curve_equation
      ring_nf
  ⟨P, P_in_E_over_F⟩
