/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Architect
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
variable {s : F} (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

omit [Fintype F] in
@[blueprint
  (title := "u defined")
  (statement := /--
  The following element of $\mathbb{F}_q$ is defined for each $t \in \mathbb{F}_q \setminus \{-1,1\}$:
  $$
  u = (1 - t)/(1 + t),
  $$
  -/)]
theorem u_defined :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, (1 + t.val) ≠ 0 := by
    intro t
    exact FiniteFieldBasic.one_add_t_ne_zero t

@[blueprint
  (title := "Y defined")
  (statement := /--
  The following element of $\mathbb{F}_q$ is defined for each $t \in \mathbb{F}_q \setminus \{-1,1\}$:
  $$
  Y = (\chi(v)v)^{(q+1)/4}\chi(v)\chi(u^2 + 1/c^2),
  $$
  -/)]
theorem Y_defined
  (s_h1 : s ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (c s)^2 ≠ 0 := by
    exact c_pow_two_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3

@[blueprint
  (title := "x defined")
  (statement := /--
  The following element of $\mathbb{F}_q$ is defined for each $t \in \mathbb{F}_q \setminus \{-1,1\}$:
  $$
  x = (c - 1)sX(1 + X)/Y,
  $$
  -/)]
theorem x_defined
  (s_h1 : s ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, (Y t s q) ≠ 0 := by
    intro t
    exact Y_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3 t

@[blueprint
  (title := "y defined")
  (statement := /--
  The following element of $\mathbb{F}_q$ is defined for each $t \in \mathbb{F}_q \setminus \{-1,1\}$:
  $$
  y = (rX - (1 + X)^2)/(rX + (1 + X)^2).
  $$
  -/)]
theorem y_defined
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ((r s) * (X t s) + (1 + (X t s))^2) ≠ 0 := by
    intro t
    exact y_divisor_ne_zero s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3 t

-- Chapter 3.2 Theorem 1
@[blueprint
  (title := "Fulfill Helper Curve Equation")
  (statement := /--
  Let r, X and Y as defined above.

  Then $Y^2 = X^5 + (r^2 - 2)X^3 + X$ holds.
  -/)]
theorem map_fulfills_helper_equation
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s_h1 : s ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r := r s
  let X := X t s
  let Y := Y t s q
  Y^2 = X^5 + (r^2 - 2) * X^3 + X := by
    intro r_of_s X_of_t Y_of_t
    exact Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X t s_h1 field_cardinality q_prime_power q_mod_4_congruent_3

-- Chapter 3.2 Theorem 1
@[blueprint
  (title := "Non zero helper variables")
  (statement := /--
  Let u, v, X, Y, x, y as defined above.

  Then $uvXYx(y + 1) \neq 0$.
  -/)]
theorem variable_mul_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let u := u t
  let v := v t s
  let X := X t s
  let Y := Y t s q
  let x := x t s q
  let y := y t s
  u * v * X  * Y * x * (y + 1) ≠ 0 := by
  exact u_mul_v_mul_X_mul_Y_mul_x_mul_y_add_one_ne_zero t s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3

-- Chapter 3.2 Theorem 1
@[blueprint
  (title := "Fulfill Curve Equation")
  (statement := /--
  Let x and y as defined above.

  Then $x^2 + y^2 = 1 + d x^2 y^2$ holds.
  -/)]
theorem map_fulfills_curve_equation
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let x := x t s q
  let y := y t s
  let d := d s
  have d_h : d ≠ 0 ∧ d ≠ 1 := by exact d_ne_zero_and_d_ne_one s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
  edwardsCurveEquation x y ⟨d, d_h⟩ := by
    intro x_of_t y_of_t d_of_s
    exact x_pow_two_add_y_pow_two_eq_one_add_d_mul_x_pow_two_mul_y_pow_two t s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3

/-- Original: Chapter "3.2 The map": Definition 2-/
@[blueprint "def:ϕ"]
noncomputable def ϕ
  (t : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : EOverF s_h2 field_cardinality q_prime_power q_mod_4_congruent_3 :=
  open scoped Classical in let P := if h : t ≠ 1 ∧ t ≠ -1
    then (x ⟨t, h⟩ s q, y ⟨t, h⟩ s)
    else (0, 1)
  -- TODO writeable as type?
  have P_in_EOverF : P ∈ (EOverF s_h2 field_cardinality q_prime_power q_mod_4_congruent_3) := by
    unfold EOverF
    rw [Set.mem_setOf_eq]
    unfold P
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · rw [dif_pos h1]
      exact map_fulfills_curve_equation ⟨t, h1⟩ s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
    · rw [dif_neg h1]
      unfold edwardsCurveEquation
      ring_nf
  ⟨P, P_in_EOverF⟩
