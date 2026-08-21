/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.AuxiliaryCoordinates
public import Elligator.Elligator1.EdwardsCurve

/-!
# Output Coordinates

TODO

## Main Results

* TODO

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.OutputCoordinates

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates

section x

/-- x(t, s) is a function defined in the paper. It is the x-coordinate of the point on the curve.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:x"
  (title := "The curve coordinate $x$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$, with $c$, $X$ and $Y$ as above, define
  $$
  x = (c - 1)sX(1 + X)/Y .
  $$
  -/)]
def x [DecidableEq F]
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) (q : ℕ) : F :=
    let c := c s
    let X := X t s
    let Y := Y t s q
    (c - 1) * s * X * (1 + X) / Y

@[blueprint "lemma:x_ne_zero"
  (title := "$x \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $x = (c - 1)sX(1 + X)/Y \neq 0$, since $c \neq 1$, $s \neq 0$,
  $X \neq 0$ and $1 + X \neq 0$.
  -/)]
lemma x_ne_zero [DecidableEq F]
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let x := x t s q
    x ≠ 0 := by
  let c := c s
  let X := X t s
  let Y := Y t s q
  change (c - 1) * s * X * (1 + X) / Y ≠ 0
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · intro hc_eq_one
          have hc_eq_one' : c = 1 := by grind
          exact (c_ne_one sq_ne_pm_two) hc_eq_one'
        · apply hs_ne_zero
      · apply X_ne_zero hs_ne_zero hq_card hq_mod t
    · apply one_add_X_ne_zero hs_ne_zero hq_card hq_mod t
  · apply Y_ne_zero hs_ne_zero hq_card hq_mod t

lemma x_comparison [DecidableEq F]
    (t : { t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let x1 := x t s q
    let x2 := x ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s q
    x2 = x1 := by
  intro t1 t2 x1 x2
  let c := c s
  let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let X1 := X t s
  let Xbar := X ⟨t2, t_h⟩ s
  let Y1 := Y t s q
  let Y2 := Y ⟨t2, t_h⟩ s q
  have hX1_pow3_ne_zero : X1 ^ 3 ≠ 0 := pow_ne_zero 3 (X_ne_zero hs_ne_zero hq_card hq_mod t)
  calc
    x2 = (c - 1) * s * Xbar * (1 + Xbar) / Y2 := by rfl
    _ = (c - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1 ^ 3) := by grind [X_comparison, Y_comparison]
    _ = (c - 1) * s * X1 * (1 + X1) / Y1 := by simp_all; grind
    _ = x1 := by rfl

lemma x_y_eq_zero_sign_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // P ∈ EOverF sq_ne_pm_two hq_card hq_mod})
    (hx_eq_zero : P.val.1 = 0) :
    P.val = ((0 : F), (1 : F)) ∨ P.val = ((0 : F), (-1 : F)) := by
  let d := d s
  let x := P.val.1
  let y := P.val.2
  change (x, y) = (0, 1) ∨ (x, y) = (0, -1)
  change x = 0 at hx_eq_zero
  rw [← hx_eq_zero]
  have h_curve_eq : x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2 := by
    let hP := P.prop
    rw [mem_EOverF_iff] at hP
    exact hP
  have hy_eq_pm_one : y = 1 ∨ y = -1 := by simp_all
  rcases hy_eq_pm_one with h | h
  · rw [← h]; left; rfl
  · rw [← h]; right; rfl

end x

section y

variable [DecidableEq F]

/-- y(t, s) is a function defined in the paper. It is the y-coordinate of the point on the curve.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:y"
  (title := "The curve coordinate $y$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$, with $r$ and $X$ as above, define
  $$
  y = (rX - (1 + X) ^ 2)/(rX + (1 + X) ^ 2) .
  $$
  -/)]
def y
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
    let r := r s
    let X := X t s
    (r * X - (1 + X) ^ 2) / (r * X + (1 + X) ^ 2)

lemma helper_eq (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let r := r s
    let X := X t s
    let Y := Y t s q
    Y ^ 2 = X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X := by
  intro r X Y
  let c := c s
  let u := u t
  let v := v t s
  have hv_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
  have h_X_expand_eq_chi_v_mul_v : X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X = χ v * v := by
    calc
    X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X = χ v * (u ^ 5 + (r ^ 2 - 2) * u ^ 3 + u) := by
      change (χ v * u) ^ 5 + (r ^ 2 - 2) * (χ v * u) ^ 3 + (χ v * u)
        = χ v * (u ^ 5 + (r ^ 2 -2 ) * u ^ 3 + u)
      rw [mul_pow (χ v) (u) 5, mul_pow (χ v) (u) 3]
      rw [χ_of_a_pow_n_eq_χ_a v ⟨5, by trivial⟩]
      rw [χ_of_a_pow_n_eq_χ_a v ⟨3, by trivial⟩]
      ring_nf
    _ = χ v * v := by rfl
  have χ_a_mul_a_IsSquare := χ_a_mul_a_IsSquare hv_ne_zero hq_card hq_mod
  have h_χ_v_mul_v_fixed : (χ v * v) ^ ((q + 1) / 2) = χ v * v :=
    a_pow_q_add_one_div_two_eq_a χ_a_mul_a_IsSquare  hq_card hq_mod
  let χ_of_sum := χ (u ^ 2 + 1 / c ^ 2)
  have h_Y_sq_eq_chi_v_mul_v : Y ^ 2 = χ v * v := by
    calc
      Y ^ 2 = (χ v * v) ^ ((q + 1) / 2) * (χ v) ^ 2 * χ_of_sum ^ 2 := by
        change ((χ v * v) ^ ((q + 1) / 4) * χ v * χ_of_sum) ^ 2
          = (χ v * v) ^ ((q + 1) / 2) * (χ v) ^ 2 * χ_of_sum ^ 2
        ring_nf
        rw [one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
      _ = (χ v * v) ^ ((q + 1) / 2) * 1 := by
        rw [χ_of_a_even_pow_n_eq_one hv_ne_zero ⟨2, even_two⟩]
        rw [χ_of_a_even_pow_n_eq_one
          (v_factored_third_factor_ne_zero hs_ne_zero hq_card hq_mod t) ⟨2, even_two⟩]
        rw [mul_one]
      _ = χ v * v := by rw [h_χ_v_mul_v_fixed, mul_one]
  rw [h_X_expand_eq_chi_v_mul_v]
  exact h_Y_sq_eq_chi_v_mul_v

lemma y_divisor_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let r := r s;
    let X := X t s
    (r * X + (1 + X) ^ 2) ≠ 0 := by
  let Y := Y t s q
  let c := c s
  intro r X h_contra
  have hr_mul_X_eq_neg_expand : r * X = -(1 + X) ^ 2 :=
    Eq.symm (neg_eq_of_add_eq_zero_left h_contra)
  have hY_sq_eq_neg_expand : Y ^ 2 = -(1 + X) ^ 2 * X ^ 2 * (s + 2 / s) ^ 2 := by
    calc
      Y ^ 2 = X * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1) := by grind [helper_eq]
      _ = X ^ 3 * (2 * r ^ 2 + 4 * r) := by grind
      _ = r * X * X ^ 2 * (2 * r + 4) := by grind
      _ = -(1 + X) ^ 2 * X ^ 2 * (s + 2 / s) ^ 2 := by
        rw [← hr_mul_X_eq_neg_expand]
        change r * X * X ^ 2 * (2 * (2 / s ^ 2 + 1 / (2 / s ^ 2)) + 4)
          = r * X * X ^ 2 * (s + 2 / s) ^ 2
        have h_algebra_identity : (2 * (2 / s ^ 2 + 1 / (2 / s ^ 2)) + 4) = (s + 2 / s) ^ 2 := by
          ring_nf
          rw [inv_inv, mul_inv_cancel₀ hs_ne_zero, one_mul, mul_assoc]
          rw [inv_mul_cancel₀ (two_ne_zero hq_card hq_mod)]
          ring
        rw [h_algebra_identity]
  have h_isSquare_neg_one : IsSquare (-1 : F) := by
    have h_ratio_eq_neg_one : Y ^ 2 / ((1 + X) * X * (s + 2 / s)) ^ 2 = -1 := by
      rw [← neg_one_mul, mul_assoc (-1) ((1 + X) ^ 2) (X ^ 2)] at hY_sq_eq_neg_expand
      rw [← mul_pow (1 + X) (X) 2, mul_assoc (-1) (((1 + X) * X) ^ 2) _] at hY_sq_eq_neg_expand
      rw [← mul_pow (((1 + X) * X))] at hY_sq_eq_neg_expand
      have h_denom_ne_zero : ((1 + X) * X * (s + 2 / s)) ^ 2 ≠ 0 := by
        apply pow_ne_zero 2
        apply mul_ne_zero
        · apply mul_ne_zero
          · apply one_add_X_ne_zero hs_ne_zero hq_card hq_mod t
          · apply X_ne_zero hs_ne_zero hq_card hq_mod t
        · grind
      rw [← div_left_inj' h_denom_ne_zero, mul_div_assoc, div_self h_denom_ne_zero, mul_one]
        at hY_sq_eq_neg_expand
      exact hY_sq_eq_neg_expand
    have h_ratio_sq_eq_neg_one : (Y / ((1 + X) * X * (s + 2 / s))) ^ 2 = -1 := by
      rw [← div_pow] at h_ratio_eq_neg_one
      exact h_ratio_eq_neg_one
    rw [← h_ratio_sq_eq_neg_one, pow_two]
    apply IsSquare.mul_self
  have h_mod_ne_three : q % 4 ≠ 3 := by
    rw [FiniteField.isSquare_neg_one_iff, hq_card] at h_isSquare_neg_one
    exact h_isSquare_neg_one
  contradiction

lemma y_add_one_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let y := y t s
    y + 1 ≠ 0 := by
  let r := r s
  let X := X t s
  intro y h_contra
  have hy_eq_neg_one : y = -1 := Eq.symm (neg_eq_of_add_eq_zero_left h_contra)
  have hy_unfolded_eq_neg_one : (r * X - (1 + X) ^ 2) / (r * X + (1 + X) ^ 2) = -1 := by
    change y = -1
    exact hy_eq_neg_one
  have h_num_eq_neg_denom : r * X - (1 + X) ^ 2 = -(r * X + (1 + X) ^ 2) := by grind
  have hr_mul_X_eq_zero : r * X = 0 := by
    rw [← add_left_inj (r * X + (1 + X) ^ 2)] at h_num_eq_neg_denom
    ring_nf at h_num_eq_neg_denom
    rw [← div_left_inj' (two_ne_zero hq_card hq_mod), mul_div_assoc] at h_num_eq_neg_denom
    rw [div_self (two_ne_zero hq_card hq_mod)] at h_num_eq_neg_denom
    ring_nf at h_num_eq_neg_denom
    exact h_num_eq_neg_denom
  have hr_mul_X_ne_zero : r * X ≠ 0 := mul_ne_zero
    (r_ne_zero hs_ne_zero hq_card hq_mod) (X_ne_zero hs_ne_zero hq_card hq_mod t)
  contradiction

lemma variable_mul_ne_zero' (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
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
          · apply v_ne_zero hs_ne_zero hq_card hq_mod t
        · apply X_ne_zero hs_ne_zero hq_card hq_mod t
      · apply Y_ne_zero hs_ne_zero hq_card hq_mod t
    · apply x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t
  · apply y_add_one_ne_zero hs_ne_zero hq_card hq_mod t

lemma curve_equation (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let x := x t s q
    let y := y t s
    let d := d s
    x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2 := by
  let c := c s
  let r := r s
  let X := X t s
  let Y := Y t s q
  intro x y d
  have h_c_sub_one_sq_mul_s_sq_eq : (c - 1) ^ 2 * s ^ 2 = 2 * (r - 2) :=
    calc
      (c - 1) ^ 2 * s ^ 2 = (c - 1) ^ 2 * (2 / c) := by grind [s_pow_two_eq_two_div_c]
      _ = 2 * (r - 2) := by
        rw [sub_pow_two, mul_one, one_pow 2, add_mul, sub_mul]
        rw [← mul_div_assoc, one_mul, mul_comm, pow_two, ← mul_assoc]
        rw [mul_div_assoc, div_self (c_ne_zero hs_ne_zero hq_card hq_mod), mul_one]
        nth_rw 4 [← mul_one 2]
        rw [add_comm, ← add_sub_assoc, mul_div_assoc, ← mul_add 2 (1 / c) c, add_comm]
        change 2 * r - 2 * c * (2 / c) = 2 * (r - 2)
        ring_nf
        rw [mul_inv_cancel₀ (c_ne_zero hs_ne_zero hq_card hq_mod)]
        ring
  have h_Y_sq_mul_one_sub_x_sq_eq : Y ^ 2 * (1 - x ^ 2) = X * (r * X - (1 + X) ^ 2) ^ 2 := by
    calc
      Y ^ 2 * (1 - x ^ 2) = Y ^ 2 - (c - 1) ^ 2 * s ^ 2 * X ^ 2 * (1 + X) ^ 2 := by
        change Y ^ 2 * (1 - (((c - 1) * s * X * (1 + X)) / Y) ^ 2)
          = Y ^ 2 - (c - 1) ^ 2 * s ^ 2 * X ^ 2 * (1 + X) ^ 2
        rw [mul_sub, mul_one]
        have hY_sq_ne_zero : Y ^ 2 ≠ 0 := pow_ne_zero 2 (Y_ne_zero hs_ne_zero hq_card hq_mod t)
        grind
    _ = X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X - 2 * (r - 2) * X ^ 2 * (1 + X) ^ 2 := by
        rw [h_c_sub_one_sq_mul_s_sq_eq, helper_eq t hs_ne_zero hq_card hq_mod]
    _ = X * (r * X - (1 + X) ^ 2) ^ 2 := by ring
  have h_neg_d_mul_c_sub_one_sq_mul_s_sq_eq : -d * (c - 1) ^ 2 * s ^ 2 = 2 * (r + 2) := by
    rw [neg_d_eq_r_add_two_div_r_sub_two hs_ne_zero hq_card hq_mod, mul_assoc,
      h_c_sub_one_sq_mul_s_sq_eq]
    rw [mul_comm, ← mul_div_assoc, mul_assoc, mul_comm (r - 2) (r + 2), ← mul_assoc]
    have hr_sub_two_ne_zero : r - 2 ≠ 0 := by
      intro hr_sub_two_eq_zero
      have h_c_sub_one_sq_mul_s_sq_eq_zero : (c - 1) ^ 2 * s ^ 2 = 0 := by grind
      have h_c_sub_one_sq_mul_s_sq_ne_zero : (c - 1) ^ 2 * s ^ 2 ≠ 0 := by
        apply mul_ne_zero
        · exact pow_ne_zero 2 (c_sub_one_ne_zero sq_ne_pm_two)
        · exact pow_ne_zero 2 hs_ne_zero
      contradiction
    rw [mul_div_assoc, div_self hr_sub_two_ne_zero, mul_one]
  have h_Y_sq_mul_one_sub_d_mul_x_sq_eq : Y ^ 2 * (1 - d * x ^ 2)
      = X * (r * X + (1 + X) ^ 2) ^ 2 := by
    calc
      Y ^ 2 * (1 - d * x ^ 2) = Y ^ 2 - d * (c - 1) ^ 2 * s ^ 2 * X ^ 2 * (1 + X) ^ 2 := by
        change Y ^ 2 * (1 - d * (((c - 1) * s * X * (1 + X)) / Y) ^ 2)
          = Y ^ 2 - d * (c - 1) ^ 2 * s ^ 2 * X ^ 2 * (1 + X) ^ 2
        rw [mul_sub, mul_one]
        have hY_sq_ne_zero : Y ^ 2 ≠ 0 := pow_ne_zero 2 (Y_ne_zero hs_ne_zero hq_card hq_mod t)
        rw [div_pow, ← mul_assoc, mul_comm (Y ^ 2)]
        grind
    _ = X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X + 2 * (r + 2) * X ^ 2 * (1 + X) ^ 2 := by
      rw [helper_eq t hs_ne_zero hq_card hq_mod]
      grind
    _ = X * (r * X + (1 + X) ^ 2) ^ 2 := by ring
  have h_one_sub_d_mul_x_sq_ne_zero : (1 - d * x ^ 2) ≠ 0 := by
    intro h_one_sub_d_mul_x_sq_eq_zero
    have hd_isSquare : IsSquare d := by
      rw [← add_right_inj (d * x ^ 2), add_comm] at h_one_sub_d_mul_x_sq_eq_zero
      have h_cancel_identity : 1 - d * x ^ 2 + d * x ^ 2 = 1 := by ring
      rw [add_zero, h_cancel_identity] at h_one_sub_d_mul_x_sq_eq_zero
      have hx_sq_ne_zero : x ^ 2 ≠ 0 := pow_ne_zero 2
        (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t)
      rw [← div_left_inj' hx_sq_ne_zero] at h_one_sub_d_mul_x_sq_eq_zero
      rw [mul_div_assoc, div_self hx_sq_ne_zero, mul_one] at h_one_sub_d_mul_x_sq_eq_zero
      rw [← mul_one 1, ← pow_two, ← div_pow _ _ 2] at h_one_sub_d_mul_x_sq_eq_zero
      rw [← h_one_sub_d_mul_x_sq_eq_zero, pow_two]
      apply IsSquare.mul_self
    have hd_not_isSquare : ¬IsSquare d := d_nonsquare sq_ne_pm_two hq_card hq_mod
    contradiction
  have h_Y_sq_mul_one_sub_d_mul_x_sq_ne_zero : Y ^ 2 * (1 - d * x ^ 2) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero 2 (Y_ne_zero hs_ne_zero hq_card hq_mod t)
    · exact h_one_sub_d_mul_x_sq_ne_zero
  have h_ratio_eq_y_sq : (1 - x ^ 2) / (1 - d * x ^ 2) = y ^ 2 := by
    calc
      (1 - x ^ 2) / (1 - d * x ^ 2) = (r * X - (1 + X) ^ 2) ^ 2 / (r * X + (1 + X) ^ 2) ^ 2 := by
        have h_Y_sq_div_self_eq_one : Y ^ 2 / Y ^ 2 = 1 := by
          have hY_sq_ne_zero : Y ^ 2 ≠ 0 := pow_ne_zero 2 (Y_ne_zero hs_ne_zero hq_card hq_mod t)
          rw [div_self hY_sq_ne_zero]
        nth_rw 1 [← one_mul (1 - x ^ 2), ← h_Y_sq_div_self_eq_one]
        rw [mul_div_assoc, ← mul_div_mul_comm, h_Y_sq_mul_one_sub_x_sq_eq,
          h_Y_sq_mul_one_sub_d_mul_x_sq_eq]
        rw [mul_div_mul_comm X _ X _, div_self (X_ne_zero hs_ne_zero hq_card hq_mod t), one_mul]
      _ = y ^ 2 := by
        rw [← div_pow _ _ 2]
        rfl
  grind


end y

end Elligator.Elligator1.OutputCoordinates
