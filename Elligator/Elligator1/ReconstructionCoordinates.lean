/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Reconstruction Coordinates

TODO

## Main Results

* TODO

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.ReconstructionCoordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates

section η

/-- η(s, q, point) is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:η"
  (title := "The inversion quantity $\\eta$")
  (statement := /--
  For a point $(x, y)$ of $E(\mathbb{F}_q)$ with $y + 1 \neq 0$, define
  $$
  \eta = \frac{y - 1}{2(y + 1)} .
  $$
  -/)]
def η (P : F × F) : F :=
    let y := P.snd
    (y - 1) / (2 * (y + 1))

-- Used in Theorem 3 Proof B part as implication for P_in_ϕOverF_with_prop2_main_case
-- argument.
lemma y_h1 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let y := y t s
    let r := r s
    let X := X t s
    X ^ 2 + (2 + r * (y - 1) / (y + 1)) * X + 1 = 0 := by
  intro y r X
  rw [← mul_left_inj' (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
  change (X ^ 2 + (2 + r * (y - 1) / (y + 1)) * X + 1) * (y + 1) = 0 * (y + 1)
  repeat rw [add_mul]
  rw [zero_mul]
  have h1 : (2 * X * (y + 1) + r * (y - 1) / (y + 1) * X * (y + 1))
      = (2 * (y + 1) + r * (y - 1)) * X := by
    rw [add_mul _ _ X, ← div_left_inj' (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
    change (2 * X * (y + 1) + r * (y - 1) / (y + 1) * X * (y + 1)) / (y + 1)
      = (2 * (y + 1) * X + r * (y - 1) * X) / (y + 1)
    repeat rw [add_div, mul_div_assoc, div_self (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
    rw [mul_comm (2 * (y + 1)) X, ← mul_assoc]
    nth_rw 2 [mul_div_assoc]
    rw [div_self (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
    ring
  have h2 : (2 * (y + 1) + r * (y - 1)) = (y * r - r + 2 * y + 2) := by ring_nf
  rw [h1, h2, mul_add, add_mul]
  ring_nf
  rw [← add_right_inj (r * X - 1 - 2 * X - X ^ 2)]
  ring_nf
  rw [mul_comm (X ^ 2) y, mul_comm X y, mul_assoc, mul_assoc]
  nth_rw 4 [← mul_one y]
  rw [add_assoc, ← mul_add y]
  rw [add_assoc, ← mul_add y, add_comm (X ^ 2) 1, ← add_assoc, add_comm (X * 2) 1]
  rw [mul_comm X 2]
  have h3 : 1 + 2 * X + X ^ 2 = (1 + X) ^ 2 := by ring_nf
  have h4 : -1 + r * X - 2 * X - X ^ 2 = r * X - (1 + 2 * X + X ^ 2) := by ring_nf
  rw [h4, h3]
  rw [← mul_assoc, mul_comm, ← mul_add]
  rw [← div_left_inj' (y_divisor_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t)]
  change (y * (r * X + (1 + X) ^ 2)) / (r * X + (1 + X) ^ 2) = y
  rw [mul_div_assoc]
  rw [div_self (y_divisor_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t), mul_one]

-- Implicated by y_h1. Saved for further proof arguments in Theorem 3 Proof B
lemma y_h2 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let r := r s
    let X := X t s
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let η := η P
    X ^ 2 + 2 * (1 + η * r) * X + 1 = 0 := by
  intro r X P η
  let y := y t s
  calc
    X ^ 2 + 2 * (1 + η * r) * X + 1
    = X ^ 2 + 2 * (1 + 1 / 2 * ((y - 1) / (y + 1)) * r) * X + 1 := by
      -- Unfold until reaching the y which is equivalent to y for comparison
      unfold η ReconstructionCoordinates.η P ϕ
      simp only [Subtype.coe_eta, dite_eq_ite, one_div]
      rw [ite_eq_left t.prop]
      change X ^ 2 + 2 * (1 + (y - 1) / (2 * (y + 1)) * r) * X + 1
        = X ^ 2 + 2 * (1 + 2⁻¹ * ((y - 1) / (y + 1)) * r) * X + 1
      rw [inv_eq_one_div, ← mul_div_mul_comm]
      ring
    _ = X ^ 2 + (2 + r * (y - 1) / (y + 1)) * X + 1 := by
      rw [mul_add 2]
      rw [div_eq_mul_inv 1 2, mul_one, one_mul, mul_assoc, ← mul_assoc]
      rw [mul_inv_cancel₀ (two_ne_zero hq_card hq_mod)]
      ring
    _ = 0 := by rw [y_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod]

-- Implicated by y_h2.
lemma y_h3 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let r := r s
    let X := X t s
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let η := η P
    X + 1 / X = -2 * (1 + η * r) := by
  intro r X P η
  rw [← add_right_inj (2 * (1 + η * r))]
  rw [← mul_left_inj' (X_ne_zero hs_ne_zero hq_card hq_mod t)]
  change (2 * (1 + η * r) + (X + 1 / X)) * X = (2 * (1 + η * r) + -2 * (1 + η * r)) * X
  have h1 : (2 * (1 + η * r) + -2 * (1 + η * r)) * X = 0 := by ring_nf
  rw [h1, ← y_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  change (2 * (1 + η * r) + (X + 1 / X)) * X = X ^ 2 + 2 * (1 + η * r) * X + 1
  ring_nf
  rw [mul_inv_cancel₀ (X_ne_zero hs_ne_zero hq_card hq_mod t)]
  ring_nf

lemma ϕ_of_t_eq_zero_one (t : { n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    ϕ.val = (0, 1) := by
  intro ϕ
  unfold ϕ Elligator1.ϕ
  rcases t.prop with h | h <;> simp [h]

lemma η_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    (η P) = 0 := by
  intro P
  unfold η
  let y := P.2
  change (y - 1) / (2 * (y + 1)) = 0
  unfold y P
  rw [ϕ_of_t_eq_zero_one t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  rw [sub_self, zero_div]

lemma y_add_one_eq_two (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let y := P.2
    y + 1 = 2 := by
  intro P y
  unfold y P
  rw [ϕ_of_t_eq_zero_one t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  ring_nf

end η

section comparison

lemma u_comparison (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let u1 := u t
    let ubar := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
    ubar = 1 / u1 := by
  intro t1 t2 u1 ubar
  calc
    ubar = (1 - t2) / (1 + t2) := by simp [ubar, u]
    _ = (1 + t) / (1 - t) := by simp [t2, t1]; ring
    _ = 1 / u1 := by simp [u1, u]

lemma v_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let u1 := u t
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let r := r s
    v2 = 1 / u1 ^ 5 + (r ^ 2 - 2) * 1 / u1 ^ 3 + 1 / u1 := by
  intro t1 t2 u1 v2 r
  let ubar := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
  calc
    v2 = ubar ^ 5 + (r ^ 2 - 2) * ubar ^ 3 + ubar := by rfl
    _ = 1 / u1 ^ 5 + (r ^ 2 - 2) * 1/ u1 ^ 3 + 1 / u1 := by
      unfold ubar u1 t2 t1
      rw [u_comparison t]
      ring

lemma v_comparison_implication1 (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let u1 := u t
    let v1 := v t s
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    v2 * u1 ^ 6 = v1 := by
  intro t1 t2 u1 v1 v2
  let r := r s
  calc
    v2 * u1 ^ 6 = u1 + (r ^ 2 - 2) * u1 ^ 3 + u1 ^ 5 := by
      unfold v2
      rw [v_comparison t]
      grind
    _ = v1 := by grind [v]

lemma v_comparison_implication2 (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let u1 := u t
    let v1 := v t s
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    v2 = v1 / u1 ^ 6 := by
  intro t1 t2 u1 v1 v2
  have hu1_pow6_ne_zero : u1 ^ 6 ≠ 0 := pow_ne_zero 6 (u_ne_zero t)
  rw [← mul_right_inj' hu1_pow6_ne_zero]
  unfold v1
  rw [← v_comparison_implication1 t]
  grind

lemma v_comparison_implication3
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    χ ((u t) ^ 6) = 1 := by
  let u := u t
  have hu6_eq_u2_mul_u2_mul_u2 : u ^ 6 = u ^ 2 * u ^ 2 * u ^ 2 := by ring
  rw [hu6_eq_u2_mul_u2_mul_u2, χ_mul, χ_mul, χ_sq (u_ne_zero t)]
  rw [mul_one, mul_one]

lemma v_comparison_implication4
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let v1 := v t s
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    χ v2 = χ v1 := by
  intro t1 t2 v1 v2
  let u := u t
  unfold v1
  rw [← v_comparison_implication1 t]
  change χ v2 = χ (v2 * u ^ 6)
  rw [χ_mul, v_comparison_implication3 t, mul_one]

lemma X_comparison (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Xbar := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    Xbar = 1 / X1 := by
  intro t1 t2 X1 Xbar
  let u1 := u t
  let ubar := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  calc
    Xbar = (χ v2) * ubar := by rfl
    _ = (χ v1) / u1 := by
      unfold v2 t2
      rw [v_comparison_implication4 t]
      unfold ubar
      rw [u_comparison t]
      change (χ v1) * (1 / u1) = (χ v1) / u1
      ring
    _ = 1 / ((χ v1) * u1) := by
      nth_rw 1 [one_div_χ_of_a_eq_χ_a]
      ring
    _ = 1 / X1 := by rfl

lemma Y_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Y1 := Y t s q
    let Y2 := Y ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s q
    Y2 = Y1 / X1 ^ 3 := by
  intro t1 t2 X1 Y1 Y2
  let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let c := c s
  let r := r s
  let u1 := u t
  let ubar := u ⟨t2, t_h⟩
  let v1 := v t s
  let v2 := v ⟨t2, t_h⟩ s
  have hu1_ne_zero := u_ne_zero (t := t)
  have first_factor :
    ((χ v2) * v2) ^ ((q + 1) / 4) = ((χ v1) * v1) ^ ((q + 1) / 4) * (χ u1) / u1 ^ 3 := by
      have h_v2_mul_v2_eq_v1_mul_v1_div_u1_pow6 : (χ v2) * v2 = (χ v1) * v1 / u1 ^ 6 := by
        rw [v_comparison_implication4 t]
        unfold v2
        rw [v_comparison_implication2 t]
        change (χ v1) * (v1 / u1 ^ 6) = (χ v1) * v1 / u1 ^ 6
        rw [← mul_div_assoc]
      have h_chi_u1_mul_u1_cubed_isSquare : IsSquare ((χ u1) * u1 ^ 3) := by
        have h_chi_u1_mul_u1_cubed_ne_zero : (χ u1) * u1 ^ 3 ≠ 0 := by
          apply mul_ne_zero
          · apply χ_a_ne_zero hu1_ne_zero
          · apply pow_ne_zero 3 hu1_ne_zero
        apply (χ_eq_one_iff_isSquare h_chi_u1_mul_u1_cubed_ne_zero hq_card hq_mod).mp
        have h_three_eq_one_add_two : (3 : ℕ) = 1 + 2 := by norm_num
        rw [h_three_eq_one_add_two, pow_add u1 1 2, ← mul_assoc, pow_one]
        rw [χ_mul, χ_mul]
        rw [χ_χ_eq_χ hq_card hq_mod]
        rw [← χ_mul, ← pow_two]
        have h_u1_sq_isSquare : IsSquare (u1 ^ 2) := IsSquare.sq u1
        have h_chi_u1_sq_eq_one : χ (u1 ^ 2) = 1 := by
          apply (χ_eq_one_iff_isSquare (pow_ne_zero 2 hu1_ne_zero) hq_card hq_mod).mpr
          exact h_u1_sq_isSquare
        simp [h_chi_u1_sq_eq_one]
      have h_u1_pow6_pow_eq_chi_u1_mul_u1_cubed : (u1 ^ 6) ^ ((q + 1) / 4) = (χ u1) * u1 ^ 3 := by
        have h_six_eq_three_mul_two : 6 = 3 * 2 := by norm_num
        rw [h_six_eq_three_mul_two, ← pow_mul, mul_assoc, mul_comm, pow_mul, mul_comm]
        rw [add_comm, one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
        rw [add_comm, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_card hq_mod]
        change ((χ u1) * u1) ^ 3 = (χ u1) * u1 ^ 3
        rw [mul_pow, χ_of_a_pow_n_eq_χ_a u1 ⟨3, by trivial⟩]
      calc
        ((χ v2) * v2) ^ ((q + 1) / 4) = ((χ v1) * v1 / u1 ^ 6) ^ ((q + 1) / 4) := by
          rw [h_v2_mul_v2_eq_v1_mul_v1_div_u1_pow6]
        _ = ((χ v1) * v1) ^ ((q + 1) / 4) * (χ u1) / u1 ^ 3 := by
          rw [div_pow, h_u1_pow6_pow_eq_chi_u1_mul_u1_cubed]
          nth_rw 2 [one_div_χ_of_a_eq_χ_a]
          grind
  have second_factor : (χ v2) = (χ v1) := v_comparison_implication4 t
  have third_factor : χ (ubar ^ 2 + 1 / c ^ 2) = χ (u1 * v1 * (u1 ^ 2 + 1 / c ^ 2)) := by
    calc
      χ (ubar ^ 2 + 1 / c ^ 2)
        = χ ((c ^ 2 * u1 ^ 4 * (ubar ^ 2 + 1 / c ^ 2)) * (u1 ^ 2 + 1 / c ^ 2) ^ 2) := by
        rw [← χ_of_a_eq_χ_a_mul_b_pow_two (c_ne_zero hs_ne_zero hq_card hq_mod)]
        rw [mul_comm, ← χ_of_a_eq_χ_a_mul_b_pow_two (pow_ne_zero 2 hu1_ne_zero)]
        rw [χ_of_a_eq_χ_a_mul_b_pow_two
          (v_factored_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)]
        grind
      _ = χ ((u1 ^ 2 * (c ^ 2 + u1 ^ 2)) * (u1 ^ 2 + 1 / c ^ 2) ^ 2) := by
        rw [pow_two ubar]
        unfold ubar
        rw [u_comparison t]
        change χ (c ^ 2 * u1 ^ 4 * (1 / u1 * (1 / u1) + 1 / c ^ 2) * (u1 ^ 2 + 1 / c ^ 2) ^ 2)
          = χ (u1 ^ 2 * (c ^ 2 + u1 ^ 2) * (u1 ^ 2 + 1 / c ^ 2) ^ 2)
        have h_clear_denominators :
            c ^ 2 * u1 ^ 4 * (1 / u1 * (1 / u1) + 1 / c ^ 2) = u1 ^ 2 * (c ^ 2 + u1 ^ 2) := by
          have hc_sq_ne_zero : c ^ 2 ≠ 0 := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)
          grind
        rw [h_clear_denominators]
      _ = χ (u1 * v1 * (u1 ^ 2 + 1 / c ^ 2)) := by grind [v_factored]
  calc
    Y2 = Y1 * (χ u1) * χ (u1 * v1) / u1 ^ 3 := by
      unfold Y2 Y
      change ((χ v2) * v2) ^ ((q + 1) / 4) * (χ v2) * χ (ubar ^ 2 + 1 / c ^ 2)
        = Y1 * (χ u1) * χ (u1 * v1) / u1 ^ 3
      rw [first_factor, second_factor, third_factor, χ_mul]
      have h_rearrange :
        ((χ v1) * v1) ^ ((q + 1) / 4) * (χ u1) / u1 ^ 3 * (χ v1)
        * (χ (u1 * v1) * (χ (u1 ^ 2 + 1 / c ^ 2)))
        = ((χ v1) * v1) ^ ((q + 1) / 4) * (χ v1) * (χ (u1 ^ 2 + 1 / c ^ 2))
          * (χ u1) * χ (u1 * v1) / u1 ^ 3 := by ring_nf
      rw [h_rearrange]
      rfl
    _ = Y1 / ((χ v1) * u1) ^ 3 := by
      calc
      Y1 * (χ u1) * χ (u1 * v1) / u1 ^ 3 = Y1 * (χ v1) / u1 ^ 3 := by
        rw [χ_mul, ← mul_assoc, mul_assoc Y1, ← χ_mul, ← pow_two, χ_sq hu1_ne_zero, mul_one]
      _ = Y1 / ((χ v1) * u1) ^ (2 + 1) := by
        nth_rw 1 [one_div_χ_of_a_eq_χ_a]
        rw [mul_div_assoc, div_div]
        nth_rw 1 [← χ_of_a_pow_n_eq_χ_a v1 ⟨3, by trivial⟩, ← mul_pow]
        ring_nf
    _ = Y1 / X1 ^ 3 := by rfl

lemma X_comparison_implication (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Xbar := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let η := η P
    let r := r s
    X1 + Xbar = -2 * (1 + η * r) := by
  intro t1 t2 X1 Xbar P η r
  unfold Xbar
  rw [X_comparison t]
  exact (y_h3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod)

lemma X_comparison_implication2 (t : { t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Xbar := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    Xbar * X1 = 1 := by
  intro t1 t2 X1 Xbar
  unfold Xbar
  rw [X_comparison t]
  rw [← inv_eq_one_div, inv_mul_cancel₀ (X_ne_zero hs_ne_zero hq_card hq_mod t)]

lemma x_comparison
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

lemma y_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let y1 := y t s
    let y2 := y ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    y2 = y1 := by
  intro t1 t2 y1 y2
  let c := c s
  let r := r s
  let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let X1 := X t s
  let Xbar := X ⟨t2, t_h⟩ s
  calc
    y2 = (r * Xbar - (1 + Xbar) ^ 2) / (r * Xbar + (1 + Xbar) ^ 2) := by rfl
    _ = (r * (1 / X1) - (1 + (1 / X1)) ^ 2) / (r * (1 / X1) + (1 + (1 / X1)) ^ 2) := by
      unfold Xbar
      rw [X_comparison t]
    _ = (r * X1 - (X1 + 1) ^ 2) / (r * X1 + (X1 + 1) ^ 2) := by grind
    _ = y1 := by
      rw [add_comm]
      rfl

lemma P_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    have t_h : (t2 ≠ 1 ∧ t2 ≠ -1) := neg_t_ne_one_and_neg_t_ne_neg_one t
    let y1 := y t s
    let y2 := y ⟨t2, t_h⟩ s
    let x1 := x t s q
    let x2 := x ⟨t2, t_h⟩ s q
    (x1, y1) = (x2, y2) := by
  intro t1 t2 t_h y1 y2 x1 x2
  unfold x2 y2
  rw [x_comparison t hs_ne_zero hq_card hq_mod]
  rw [y_comparison]

end comparison

section Xbar

/-- Xbar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:Xbar"
  (title := "The reconstructed coordinate $\\bar X$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\eta$ as above, define
  $$
  \bar X = -(1 + \eta r) + ((1 + \eta r) ^ 2 - 1)^{(q+1)/4} .
  $$
  -/)]
def Xbar (s : F) (P : F × F) (q : ℕ) : F :=
    let η := η P
    let r := r s
    (-(1 + η * r) + ((1 + η * r) ^ 2 - 1) ^ ((q + 1) / 4))

lemma Xbar_eq_neg_one
    (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let Xbar := Xbar s P.1 q
    Xbar = -1 := by
  intro P Xbar
  unfold Xbar ReconstructionCoordinates.Xbar
  let η := η P.1
  change -(1 + η * (r s)) + ((1 + η * (r s)) ^ 2 - 1) ^ ((q + 1) / 4) = -1
  unfold η
  rw [η_eq_zero t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  ring_nf
  rw [zero_pow, add_zero]
  omega

end Xbar

section z

/-- z is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:z"
  (title := "The inversion sign $z$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\bar X$ as above, define
  $$
  z = \chi\bigl((c - 1)s\bar X(1 + \bar X)x(\bar X ^ 2 + 1/c ^ 2)\bigr) .
  $$
  -/)]
def z (s : F) (P : F × F) (q : ℕ) : F :=
    let x := P.fst
    let c := c s
    let Xbar := Xbar s P q
    χ ((c - 1) * s * Xbar * (1 + Xbar) * x * (Xbar ^ 2 + 1 / c ^ 2))

lemma z_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let z := z s P q
    z = 0 := by
  intro P z
  unfold z ReconstructionCoordinates.z
  let c := c s
  repeat rw [Xbar_eq_neg_one t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  simp_all

omit [DecidableEq F] in
lemma X_pow_two_add_1_div_c_pow_two_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) :
    let X := Xbar s P q
    let c := c s
    X ^ 2 + 1 / c ^ 2 ≠ 0 := by
  intro X c h
  rw [← mul_left_inj' (c_ne_zero hs_ne_zero hq_card hq_mod)] at h
  rw [← mul_left_inj' (c_ne_zero hs_ne_zero hq_card hq_mod)] at h
  ring_nf at h
  change X ^ 2 * c ^ 2 + c⁻¹^2 * c ^ 2 = 0 at h
  rw [inv_pow c 2, inv_mul_cancel₀ (pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod))] at h
  rw [← add_left_inj (-1 : F), ← mul_pow] at h
  simp only [add_neg_cancel_right, zero_add] at h
  let h' := neg_one_non_square hq_card hq_mod
  have h'' : IsSquare (-1 : F) := by
    rw [← h, pow_two]
    apply IsSquare.mul_self
  contradiction

end z

section ubar

/-- ubar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:ubar"
  (title := "The reconstructed quantity $\\bar u$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $z$ and $\bar X$ as above, define
  $$
  \bar u = z\bar X .
  $$
  -/)]
def ubar (s : F) (P : F × F) (q : ℕ) : F :=
    let Xbar := Xbar s P q
    let z := z s P q
    z * Xbar

lemma ubar_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let ubar := ubar s P q
    ubar = 0 := by
  grind [z_eq_zero, ubar]

lemma ubar_eq_u (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      let X := X t s
      let Xbar := Xbar s P q
      Xbar = X) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let u := u t
    let ubar := ubar s P q
    ubar = u := by
  intro P u ubar
  let X := X t s
  let Xbar := Xbar s P q
  let c := c s
  let x := x t s q
  let Y := Y t s q
  let z := z s P q
  let v := v t s;
  let χ_of_v := χ v
  let χ_of_Y := χ Y
  unfold ubar ReconstructionCoordinates.ubar
  rw [hXXbar]
  change z * X = u
  have hXbar_expand_eq_x_mul_Y : (c - 1) * s * Xbar * (1 + Xbar) = x * Y := by
    unfold Xbar
    rw [hXXbar]
    rw [← div_left_inj' (Y_ne_zero hs_ne_zero hq_card hq_mod t)]
    change x = x * Y / Y
    rw [mul_div_assoc, div_self (Y_ne_zero hs_ne_zero hq_card hq_mod t)]
    ring_nf
  have hz_eq_χY_mul_χ_sum : z = χ_of_Y * χ (X ^ 2 + 1 / c ^ 2) := by
    calc
      z = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2)) := by
        unfold z ReconstructionCoordinates.z
        change χ ((c - 1) * s * Xbar * (1 + Xbar) * P.1 * (Xbar ^ 2 + 1 / c ^ 2))
          = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2))
        unfold P ϕ
        simp only [hXbar_expand_eq_x_mul_Y]
        rw [dite_eq_left t.prop]
        change χ (x * Y * x * (Xbar ^ 2 + 1 / c ^ 2)) = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2))
        unfold Xbar X
        rw [hXXbar]
        ring_nf
      _ = χ_of_Y * χ (X ^ 2 + 1 / c ^ 2) := by
        rw [χ_mul, χ_mul]
        rw [χ_a_eq_one (pow_ne_zero 2
          (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t))
          (IsSquare.sq x)]
        unfold χ_of_Y
        ring
  have hχu_sum_eq_χX_sum : χ (u ^ 2 + 1 / c ^ 2) = χ (X ^ 2 + 1 / c ^ 2) := by
    unfold X AuxiliaryCoordinates.X
    rw [mul_pow]
    nth_rw 3 [pow_two]
    rw [← χ_mul]
    rw [← pow_two, χ_a_eq_one
      (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod t)) (IsSquare.sq v)]
    unfold u
    simp_all
  have hχY_eq_χv_mul_χ_sum : χ_of_Y = χ_of_v * χ (X ^ 2 + 1 / c ^ 2) := by
    rw [← hχu_sum_eq_χX_sum]
    unfold χ_of_Y Y AuxiliaryCoordinates.Y
    let χ_sum := χ (u ^ 2 + 1 / c ^ 2)
    change χ ((χ_of_v * v) ^ ((q + 1) / 4) * χ_of_v * χ_sum) = χ_of_v * χ_sum
    rw [mul_assoc, χ_mul]
    rw [χ_a_eq_one
      (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero t hs_ne_zero hq_card hq_mod)
      (χ_IsSquare_h1 t hs_ne_zero hq_card hq_mod)]
    rw [χ_mul]
    rw [χ_χ_eq_χ hq_card hq_mod]
    rw [χ_χ_eq_χ hq_card hq_mod]
    unfold χ_of_v χ_sum
    simp_all
  have hz_eq_χv : z = χ_of_v := by
    rw [hz_eq_χY_mul_χ_sum, hχY_eq_χv_mul_χ_sum, mul_assoc, ← χ_mul, ← pow_two]
    rw [χ_a_eq_one
      (pow_ne_zero 2 (X_pow_two_add_one_div_c_pow_two_ne_zero hs_ne_zero hq_card hq_mod t))
      (IsSquare.sq (X ^ 2 + 1 / c ^ 2))]
    simp
  rw [hz_eq_χv]
  unfold X AuxiliaryCoordinates.X
  change χ_of_v * (χ_of_v * u) = u
  rw [← mul_assoc, ← χ_mul, ← pow_two]
  have hv_sq_isSquare : IsSquare (v ^ 2) := IsSquare.sq v
  rw [χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod t)) hv_sq_isSquare]
  simp

lemma ubar_eq_u' (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
      let Xbar := Xbar s P q
      Xbar = X') :
    let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let u' := u ⟨-t.val, t_h⟩
    let ubar := ubar s P q
    ubar = u' := by
  intro t_h P u' ubar
  let X' := X ⟨-t.val, t_h⟩ s
  let X := X t s
  let Xbar := Xbar s P q
  let c := c s
  let x' := x ⟨-t.val, t_h⟩ s q
  let x := x t s q
  let Y' := Y ⟨-t.val, t_h⟩ s q
  let Y := Y t s q
  let z := z s P q
  let v' := v ⟨-t.val, t_h⟩ s
  let v := v t s;
  unfold ubar ReconstructionCoordinates.ubar
  rw [hXXbar]
  change z * X' = u'
  have hXbar_expand_eq_x'_mul_Y' : (c - 1) * s * Xbar * (1 + Xbar) = x' * Y' := by
    unfold Xbar
    rw [hXXbar]
    rw [← div_left_inj' (Y_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩)]
    change x' = x' * Y' / Y'
    rw [mul_div_assoc, div_self (Y_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩)]
    ring_nf
  have hz_eq_χY'_mul_χ_sum : z = (χ Y') * (χ (X'^2 + 1 / c ^ 2)) := by
    calc
      z = (χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))) := by
        unfold z ReconstructionCoordinates.z
        change χ ((c - 1) * s * Xbar * (1 + Xbar) * P.1 * (Xbar ^ 2 + 1 / c ^ 2))
          = χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))
        unfold P ϕ
        simp only [hXbar_expand_eq_x'_mul_Y']
        rw [dite_eq_left t.prop]
        change χ (x' * Y' * x * (Xbar ^ 2 + 1 / c ^ 2)) = χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))
        unfold Xbar X' x' x
        rw [x_comparison t hs_ne_zero hq_card hq_mod]
        rw [hXXbar]
        ring_nf
      _ = (χ Y') * χ (X'^2 + 1 / c ^ 2) := by
        rw [χ_mul]
        rw [χ_mul]
        rw [χ_a_eq_one (pow_ne_zero 2
          (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod ⟨-t, t_h⟩))
          (IsSquare.sq x')]
        ring_nf
  have hχu'_sum_eq_χX'_sum : (χ (u'^2 + 1 / c ^ 2)) = (χ (X'^2 + 1 / c ^ 2)) := by
    unfold X' AuxiliaryCoordinates.X
    rw [mul_pow]
    nth_rw 3 [pow_two]
    rw [← χ_mul]
    rw [← pow_two, χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod ⟨-t, t_h⟩))
      (IsSquare.sq v')]
    unfold u'
    simp_all
  have hχY'_eq_χv'_mul_χ_sum : (χ Y') = (χ v') * (χ (X'^2 + 1 / c ^ 2)) := by
    rw [← hχu'_sum_eq_χX'_sum]
    unfold Y' AuxiliaryCoordinates.Y
    let χ_sum := χ (u'^2 + 1 / c ^ 2);
    change (χ (((χ v') * v') ^ ((q + 1) / 4) * (χ v') * χ_sum)) = (χ v') * χ_sum
    rw [mul_assoc, χ_mul]
    rw [χ_a_eq_one
      (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero ⟨-t.val, t_h⟩ hs_ne_zero hq_card hq_mod)
      (χ_IsSquare_h1 ⟨-t.val, t_h⟩ hs_ne_zero hq_card hq_mod)]
    rw [χ_mul, χ_χ_eq_χ hq_card hq_mod]
    rw [χ_χ_eq_χ hq_card hq_mod]
    unfold χ_sum
    simp_all
  have hz_eq_χv' : z = (χ v') := by
    rw [hz_eq_χY'_mul_χ_sum, hχY'_eq_χv'_mul_χ_sum, mul_assoc]
    rw [← χ_mul, ← pow_two]
    rw [χ_a_eq_one (pow_ne_zero 2
        (X_pow_two_add_one_div_c_pow_two_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩))
      (IsSquare.sq (X'^2 + 1 / c ^ 2))]
    simp
  rw [hz_eq_χv']
  unfold X' AuxiliaryCoordinates.X
  change (χ v') * ((χ v') * u') = u'
  rw [← mul_assoc, ← χ_mul, ← pow_two]
  have hv'_sq_isSquare : IsSquare (v'^2) := IsSquare.sq v'
  rw [χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩))
    hv'_sq_isSquare]
  simp

lemma one_add_ubar_ne_zero_base_case (t : {n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    let ubar := ubar s P q
    1 + ubar ≠ 0 := by
  intro P ubar
  unfold ubar
  rw [ubar_eq_zero, add_zero]
  exact one_ne_zero' F

end ubar

section tbar

/-- tbar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:tbar"
  (title := "The reconstructed preimage $\\bar t$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\bar u$ as above, define
  $$
  \bar t = (1 - \bar u)/(1 + \bar u) .
  $$
  -/)]
def tbar (s : F) (P : F × F) (q : ℕ) : F :=
    let ubar := ubar s P q
    (1 - ubar) / (1 + ubar)

lemma tbar_eq_one (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let tbar := tbar s P q
    tbar = 1 := by
  intro P tbar_of_P
  unfold tbar_of_P tbar
  let ubar_of_P := ubar s P q
  change (1 - ubar_of_P) / (1 + ubar_of_P) = 1
  unfold ubar_of_P
  rw [ubar_eq_zero t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  simp

lemma tbar_eq_t (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let X := X t s
      let Xbar := Xbar s P q
      Xbar = X) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let tbar_of_P := tbar s P q
    tbar_of_P = t := by
  intro P tbar_of_P
  let u := u t
  let ubar := ubar s P q
  have h : ubar = u := ubar_eq_u t hs_ne_zero sq_ne_pm_two hq_card hq_mod hXXbar
  unfold u AuxiliaryCoordinates.u at h
  unfold tbar_of_P tbar
  change (1 - ubar) / (1 + ubar) = t.val
  change ubar = (1 - t.val) / (1 + t.val) at h
  rw [h, sub_div' (one_add_t_ne_zero t)]
  rw [add_div' (1 - t.val) 1 (1 + t.val) (one_add_t_ne_zero t)]
  rw [div_div_div_eq]
  have h' : (1 + t.val) * 2 ≠ 0 := mul_ne_zero (one_add_t_ne_zero t) (two_ne_zero hq_card hq_mod)
  grind

lemma tbar_eq_t' (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
      let Xbar := Xbar s P q
      Xbar = X')
    :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let tbar_of_P := tbar s P q
    let t' := -t.val
    tbar_of_P = t' := by
  intro P tbar_of_P t'
  have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let u' := u ⟨t', t_h⟩
  let ubar := ubar s P q
  let h : ubar = u' := ubar_eq_u' t hs_ne_zero sq_ne_pm_two hq_card hq_mod hXXbar
  unfold u' u at h
  unfold tbar_of_P tbar
  change (1 - ubar) / (1 + ubar) = t'
  change ubar = (1 - t') / (1 + t') at h
  rw [h, sub_div' (one_add_t_ne_zero ⟨t', t_h⟩)]
  rw [add_div' (1 - t') 1 (1 + t') (one_add_t_ne_zero ⟨t', t_h⟩), div_div_div_eq]
  have h' : ((1 + t') * 2) ≠ 0 :=
    mul_ne_zero (one_add_t_ne_zero ⟨t', t_h⟩) (two_ne_zero hq_card hq_mod)
  grind

end tbar

end Elligator.Elligator1.ReconstructionCoordinates
