/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Elligator.Elligator1.Map

/-!
# Map Properties

In this file we introduce lemmas, which are directly derivable from the main results in
`Elligator.Elligator1.Map`.

These results are mainly used for Theorem 3 proof part A, i.e. results only proofable right in
between Theorem 1 and proof part B.

This hierarchy allows to have a linear dependence hierarchy without polluting major result files.

## References

See [bernstein2013a], Section 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

-- Used in Theorem 3 Proof B part as implication for P_in_ϕOverF_with_prop2_main_case
-- argument.
lemma y_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let y := y t s
  let r := r s
  let X := X t s
  X^2 + (2 + r * (y - 1) / (y + 1)) * X + 1 = 0 := by
    intro y r X
    rw [← mul_left_inj' (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
    change (X^2 + (2 + r * (y - 1) / (y + 1)) * X + 1) * (y + 1) = 0 * (y + 1)
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
      ring_nf
    have h2 : (2 * (y + 1) + r * (y - 1)) = (y * r - r + 2 * y + 2) := by ring_nf
    rw [h1, h2, mul_add, add_mul]
    ring_nf
    rw [← add_right_inj (r * X - 1 - 2 * X - X^2)]
    ring_nf
    rw [mul_comm (X^2) y, mul_comm X y, mul_assoc, mul_assoc]
    nth_rw 4 [← mul_one y]
    rw [add_assoc, ← mul_add y]
    rw [add_assoc, ← mul_add y, add_comm (X^2) 1, ← add_assoc, add_comm (X * 2) 1]
    rw [mul_comm X 2]
    have h3 : 1 + 2 * X + X^2 = (1 + X)^2 := by ring_nf
    have h4 : -1 + r * X - 2 * X - X^2 = r * X - (1 + 2 * X + X^2) := by ring_nf
    rw [h4, h3]
    rw [← mul_assoc, mul_comm, ← mul_add]
    rw [← div_left_inj' (y_divisor_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t)]
    change (y * (r * X + (1 + X)^2)) / (r * X + (1 + X)^2) = y
    rw [mul_div_assoc]
    rw [div_self (y_divisor_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t)]
    simp

-- Implicated by y_h1. Saved for further proof arguments in Theorem 3 Proof B
lemma y_h2
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let r := r s
  let X := X t s
  let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
  let η := η P
  X^2 + 2 * (1 + η * r) * X + 1 = 0 := by
    intro r X P η
    let y := y t s
    calc
      X^2 + 2 * (1 + η * r) * X + 1
      = X^2 + 2 * (1 + 1 / 2 * ((y - 1) / (y + 1)) * r) * X + 1 := by
        -- Unfold until reaching the y which is equivalent to y for comparison
        unfold η Elligator1.η P ϕ
        simp only [Subtype.coe_eta, dite_eq_ite, one_div]
        rw [if_pos t.prop]
        change X^2 + 2 * (1 + (y - 1) / (2 * (y + 1)) * r) * X + 1
          = X^2 + 2 * (1 + 2⁻¹ * ((y - 1) / (y + 1)) * r) * X + 1
        rw [inv_eq_one_div, ← mul_div_mul_comm]
        ring_nf
      _ = X^2 + (2 + r * (y - 1) / (y + 1)) * X + 1 := by
        rw [mul_add 2]
        rw [div_eq_mul_inv 1 2, mul_one, one_mul, mul_assoc, ← mul_assoc]
        rw [mul_inv_cancel₀ (two_ne_zero hq_card hq_mod)]
        ring_nf
      _ = 0 := by rw [y_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod]

-- Implicated by y_h2.
lemma y_h3
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
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
    change (2 * (1 + η * r) + (X + 1 / X)) * X = X^2 + 2 * (1 + η * r) * X + 1
    ring_nf
    rw [mul_inv_cancel₀ (X_ne_zero hs_ne_zero hq_card hq_mod t)]
    ring_nf

lemma X_comparison_implication
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let X1 := X t s
  let X2 := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
  let η_of_P := η P
  let r := r s
  X1 + X2 = -2 * (1 + η_of_P * r) := by
    intro t1 t2 X1 X2 P η_of_P r
    unfold X2
    rw [X_comparison t]
    exact (y_h3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod)

lemma X_comparison_implication2
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let X1 := X t s
  let X2 := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  X2 * X1 = 1 := by
    intro t1 t2 X1 X2
    unfold X2
    rw [X_comparison t]
    rw [← inv_eq_one_div]
    rw [inv_mul_cancel₀ (X_ne_zero hs_ne_zero hq_card hq_mod t)]

lemma χ_IsSquare_h1
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let v := v t s
  IsSquare (((χ v) * v)^((q + 1) / 4)) := by
    intro v
    have v_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
    have h1 := χ_a_mul_a_IsSquare v_ne_zero hq_card hq_mod
    unfold IsSquare at h1
    rcases h1 with ⟨r, hr⟩
    rw [hr, ← pow_two, ← pow_mul, mul_comm, pow_mul]
    apply IsSquare.sq

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
    let X2 := X ⟨t2, t_h⟩ s
    calc
      y2 = (r * X2 - (1 + X2)^2) / (r * X2 + (1 + X2)^2) := by rfl
      _ = (r * (1 / X1) - (1 + (1 / X1))^2) / (r * (1 / X1) + (1 + (1 / X1))^2) := by
        unfold X2
        rw [X_comparison t]
      _ = (r * X1 - (X1 + 1)^2) / (r * X1 + (X1 + 1)^2) := by grind
      _ = y1 := by
        rw [add_comm]
        unfold y1 y X1
        simp
        rfl

lemma P_comparison
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
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

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (η_h1 :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let r := r s
    let η_of_P := η P
    η_of_P * r = -2)
  :
  let X := X t s
  (X - 1)^2 = 0 := by
    intro X
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let r := r s
    let η := η P.val
    have h : X + 1 / X = -2 * (1 + η * r) :=
      y_h3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    rw [η_h1] at h
    ring_nf at h
    rw [← mul_left_inj' (X_ne_zero hs_ne_zero hq_card hq_mod t), add_mul] at h
    change X * X + X⁻¹ * X = 2 * X at h
    rw [← add_left_inj (2 * X)]
    ring_nf
    rw [inv_mul_cancel₀ (X_ne_zero hs_ne_zero hq_card hq_mod t)] at h
    rw [pow_two, add_comm]
    nth_rw 2 [mul_comm]
    exact h

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h2
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (η_h1 :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let r := r s
    let η_of_P := η P.val
    η_of_P * r = -2)
  :
  let X := X t s
  X = 1 := by
    intro X
    have h1 : (X - 1)^2 = 0 := X_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod η_h1
    grind

-- Used in the main case of Theorem 3 Proof part B
lemma u_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (η_h1 :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let r := r s
    let η_of_P := η P
    η_of_P * r = -2)
  :
  let u := u t;
  u = 1 := by
    intro u
    let X := X t s
    let v := v t s
    let χ_of_v := χ v
    have v_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
    have h1 : X = χ_of_v * u := by rfl
    unfold X at h1
    rw [X_η_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod η_h1] at h1
    rcases χ_values (a := v)
    · rename_i h2
      change χ_of_v = 0 at h2
      have h3 := a_eq_zero_of_χ_of_a_eq_zero (a := v)
      have h4 : v = 0 := by apply h3 h2
      contradiction
    · rename_i h2
      rcases h2
      · rename_i h2
        change χ_of_v = -1 at h2
        rw [h2] at h1
        unfold u Elligator1.u at h1
        have two_ne_zero := two_ne_zero hq_card hq_mod
        have h3 : (2 : F) = 0 := by grind
        contradiction
      · rename_i h2
        grind

-- Used in the main case of Theorem 3 Proof part B
lemma t_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (η_h1 :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let r := r s
    let η_of_P := η P
    η_of_P * r = -2)
  :
  t.val = 0 := by
    let u := u t
    have h1 : u = 1 := u_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod η_h1
    unfold u Elligator1.u at h1
    have h4_1 : 1 + t.val ≠ 0 := one_add_t_ne_zero t
    rw [← mul_right_inj' h4_1, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self h4_1] at h1
    rw [← add_left_inj (t.val - 1)] at h1
    ring_nf at h1
    symm at h1
    rw [← div_left_inj' (two_ne_zero hq_card hq_mod)] at h1
    ring_nf at h1
    rw [mul_assoc, inv_mul_cancel₀ (two_ne_zero hq_card hq_mod), mul_one] at h1
    exact h1

-- Used in the main case of Theorem 3 Proof part B
lemma v_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (η_h1 :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let r := r s
    let η_of_P := η P
    η_of_P * r = -2)
  :
  let v := v t s;
  let r := r s
  v = r^2 := by
    intro v r
    unfold v Elligator1.v
    rw [u_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod η_h1]
    ring

-- Used in the main case of Theorem 3 Proof part B
lemma Y_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (η_h1 :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let r := r s
    let η_of_P := η P
    η_of_P * r = -2)
  :
  let Y := Y t s q
  let c := c s
  let r := r s
  Y = r * (χ c) := by
    intro Y c r
    have c_ne_zero := c_ne_zero hs_ne_zero hq_card hq_mod
    calc
      Y = (r^2)^((q + 1) / 4) * χ (1 + 1 / c^2) := by
        unfold Y Elligator1.Y
        rw [v_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod η_h1]
        rw [u_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod η_h1]
        change (χ (r^2) * r^2)^((q + 1) / 4) * χ (r^2) * (χ (1^2 + 1 / c^2))
          = (r^2)^((q + 1) / 4) * χ (1 + 1 / c^2)
        have h1 : r^2 ≠ 0 := pow_ne_zero 2 (r_ne_zero hs_ne_zero hq_card hq_mod)
        have h2 : IsSquare (r^2) := IsSquare.sq r
        rw [χ_a_eq_one h1 h2]
        nth_rw 2 [pow_two]
        rw [mul_one, one_mul, mul_one]
      _ = (χ r) * r * χ (r / c) := by
        have h : 1 + 1 / c^2 = (c + 1 / c) / c := by grind
        rw [h]
        change (r^2)^((q + 1) / 4) * χ (r / c) = (χ r) * r * χ (r / c)
        rw [b_pow_q_add_one_div_four_eq_χ_of_a_mul_a hq_card hq_mod]
      _ = r * (χ c) := by
        have r_ne_zero := r_ne_zero hs_ne_zero hq_card hq_mod
        let χ_of_one_div_c := χ (1 / c)
        calc
          (χ r) * r * χ (r / c) = r * (χ r) * (χ r) * χ_of_one_div_c := by
            grind [χ_mul]
          _ = r * 1 * χ_of_one_div_c := by
            rw [mul_assoc r, ← χ_mul]
            rw [← pow_two]
            rw [χ_sq r_ne_zero]
          _ = r * (χ c) := by
            unfold χ_of_one_div_c
            rw [← χ_inv]
            rw [mul_one]

-- Implicated by main case of Theorem 3 proof part B.
lemma y_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (η_h1 :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let r := r s
    let η_of_P := η P
    η_of_P * r = -2)
  :
  let r := r s
  let y := y t s
  y = (r - 4) / (r + 4) := by
    intro r y
    unfold y Elligator1.y
    let X := X t s
    change (r * X - (1 + X)^2) / (r * X + (1 + X)^2) = (r - 4) / (r + 4)
    unfold X
    rw [X_η_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod η_h1]
    ring_nf

lemma y_of_zero (hs_ne_zero : s ≠ 0) (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
  let y := y ⟨(0 : F), by simp⟩ s
  let r := r s
  y = (r - 4) / (r + 4) := by
    intro y r
    unfold y Elligator1.y
    rw [X_of_zero hs_ne_zero hq_card hq_mod]
    change (r * 1 - (1 + 1)^2) / (r * 1 + (1 + 1)^2) = (r - 4) / (r + 4)
    ring_nf

lemma ϕ_of_t_eq_zero_one
  (t : { n : F // n = 1 ∨ n = -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let ϕ := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
  ϕ.val = (0, 1) := by
    intro ϕ
    unfold ϕ Elligator1.ϕ
    rcases t.prop with h | h <;> simp [h]

lemma y_add_one_eq_two
  (t : { t : F // t = 1 ∨ t = -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
  let y := P.2
  y + 1 = 2 := by
    intro P y
    unfold y P
    rw [ϕ_of_t_eq_zero_one t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
    ring_nf

/-- `ϕOverFProp1` is the first property fulfilled by Ps in `EOverF`.
This property does not have to consider a dedicated field `F` with `q`.
This restriction is defined during the context evolution.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp1"
  (title := "Image condition 1: $y + 1 \\neq 0$")
  (statement := /--
  The first of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies
  $$
  y + 1 \neq 0 .
  $$
  -/)]
def ϕOverFProp1 (P : F × F) : Prop :=
  let y := P.snd
  y + 1 ≠ 0

/-- `ϕOverFProp2` is the second property fulfilled by Ps in `EOverF`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp2"
  (title := "Image condition 2: $(1 + \\eta r)^2 - 1$ is a square")
  (statement := /--
  The second of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies that
  $$
  (1 + \eta r)^2 - 1
  $$
  is a square, where $\eta = (y - 1)/(2(y + 1))$.
  -/)]
def ϕOverFProp2 (s : F) (P : F × F) : Prop :=
  let r := r s
  let η := η P
  IsSquare ((1 + η * r)^2 - 1)

/-- `ϕOverFProp3` is the third property fulfilled by Ps in `EOverF`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp3"
  (title := "Image condition 3: the exceptional case $\\eta r = -2$")
  (statement := /--
  The third of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies that if $\eta r = -2$ then
  $$
  x = 2s(c - 1)\chi(c)/r .
  $$
  -/)]
def ϕOverFProp3 (s : F) (P : F × F) : Prop :=
  let x := P.fst
  let c := c s
  let r := r s
  let η := η P
  η * r = -2 → x = 2 * s * (c - 1) * (χ c) / r

/-- `ϕOverFProps` combines the previously defined properties which are fulfilled by Ps
in `EOverF`, i.e. `ϕOverFProp1`, `ϕOverFProp2` and `ϕOverFProp3`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProps"
  (title := "The image conditions of Theorem 3")
  (statement := /--
  The conjunction of the three conditions of Theorem 3 for a point $(x, y) \in E(\mathbb{F}_q)$:
  $y + 1 \neq 0$; $(1 + \eta r)^2 - 1$ is a square, where $\eta = (y - 1)/(2(y + 1))$; and if
  $\eta r = -2$ then $x = 2s(c - 1)\chi(c)/r$.
  -/)]
def ϕOverFProps (s : F) (P : F × F) : Prop :=
  ϕOverFProp1 P ∧ ϕOverFProp2 s P ∧ ϕOverFProp3 s P

/-- `ϕOverF` is the set of Ps produced by `ϕ`.

Original: Section "3.2 The map", Definition 2
-/
@[blueprint "def:ϕOverF"
  (title := "The image $\\varphi(\\mathbb{F}_q)$")
  (statement := /--
  The image of the decoding function of Definition 2,
  $$
  \varphi(\mathbb{F}_q) = \{\varphi(t) : t \in \mathbb{F}_q\} \subseteq E(\mathbb{F}_q) .
  $$
  -/)]
def ϕOverF
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : Set (F × F)
  := Set.range (fun t : F => ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod)

lemma P_in_ϕOverF_with_prop1_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
  ϕOverFProp1 P := by
    intro P
    unfold ϕOverFProp1
    intro y
    unfold y P ϕ
    let two_ne_zero := two_ne_zero hq_card hq_mod
    simp only [not_t_ne_one_and_t_ne_neg_one]
    norm_num
    exact two_ne_zero

lemma P_in_ϕOverF_with_prop1_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
  ϕOverFProp1 P := by
    intro P
    unfold ϕOverFProp1
    intro y
    unfold y P ϕ
    dsimp
    rw [dif_pos t.prop]
    exact y_add_one_ne_zero hs_ne_zero hq_card hq_mod t

-- Original: Theorem 3.2 Proof B prop 1 argumentation
lemma P_in_ϕOverF_with_prop1
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
  ϕOverFProp1 P := by
    intro P
    unfold ϕOverFProp1
    intro y
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · exact P_in_ϕOverF_with_prop1_main_case ⟨t, h1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq, ← not_or, not_not] at h1
        exact h1
      exact P_in_ϕOverF_with_prop1_base_case
        ⟨t, h1_1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod

lemma P_in_ϕOverF_with_prop2_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
  ϕOverFProp2 s P := by
    intro P
    unfold ϕOverFProp2
    intro r η
    have h1 : ¬ (t.val ≠ 1 ∧ t.val ≠ -1) := by
      rcases t.prop with h'' | h'' <;> simp [h'']
    unfold η Elligator1.η P ϕ
    simp_all [not_t_ne_one_and_t_ne_neg_one]

lemma P_in_ϕOverF_with_prop2_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
  ϕOverFProp2 s P := by
    intro P
    unfold ϕOverFProp2
    let r := r s
    let X := X t s
    let y := y t s
    let c := c s
    let η := η P
    have h1 : X^2 + 2 * (1 + η * r) * X + 1 = 0 := y_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    have h2 : NeZero (2 : F) := by
      rw [neZero_iff]
      apply (two_ne_zero hq_card hq_mod)
    rw [pow_two] at h1
    nth_rw 1 [← one_mul X, mul_assoc] at h1
    change IsSquare ((1 + η * r) ^ 2 - 1)
    rw [@quadratic_eq_zero_iff_discrim_eq_sq
      F _ 1 (2 * (1 + η * r)) 1 h2 _ FiniteFieldBasic.one_ne_zero X] at h1
    unfold discrim at h1
    rw [mul_pow 2 _ 2] at h1
    have h3 : 2^2 = (4 : F) := by norm_num
    rw [mul_one, h3, ← mul_sub, mul_comm] at h1
    rw [← div_left_inj' (four_ne_zero hq_card hq_mod)] at h1
    rw [mul_div_assoc, div_self (four_ne_zero hq_card hq_mod)] at h1
    rw [mul_one, ← h3, ← div_pow _ _ 2] at h1
    rw [h1]
    apply IsSquare.sq

-- Original: Theorem 3.2 Proof B prop 2 argumentation
lemma P_in_ϕOverF_with_prop2
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
  ϕOverFProp2 s P := by
    intro P
    unfold ϕOverFProp2
    intro y
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · exact P_in_ϕOverF_with_prop2_main_case ⟨t, h1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq] at h1
        rw [← not_or, not_not] at h1
        exact h1
      exact P_in_ϕOverF_with_prop2_base_case ⟨t, h1_1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod

lemma P_in_ϕOverF_with_prop3_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
  ϕOverFProp3 s P := by
    intro P
    unfold ϕOverFProp3
    intro x c r η h
    have h' : ¬ (t.val ≠ 1 ∧ t.val ≠ -1) := by simp [not_t_ne_one_and_t_ne_neg_one]
    simp only [η, Elligator1.η, P, ϕ, ne_eq] at h
    rw [dif_neg h'] at h
    ring_nf at h
    simp at h
    have h3 := two_ne_zero hq_card hq_mod
    contradiction

lemma P_in_ϕOverF_with_prop3_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
  ϕOverFProp3 s P := by
    intro P
    unfold ϕOverFProp3
    intro x_of_P c r η h1
    let X := X t s
    let Y := Y t s q
    let v := v t s
    let χ_of_c := χ c
    let χ_of_v := χ v
    simp only [x_of_P, P, ϕ]
    rw [dif_pos t.prop]
    unfold x
    change (c - 1) * s * X * (1 + X) / Y = 2 * s * (c - 1) * χ_of_c / r
    unfold X Y
    rw [X_η_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod h1]
    rw [Y_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod h1]
    nth_rw 2 [mul_div_assoc]
    unfold χ_of_c
    nth_rw 2 [one_div_χ_of_a_eq_χ_a]
    grind

-- Original: Theorem 3.2 Proof B prop 3 argumentation
lemma P_in_ϕOverF_with_prop3
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  ϕOverFProp3 s P := by
    intro P
    unfold ϕOverFProp3
    intro y
    by_cases t_h : t ≠ 1 ∧ t ≠ -1
    · exact P_in_ϕOverF_with_prop3_main_case
        ⟨t, t_h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq, ← not_or, not_not] at t_h
        exact t_h
      exact P_in_ϕOverF_with_prop3_base_case ⟨t, h1_1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod

-- Original: Theorem 3.2 Proof B (3.2 forward statement)
@[blueprint "thm:P_props_of_P_in_ϕOverF"
  (title := "Points of $\\varphi(\\mathbb{F}_q)$ satisfy the image conditions")
  (statement := /--
  The forward part of statement 2 of Theorem 3: every $(x, y) \in \varphi(\mathbb{F}_q)$
  satisfies $y + 1 \neq 0$; $(1 + \eta r)^2 - 1$ is a square, where
  $\eta = (y - 1)/(2(y + 1))$; and if $\eta r = -2$ then $x = 2s(c - 1)\chi(c)/r$.
  -/)]
theorem P_props_of_P_in_ϕOverF
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
  P ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod → ϕOverFProps s P := by
    intro P h1
    unfold ϕOverFProps
    and_intros
    · exact P_in_ϕOverF_with_prop1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    · exact P_in_ϕOverF_with_prop2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    · exact P_in_ϕOverF_with_prop3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod

lemma P_of_ϕ_in_ϕOverF
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
  let ϕOverF := ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod
  P ∈ ϕOverF := by simp [ϕOverF]

lemma P_of_ϕ_fulfills_ϕOverFProps
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
  ϕOverFProps s P := by
    intro P
    let h := P_of_ϕ_in_ϕOverF t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    apply P_props_of_P_in_ϕOverF t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod h

end Elligator.Elligator1
