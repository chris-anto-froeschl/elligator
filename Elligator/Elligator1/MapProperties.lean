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
public import Elligator.Elligator1.Map

@[expose] public section

/-!
# Map Properties

In this file we introduce lemmas, which are directly derivable from the main results in `Elligator.Elligator1.Map`.
These results are mainly used for Theorem 3 proof part A, i.e. results only proofable right in between Theorem 1 and proof part B.
This hierarchy allows to have a linear dependence hierarchy without polluting major result files.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section MapProperties

variable {F : Type*} [Field F] [Fintype F]

-- Used in Theorem 3 Proof B part as implication for point_in_ϕ_over_F_with_prop2_main_case
-- argument.
lemma y_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X_of_t^2 + (2 + r_of_s * (y_of_t - 1) / (y_of_t + 1)) * X_of_t + 1 = 0 := by
    intro y_of_t r_of_s X_of_t
    rw [← mul_left_inj' (y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    change (X_of_t ^ 2 + (2 + r_of_s * (y_of_t - 1) / (y_of_t + 1)) * X_of_t + 1) * (y_of_t + 1) = 0 * (y_of_t + 1)
    repeat rw [add_mul]
    rw [zero_mul]
    have h1 : (2 * X_of_t * (y_of_t + 1) + r_of_s * (y_of_t - 1) / (y_of_t + 1) * X_of_t * (y_of_t + 1)) = (2 * (y_of_t + 1) + r_of_s * (y_of_t - 1)) * X_of_t := by
      rw [add_mul _ _ X_of_t]
      rw [← div_left_inj' (y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      change (2 * X_of_t * (y_of_t + 1) + r_of_s * (y_of_t - 1) / (y_of_t + 1) * X_of_t * (y_of_t + 1)) / (y_of_t + 1) = (2 * (y_of_t + 1) * X_of_t + r_of_s * (y_of_t - 1) * X_of_t) / (y_of_t + 1)
      repeat rw [add_div]
      repeat rw [mul_div_assoc, div_self (y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      rw [mul_comm (2 * (y_of_t + 1)) X_of_t, ← mul_assoc]
      nth_rw 2 [mul_div_assoc]
      rw [div_self (y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      ring_nf
    rw [h1]
    have h2 : (2 * (y_of_t + 1) + r_of_s * (y_of_t - 1)) = (y_of_t * r_of_s - r_of_s + 2 * y_of_t + 2) := by ring_nf
    rw [h2]
    rw [mul_add, add_mul]
    ring_nf
    rw [← add_right_inj (r_of_s * X_of_t - 1 - 2 * X_of_t - X_of_t^2)]
    ring_nf
    rw [mul_comm (X_of_t^2) y_of_t, mul_comm X_of_t y_of_t]
    rw [mul_assoc, mul_assoc]
    nth_rw 4 [← mul_one y_of_t]
    rw [add_assoc, ← mul_add y_of_t]
    rw [add_assoc, ← mul_add y_of_t, add_comm (X_of_t^2) 1, ← add_assoc, add_comm (X_of_t * 2) 1]
    rw [mul_comm X_of_t 2]
    have h3 : 1 + 2 * X_of_t + X_of_t^2 = (1 + X_of_t)^2 := by ring_nf
    have h4 : -1 + r_of_s * X_of_t + (-(2 * X_of_t) - X_of_t ^ 2) = r_of_s * X_of_t - (1 + 2 * X_of_t + X_of_t^2) := by ring_nf
    rw [h4, h3]
    rw [← mul_assoc, mul_comm, ← mul_add]
    rw [← div_left_inj' (y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    change (y_of_t * (r_of_s * X_of_t + (1 + X_of_t) ^ 2)) / (r_of_s * X_of_t + (1 + X_of_t) ^ 2) = y_of_t
    rw [mul_div_assoc, div_self (y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    simp

-- Implicated by y_h1. Saved for further proof arguments in Theorem 3 Proof B
lemma y_h2
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
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X_of_t + 1 = 0 := by
    intro r_of_s X_of_t point η_of_point
    let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    calc
      X_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X_of_t + 1 = X_of_t^2 + 2 * (1 + 1 / 2 * ((y_of_t - 1) / (y_of_t + 1)) * r_of_s) * X_of_t + 1 := by
        -- Unfold until reaching the y which is equivalent to y_of_t for comparison
        unfold η_of_point η point ϕ
        simp only [Subtype.coe_eta, dite_eq_ite, one_div]
        rw [if_pos t.prop]
        change X_of_t ^ 2 + 2 * (1 + (y_of_t - 1) / (2 * (y_of_t + 1)) * r_of_s) * X_of_t + 1 = X_of_t ^ 2 + 2 * (1 + 2⁻¹ * ((y_of_t - 1) / (y_of_t + 1)) * r_of_s) * X_of_t + 1
        rw [inv_eq_one_div]
        rw [← mul_div_mul_comm]
        ring_nf
      _ = X_of_t^2 + (2 + r_of_s * (y_of_t - 1) / (y_of_t + 1)) * X_of_t + 1 := by
        rw [mul_add 2]
        rw [div_eq_mul_inv 1 2, mul_one, one_mul, mul_assoc (2⁻¹), ← mul_assoc 2 (2⁻¹) _]
        rw [mul_inv_cancel₀]
        ring_nf
        exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)
      _ = 0 := by
        rw [y_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]

-- Implicated by y_h2.
lemma y_h3
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
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X_of_t + 1 / X_of_t = -2 * (1 + η_of_point * r_of_s) := by
    intro r_of_s X_of_t point η_of_point
    rw [← add_right_inj (2 * (1 + η_of_point * r_of_s))]
    rw [← mul_left_inj' (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    change (2 * (1 + η_of_point * r_of_s) + (X_of_t + 1 / X_of_t)) * X_of_t = (2 * (1 + η_of_point * r_of_s) + -2 * (1 + η_of_point * r_of_s)) * X_of_t
    have h1 : (2 * (1 + η_of_point * r_of_s) + -2 * (1 + η_of_point * r_of_s)) * X_of_t = 0 := by ring_nf
    rw [h1, ← y_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (2 * (1 + η_of_point * r_of_s) + (X_of_t + 1 / X_of_t)) * X_of_t = X_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X_of_t + 1
    ring_nf
    rw [mul_inv_cancel₀ (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    ring_nf

lemma X_comparison_implication
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
  let X1 := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X1 + X2 = -2 * (1 + η_of_point * r_of_s) := by
    intro t1 t2 h2_2 X1 X2 point η_of_point r_of_s
    let u1 := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let v1 := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v1 := LegendreSymbol.χ v1 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v2 := LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold X2
    rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    exact (y_h3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma X_comparison_implication2
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
  let X1 := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X2 * X1 = 1 := by
    intro t1 t2 h2_2 X1 X2
    unfold X2
    rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [← inv_eq_one_div]
    rw [inv_mul_cancel₀ (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]

lemma χ_IsSquare_h1
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
  IsSquare ((χ_of_v * v_of_t)^((q + 1) / 4)) := by
    intro v_of_t χ_of_v
    have v_ne_zero := v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    have h1 := LegendreSymbol.χ_a_mul_a_IsSquare v_of_t v_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold IsSquare at h1
    rcases h1 with ⟨r, hr⟩
    rw [hr, ← pow_two, ← pow_mul, mul_comm, pow_mul]
    apply IsSquare.sq

lemma y_comparison
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
  let y1 := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  y2 = y1 := by
    intro t1 t2 h2_2 y1 y2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X1 := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      y2 = (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2) := by
        change (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2) = (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2)
        rfl
      _ = (r_of_s * (1 / X1) - (1 + (1 / X1))^2) / (r_of_s * (1 / X1) + (1 + (1 / X1))^2) := by
        unfold X2
        rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
      _ = (r_of_s * X1 - (X1 + 1)^2) / (r_of_s * X1 + (X1 + 1)^2) := by
        have h2_10_1 : X1^2 / X1^2 = 1 := by
          have h2_10_1_1 : X1^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          apply div_self h2_10_1_1
        rw [← mul_one ((r_of_s * (1 / X1) - (1 + 1 / X1) ^ 2) / (r_of_s * (1 / X1) + (1 + 1 / X1) ^ 2))]
        nth_rw 7 [← h2_10_1]
        rw [← mul_div_mul_comm]
        rw [sub_mul, add_mul]
        have h2_10_2 : (1 / X1) * X1^2 = X1 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          rw [pow_two, mul_div_assoc, div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
          simp
        have h2_10_3 : (1 + 1 / X1) ^ 2 * X1^2 = (X1 + 1)^2 := by
          rw [← mul_pow _ _ 2]
          rw [add_mul, one_mul]
          rw [mul_comm, ← mul_div_assoc, mul_one]
          rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
        rw [mul_assoc]
        rw [h2_10_2, h2_10_3]
      _ = y1 := by
        rw [add_comm]
        unfold y1 y X1
        simp
        rfl

lemma point_comparison
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
  let y1 := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x1 := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (x1, y1) = (x2, y2) := by
    intro t1 t2 h2_2 y1 y2 x1 x2
    unfold x2 y2
    rw [x_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [y_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  (X_of_t - 1)^2 = 0 := by
    intro X_of_t
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1_1 : X_of_t + 1 / X_of_t = -2 * (1 + η_of_point * r_of_s) := by exact (y_h3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
    rw [η_h1] at h1_1
    ring_nf at h1_1
    rw [← mul_left_inj' (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)] at h1_1
    rw [add_mul] at h1_1
    change X_of_t * X_of_t + X_of_t⁻¹ * X_of_t = 2 * X_of_t at h1_1
    rw [← add_left_inj (2 * X_of_t)]
    ring_nf
    rw [inv_mul_cancel₀ (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)] at h1_1
    rw [pow_two, add_comm]
    nth_rw 2 [mul_comm]
    exact h1_1

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h2
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  X_of_t = 1 := by
    intro X_of_t
    have h1 : (X_of_t - 1)^2 = 0 := by exact (X_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)
    simp at h1
    rw [← add_left_inj (-1)]
    ring_nf
    have h2 : -1 + X_of_t = X_of_t - 1 := by ring_nf
    rw [h2]
    exact h1

-- Used in the main case of Theorem 3 Proof part B
lemma u_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3;
  u_of_t = 1 := by
    intro u_of_t
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    have v_ne_zero := v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    have h1 : X_of_t = χ_of_v_of_t * u_of_t := by
      unfold X_of_t X
      rfl
    unfold X_of_t at h1
    rw [X_η_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1] at h1
    rcases LegendreSymbol.χ_values v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    · rename_i h2
      change χ_of_v_of_t = 0 at h2
      have h3 := LegendreSymbol.a_eq_zero_of_χ_of_a_eq_zero v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
      have h4 : v_of_t = 0 := by
        apply h3 h2
      contradiction
    · rename_i h2
      rcases h2
      · rename_i h2
        change χ_of_v_of_t = -1 at h2
        rw [h2] at h1
        unfold u_of_t u at h1
        have two_ne_zero := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
        have h3 : (2 : F) = 0 := by
          have h3' : 1 + t.val ≠ 0 := by
            intro h3''
            rw [← add_left_inj (-1)]  at h3''
            ring_nf at h3''
            have t_ne_neg_one := t.prop.right
            contradiction
          rw [← mul_left_inj' h3'] at h1
          have h3'' : (1 - t.val) / (1 + t.val) = (1 - t.val) * (1 + t.val)⁻¹ := by ring_nf
          rw [h3''] at h1
          rw [← mul_assoc, mul_assoc (-1 * (1 - t.val)), inv_mul_cancel₀ h3', mul_add] at h1
          rw [mul_one, mul_one, one_mul, mul_sub] at h1
          simp at h1
          grind
        contradiction
      · rename_i h2
        change χ_of_v_of_t = 1 at h2
        rw [h2, one_mul] at h1
        symm
        trivial

-- Used in the main case of Theorem 3 Proof part B
lemma t_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  t.val = 0 := by
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    have h1 : u_of_t = 1 := by exact (u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)
    unfold u_of_t u at h1
    have h4_1 : 1 + t.val ≠ 0 := by exact FiniteFieldBasic.one_add_t_ne_zero t
    rw [← mul_right_inj' h4_1, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self h4_1] at h1
    rw [← add_left_inj (t.val - 1)] at h1
    ring_nf at h1
    symm at h1
    rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1
    ring_nf at h1
    rw [mul_assoc, inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one] at h1
    exact h1

-- Used in the main case of Theorem 3 Proof part B
lemma v_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  v_of_t = r_of_s^2 := by
    intro v_of_t r_of_s
    unfold v_of_t v
    rw [(u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
    ring_nf
    rfl

-- Used in the main case of Theorem 3 Proof part B
lemma Y_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let χ_of_c_of_s  := (LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3)
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  Y_of_t = r_of_s * χ_of_c_of_s := by
    intro Y_of_t c_of_s χ_of_c_of_s r_of_s
    let χ_of_one_add_one_div_c_of_s_pow_two := (LegendreSymbol.χ (1 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s := (LegendreSymbol.χ r_of_s q field_cardinality q_prime_power q_mod_4_congruent_3)
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v_of_t := (LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s_div_c_of_s := (LegendreSymbol.χ (r_of_s / c_of_s) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s_pow_two := (LegendreSymbol.χ (r_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_sum := LegendreSymbol.χ (u_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3
    have c_ne_zero := c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      Y_of_t = (r_of_s^2)^((q + 1) / 4) * χ_of_one_add_one_div_c_of_s_pow_two := by
        unfold Y_of_t Y
        rw [(v_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
        rw [(u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
        change (χ_of_r_of_s_pow_two  * r_of_s^2) ^ ((q + 1) / 4) * χ_of_r_of_s_pow_two * (LegendreSymbol.χ (1 ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3) = (r_of_s ^ 2) ^ ((q + 1) / 4) * χ_of_one_add_one_div_c_of_s_pow_two
        have h1 : r_of_s^2 ≠ 0 := by
          rw [pow_two]
          apply mul_ne_zero
          · exact r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
          · exact r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        have h2 : IsSquare (r_of_s^2) := by apply IsSquare.sq
        unfold χ_of_r_of_s_pow_two
        rw [LegendreSymbol.χ_a_eq_one (r_of_s^2) h1 h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        nth_rw 2 [pow_two]
        rw [mul_one, one_mul, mul_one]
      _ = χ_of_r_of_s * r_of_s * χ_of_r_of_s_div_c_of_s := by
        unfold χ_of_one_add_one_div_c_of_s_pow_two
        rw [FiniteFieldBasic.one_add_one_a_pow_two_eq_a_add_one_over_a_over_a c_of_s c_ne_zero]
        change (r_of_s ^ 2) ^ ((q + 1) / 4) * LegendreSymbol.χ (r_of_s / c_of_s) q field_cardinality q_prime_power q_mod_4_congruent_3 = χ_of_r_of_s * r_of_s * χ_of_r_of_s_div_c_of_s
        rw [LegendreSymbol.b_pow_q_add_one_over_four_eq_χ_of_a_mul_a r_of_s q field_cardinality q_prime_power q_mod_4_congruent_3]
      _ = r_of_s * χ_of_c_of_s := by
        have r_ne_zero := r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        let χ_of_one_over_c_of_s  := (LegendreSymbol.χ (1 / c_of_s) q field_cardinality q_prime_power q_mod_4_congruent_3)
        calc
          χ_of_r_of_s * r_of_s * χ_of_r_of_s_div_c_of_s = r_of_s * χ_of_r_of_s * χ_of_r_of_s *  χ_of_one_over_c_of_s := by
            have h : r_of_s / c_of_s = r_of_s * (1 / c_of_s) := by ring_nf
            unfold χ_of_r_of_s_div_c_of_s
            rw [h]
            rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b r_of_s (1 / c_of_s) q field_cardinality q_prime_power q_mod_4_congruent_3]
            change χ_of_r_of_s * r_of_s * (χ_of_r_of_s * χ_of_one_over_c_of_s) = r_of_s * χ_of_r_of_s * χ_of_r_of_s *  χ_of_one_over_c_of_s
            ring_nf
          _ = r_of_s * 1 * χ_of_one_over_c_of_s := by
            rw [mul_assoc r_of_s, ← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b r_of_s r_of_s q field_cardinality q_prime_power q_mod_4_congruent_3]
            rw [← pow_two]
            rw [LegendreSymbol.χ_of_a_pow_two_eq_one r_of_s r_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3]
          _ = r_of_s * χ_of_c_of_s := by
            unfold χ_of_one_over_c_of_s
            rw [LegendreSymbol.χ_of_one_over_a_eq_χ_a c_of_s c_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3]
            rw [mul_one]

-- Implicated by main case of Theorem 3 proof part B.
lemma y_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  y_of_t = (r_of_s - 4) / (r_of_s + 4) := by
    intro r_of_s y_of_t
    unfold y_of_t y
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change (r_of_s * X_of_t - (1 + X_of_t) ^ 2) / (r_of_s * X_of_t + (1 + X_of_t) ^ 2) = (r_of_s - 4) / (r_of_s + 4)
    unfold X_of_t
    rw [X_η_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1]
    ring_nf

lemma y_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact FiniteFieldBasic.zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let y_of_t := y ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  y_of_t = (r_of_s - 4) / (r_of_s + 4) := by
    intro h1 y_of_t r_of_s
    unfold y_of_t y
    rw [X_of_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (r_of_s * 1 - (1 + 1) ^ 2) / (r_of_s * 1 + (1 + 1) ^ 2) = (r_of_s - 4) / (r_of_s + 4)
    ring_nf

lemma ϕ_of_t_eq_zero_one
  (t : { n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t.val = (0, 1) := by
    intro ϕ_of_t
    unfold ϕ_of_t ϕ
    rcases t.prop with h | h
    · rw [h]
      simp
    · rw [h]
      simp

lemma y_add_one_eq_two
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let y_of_t := point.2
  y_of_t + 1 = 2 := by
    intro point y_of_t
    unfold y_of_t point
    rw [ϕ_of_t_eq_zero_one t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp
    norm_num

-- Properties do not have to assume that the given `point` is element of E(F)
-- since these are just returning a Prop which would be false in the other case.
--
-- Actual assumption of E(F) is done in theorems using the following `def`s.

/-- `ϕ_over_F_prop1` is the first property fulfilled by points in `E_over_F`.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
noncomputable def ϕ_over_F_prop1
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : Prop :=
  let y := point.snd
  y + 1 ≠ 0

/-- `ϕ_over_F_prop2` is the second property fulfilled by points in `E_over_F`.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
def ϕ_over_F_prop2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : Prop :=
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  IsSquare ((1 + η_of_point * r_of_s)^2 - 1)

/-- `ϕ_over_F_prop3` is the third property fulfilled by points in `E_over_F`.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
def ϕ_over_F_prop3
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : Prop :=
  let x := point.fst
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_c_of_s := LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  η_of_point * r_of_s = -2 → x = 2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s

/-- `ϕ_over_F_props` combines the previously defined properties which are fulfilled by points in `E_over_F`,
i.e. `ϕ_over_F_prop1`, `ϕ_over_F_prop2` and `ϕ_over_F_prop3`.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
def ϕ_over_F_props
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : Prop
  :=
    ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point

/-- `ϕ_over_F` is the set of points produced by `ϕ`.

Original: Chapter "3.2 The map": Definition 2
-/
noncomputable def ϕ_over_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Set (F × F) := {P | ∃ t : F, (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) = P}

lemma point_in_ϕ_over_F_with_prop1_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop1
    intro y
    have h1 : ¬ (t.val ≠ 1 ∧ t.val ≠ -1) := by
      rcases t.property with h1_1 | h1_1
      · rw [h1_1]
        simp
      · rw [h1_1]
        simp
    unfold y point ϕ
    simp
    rw [dif_neg h1]
    ring_nf
    exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma point_in_ϕ_over_F_with_prop1_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop1
    intro y
    unfold y point ϕ
    simp only []
    rw [dif_pos t.prop]
    exact y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

-- Original: Theorem 3.2 Proof B prop 1 argumentation
lemma point_in_ϕ_over_F_with_prop1
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop1
    intro y
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · exact point_in_ϕ_over_F_with_prop1_main_case ⟨t, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq] at h1
        rw [← not_or, not_not] at h1
        exact h1
      exact point_in_ϕ_over_F_with_prop1_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma point_in_ϕ_over_F_with_prop2_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop2
    intro r_of_s η_of_point
    have h1 : ¬ (t.val ≠ 1 ∧ t.val ≠ -1) := by
      rcases t.property with h1_1 | h1_1
      · rw [h1_1]
        simp
      · rw [h1_1]
        simp
    unfold η_of_point η point ϕ
    simp
    rw [dif_neg h1]
    ring_nf
    rw [isSquare_iff_exists_sq 0]
    use 0
    simp

lemma point_in_ϕ_over_F_with_prop2_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop2
    intro r_of_s η_of_point
    let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1 : X_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X_of_t + 1 = 0 := by
      exact (y_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
    have h2 : NeZero (2 : F) := by
      rw [neZero_iff]
      apply (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)
    rw [pow_two] at h1
    nth_rw 1 [← one_mul X_of_t, mul_assoc] at h1
    apply (@quadratic_eq_zero_iff_discrim_eq_sq F _ 1 (2 * (1 + η_of_point * r_of_s)) 1 h2 _ (FiniteFieldBasic.one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3) X_of_t).mp at h1
    unfold discrim at h1
    rw [mul_pow 2 _ 2] at h1
    have h3 : 2^2 = (4 : F) := by norm_num
    rw [mul_one, h3, ← mul_sub, mul_comm] at h1
    rw [← div_left_inj' (FiniteFieldBasic.four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1
    rw [mul_div_assoc, div_self (FiniteFieldBasic.four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1
    rw [mul_one, ← h3, ← div_pow _ _ 2] at h1
    rw [h1]
    apply IsSquare.sq

-- Original: Theorem 3.2 Proof B prop 2 argumentation
lemma point_in_ϕ_over_F_with_prop2
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop2
    intro y
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · exact point_in_ϕ_over_F_with_prop2_main_case ⟨t, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq] at h1
        rw [← not_or, not_not] at h1
        exact h1
      exact point_in_ϕ_over_F_with_prop2_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma point_in_ϕ_over_F_with_prop3_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop3
    intro x c_of_s χ_of_c_of_s r_of_s η_of_point h1
    have h2 : ¬ (t.val ≠ 1 ∧ t.val ≠ -1) := by
      rcases t.property with h2_1 | h2_1
      · rw [h2_1]
        simp
      · rw [h2_1]
        simp
    unfold η_of_point η point ϕ at h1
    simp at h1
    rw [dif_neg h2] at h1
    ring_nf at h1
    simp at h1
    have h3 : (2 : F) ≠ 0 := by apply FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    contradiction

lemma point_in_ϕ_over_F_with_prop3_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop3
    intro x_of_point c_of_s χ_of_c_of_s r_of_s η_of_point h1
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_c_of_s := LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v_of_s := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold x_of_point point ϕ
    simp only []
    rw [dif_pos t.prop]
    unfold x
    simp
    change (c_of_s - 1) * s * X_of_t * (1 + X_of_t) / Y_of_t = 2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s
    unfold X_of_t Y_of_t
    rw [(X_η_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1)]
    rw [(Y_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1)]
    simp
    nth_rw 2 [mul_div_assoc]
    unfold χ_of_c_of_s
    nth_rw 2 [← LegendreSymbol.one_over_χ_of_a_eq_χ_a c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (c_of_s - 1) * s * (1 + 1) / (r_of_s * χ_of_c_of_s) = 2 * s * (c_of_s - 1) * (1 / χ_of_c_of_s / r_of_s)
    ring_nf

-- Original: Theorem 3.2 Proof B prop 3 argumentation
lemma point_in_ϕ_over_F_with_prop3
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop3
    intro y
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · exact point_in_ϕ_over_F_with_prop3_main_case ⟨t, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq] at h1
        rw [← not_or, not_not] at h1
        exact h1
      exact point_in_ϕ_over_F_with_prop3_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Original: Theorem 3.2 Proof B (3.2 forward statement)
theorem point_props_of_point_in_ϕ_over_F
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  point ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  → ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  := by
    intro point h1
    constructor
    · exact point_in_ϕ_over_F_with_prop1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · constructor
      · exact point_in_ϕ_over_F_with_prop2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact point_in_ϕ_over_F_with_prop3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma point_of_ϕ_in_ϕ_over_F
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  point.val ∈ ϕ_over_F := by
      unfold ϕ_over_F
      rw [Set.mem_setOf_eq]
      use t.val

lemma point_of_ϕ_fulfills_ϕ_over_F_props
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val := by
      intro point
      let h1 := point_of_ϕ_in_ϕ_over_F t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      apply point_props_of_point_in_ϕ_over_F t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1
