/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Elligator.FiniteFieldBasic
public import Elligator.LegendreSymbol
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
public import Elligator.Elligator1.MapProperties
public import Elligator.Elligator1.etaProperties

@[expose] public section

/-!
# X2 Variable Properties

In this file we introduce some generally helpful lemmas for `X2` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/


namespace Elligator.Elligator1

section X2Properties

variable {F : Type*} [Field F] [Fintype F]

lemma X2_eq_neg_one
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X2_of_point = -1 := by
    intro point X2_of_point
    unfold X2_of_point X2
    let r_of_s := r s
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    change -(1 + η_of_point * r_of_s) + ((1 + η_of_point * r_of_s) ^ 2 - 1) ^ ((q + 1) / 4) = -1
    unfold η_of_point
    rw [η_eq_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    ring_nf
    rw [zero_pow, add_zero]
    exact FiniteFieldBasic.q_add_one_over_four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3

lemma X2_h1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  (1 + η_of_point * r_of_s + X2_of_t)^2 = (1 + η_of_point * r_of_s)^2 - 1 := by
    intro η_of_point r_of_s X2_of_t
    unfold X2_of_t X2
    let a := ((1 + η_of_point * r_of_s)^2 - 1)^((q + 1) / 4)
    let a_sqr := (1 + η_of_point * r_of_s)^2 - 1
    change (1 + η_of_point * r_of_s + (-(1 + η_of_point * r_of_s) + a))^2 = a_sqr
    ring_nf
    unfold a a_sqr
    rw [← field_cardinality]
    nth_rw 2 [add_comm]
    rw [← pow_mul, FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two q field_cardinality q_mod_4_congruent_3]
    unfold η_of_point
    nth_rw 2 [add_comm]
    rw [field_cardinality, LegendreSymbol.a_pow_q_add_one_over_two_eq_a point.prop.2.1 q field_cardinality q_prime_power q_mod_4_congruent_3]

lemma X2_h2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X2_of_t^2 + 2 * (1 + η_of_point *r_of_s) * X2_of_t + 1 = 0 := by
    intro η_of_point r_of_s X2_of_t
    have h : (1 + η_of_point * r_of_s + X2_of_t)^2 = (1 + η_of_point * r_of_s)^2 - 1 := by exact X2_h1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    grind

lemma X2_h3
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
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X'_of_t := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = 0 := by
    intro t1 t2 h2_2 point X_of_t X'_of_t X2_of_t
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let r_of_s := r s
    let point_of_ϕ_fulfills_ϕ_over_F_props := point_of_ϕ_fulfills_ϕ_over_F_props t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = X2_of_t^2 - (X_of_t + X'_of_t) * X2_of_t + X_of_t * X'_of_t := by grind
      _ = X2_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1 := by
        rw [X_comparison_implication t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        change X2_of_t ^ 2 - -2 * (1 + η_of_point * r_of_s) * X2_of_t + X_of_t * X'_of_t = X2_of_t ^ 2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1
        rw [mul_add, mul_comm X_of_t _, X_comparison_implication2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        grind
      _ = 0 := by exact X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_of_ϕ_fulfills_ϕ_over_F_props⟩

lemma X2_h4
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
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X'_of_t := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X2_of_t = X_of_t ∨ X2_of_t = X'_of_t := by
    intro t1 t2 h2_2 point X_of_t X'_of_t X2_of_t
    have h1 : (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = 0 := by exact X2_h3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [mul_eq_zero] at h1
    nth_rw 1 [← add_left_inj (-X_of_t)]
    nth_rw 2 [← add_left_inj (-X'_of_t)]
    ring_nf
    exact h1

lemma X2_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X2_of_point ≠ 0 := by
    intro X2_of_point
    let X2_equation := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    let r_of_s := r s
    let point_prop := point.prop
    simp at X2_equation
    change X2_of_point^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_point + 1 = 0 at X2_equation
    intro h
    rw [h] at X2_equation
    simp at X2_equation

lemma y_divisor_ne_zero_with_X2_for_X
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let r_of_s := r s
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  r_of_s * X2_of_point + (1 + X2_of_point)^2 ≠ 0 := by
    intro r_of_s X2_of_point h1
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    let X2_equation := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let point_prop := point.prop
    simp at X2_equation
    change X2_of_point^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_point + 1 = 0 at X2_equation
    let y := point.val.2
    have h2 : (1 - 2 * η_of_point ) * r_of_s * X2_of_point = 0 := by
      rw [← h1]
      grind
    have h3 : 2 * η_of_point = 1 := by
      have h3_1 : r_of_s * X2_of_point ≠ 0 := by
        apply mul_ne_zero
        · exact (r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
        · exact (X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
      rw [← div_left_inj' h3_1]
      grind
    have h4 : y - 1 = y + 1 := by
      unfold η_of_point η at h3
      grind
    have h5 : y - 1 ≠ y + 1 := by grind
    contradiction

lemma X2_ne_neg_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X2_of_point ≠ -1 := by
    intro X2_of_point h1
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    let X2_equation := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let r_of_s := r s
    let point_prop := point.prop
    let y := point.val.2
    simp at X2_equation
    change X2_of_point^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_point + 1 = 0 at X2_equation
    rw [h1] at X2_equation
    simp at X2_equation
    have h2 : η_of_point = 0 := by
      ring_nf at X2_equation
      let r_ne_zero := r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at X2_equation
      rw [← div_left_inj' r_ne_zero] at X2_equation
      ring_nf at X2_equation
      change -(η_of_point * r_of_s * 2⁻¹ * r_of_s⁻¹ * 2) = 0 at X2_equation
      have h2_1 : -(η_of_point * r_of_s * 2⁻¹ * r_of_s⁻¹ * 2) = -(η_of_point * (r_of_s * r_of_s⁻¹) * (2 * 2⁻¹)) := by grind
      rw [h2_1] at X2_equation
      rw [mul_inv_cancel₀ r_ne_zero, mul_inv_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at X2_equation
      grind
    have h3 : η_of_point ≠ 0 := by
      unfold η_of_point η
      have h3_1 : y - 1 ≠ 0 := by
        intro h3_1_1
        grind
      have h3_2 : 2 * (y + 1) ≠ 0 := by
        intro h3_2_1
        let y_add_one_ne_zero := point_prop.1
        unfold ϕ_over_F_prop1 at y_add_one_ne_zero
        rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3_2_1
        ring_nf at h3_2_1
        rw [inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3_2_1
        grind
      apply div_ne_zero h3_1 h3_2
    contradiction

lemma X2_add_one_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X2_of_point + 1 ≠ 0 := by
    intro X2_of_point h1
    let h1 := X2_ne_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_ne_one
    grind

lemma y_with_X2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s
  let y := point.val.2
  y = (r_of_s * X2_of_point - (1 + X2_of_point)^2) / (r_of_s * X2_of_point + (1 + X2_of_point)^2) := by
    intro X2_of_point r_of_s y
    let X2_equation := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let point_prop := point.prop
    let y_add_one_ne_zero := point_prop.1
    let X2_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let two_ne_zero := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_ne_zero := r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    simp at X2_equation
    change X2_of_point^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_point + 1 = 0 at X2_equation
    have h1 : y = (1 + 2 * η_of_point) / (1 - 2 * η_of_point) := by
      have h1_1 : η_of_point = (y - 1) / (2 * (y + 1)) := by
        unfold η_of_point η y
        simp
      have h1_2 : (2 * (y + 1)) ≠ 0 := by
        apply mul_ne_zero
        · exact two_ne_zero
        · exact y_add_one_ne_zero
      grind
    have h2 : 2 * η_of_point = - ((1 + X2_of_point)^2) / (r_of_s * X2_of_point) := by
      have h2_1 : 1 + η_of_point * r_of_s = - (X2_of_point^2 + 1) / (2 * X2_of_point) := by
        have h2_1_1 : 2 * X2_of_point ≠ 0 := by
          apply mul_ne_zero
          · exact two_ne_zero
          · exact X2_ne_zero
        rw [← add_left_inj (-X2_of_point^2), ← add_left_inj (-1)] at X2_equation
        rw [← div_left_inj' h2_1_1] at X2_equation
        ring_nf at X2_equation
        grind
      have h2_2 : 2 * η_of_point = -((1 + X2_of_point)^2) / (r_of_s * X2_of_point) := by
        have h2_2_1 : η_of_point = (-(X2_of_point^2 + 1) / (2 * X2_of_point) -1) / r_of_s := by grind
        have h2_2_2 : η_of_point = -(X2_of_point + 1)^2 / (2 * r_of_s * X2_of_point) := by
          have h2_2_2_1 : (2 * X2_of_point) / (2 * X2_of_point) = 1 := by grind
          rw [← h2_2_2_1] at h2_2_1
          grind
        rw [← mul_left_inj' two_ne_zero] at h2_2_2
        simp_all
        ring_nf
        grind
      grind
    have h3 : (1 + 2 * η_of_point) / (1 - 2 * η_of_point) = ((r_of_s * X2_of_point - (1 + X2_of_point)^2)) / ((r_of_s * X2_of_point + (1 + X2_of_point)^2)) := by
      have h3_1 : 1 = (r_of_s * X2_of_point) / (r_of_s * X2_of_point) := by grind
      rw [h2]
      nth_rw 1 [h3_1]
      nth_rw 2 [h3_1]
      rw [← add_div, ← sub_div, div_div]
      grind
    rw [← h3]
    exact h1

lemma y_with_X2_of_X2_eq_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s
  let y := point.val.2
  X2_of_point = 1 → y = (r_of_s - 4) / (r_of_s + 4) := by
    intro X2_of_point r_of_s y X2_h
    let y_with_X2 := y_with_X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_eq_one
    grind

lemma η_mul_r_eq_neg_two_of_X2_eq_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s
  X2_of_point = 1 → η_of_point * r_of_s = -2 := by
    intro η_of_point  X2_of_point r_of_s X2_h
    let h1 := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let two_ne_zero := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    change X2_of_point^2 + 2 * (1 + η_of_point *r_of_s) * X2_of_point + 1 = 0 at h1
    rw [X2_h] at h1
    rw [← add_left_inj (-4)] at h1
    rw [← div_left_inj' two_ne_zero] at h1
    ring_nf at h1
    simp_all
    grind

lemma X2_observation1_of_X2_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let y := point.val.2
  let r_of_s := r s
  X2_of_point ≠ 1 → (r_of_s * X2_of_point + (1 + X2_of_point)^2)^2 * (1 - y^2) = 4 * r_of_s * X2_of_point * (1 + X2_of_point)^2 := by
    intro X2_of_point y r_of_s X2_h
    let y_with_X2 := y_with_X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_eq_one
    let r_ne_zero := r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let y_divisor_ne_zero_with_X2_for_X := y_divisor_ne_zero_with_X2_for_X s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change y = (r_of_s * X2_of_point - (1 + X2_of_point)^2) / (r_of_s * X2_of_point + (1 + X2_of_point)^2) at y_with_X2
    have h1 : (r_of_s * X2_of_point + (1 + X2_of_point)^2)^2 * (1 - y^2) = (r_of_s * X2_of_point + (1 + X2_of_point)^2)^2 - (r_of_s * X2_of_point - (1 + X2_of_point)^2)^2 := by
      rw [y_with_X2, div_pow, mul_sub]
      rw [← mul_div_assoc]
      nth_rw 3 [mul_comm]
      rw [mul_div_assoc, div_self]
      ring_nf
      simp_all
      grind
    grind

lemma X2_observation2_of_X2_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let y := point.val.2
  let r_of_s := r s
  let d_of_s := d s;
  X2_of_point ≠ 1 → (r_of_s * X2_of_point + (1 + X2_of_point)^2)^2 * (1 - d_of_s * y^2) = ((2 * r_of_s) / (r_of_s - 2)) * (X2_of_point^4 + (r_of_s^2 - 2) * X2_of_point^2 + 1) := by
    intro X2_of_point y r_of_s d_of_s X2_h
    let neg_d_eq_r_add_two_over_r_sub_two := neg_d_eq_r_add_two_over_r_sub_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change -d_of_s = (r_of_s + 2) / (r_of_s - 2) at neg_d_eq_r_add_two_over_r_sub_two
    let y_divisor_ne_zero_with_X2_for_X := y_divisor_ne_zero_with_X2_for_X s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y_with_X2 := y_with_X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_eq_one
    let r_ne_zero := r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    change y = (r_of_s * X2_of_point - (1 + X2_of_point)^2) / (r_of_s * X2_of_point + (1 + X2_of_point)^2) at y_with_X2
    have h1 : (r_of_s * X2_of_point + (1 + X2_of_point)^2)^2 * (1 - d_of_s * y^2) = (r_of_s * X2_of_point + (1 + X2_of_point)^2)^2 + (r_of_s + 2) / (r_of_s - 2) * ((r_of_s * X2_of_point - (1 + X2_of_point)^2)^2) := by
      rw [sub_eq_add_neg, neg_eq_neg_one_mul]
      rw [← mul_assoc, ← neg_eq_neg_one_mul]
      rw [neg_d_eq_r_add_two_over_r_sub_two, y_with_X2]
      rw [div_pow, mul_add]
      nth_rw 3 [mul_comm]
      rw [← mul_div_assoc, div_mul, mul_div_assoc]
      rw [div_self]
      ring_nf
      simp_all
      grind
    have h2 : (1 + X2_of_point)^2 = X2_of_point^2 + 2 * X2_of_point + 1 := by grind
    rw [h1, h2]
    let A := r_of_s * X2_of_point + (X2_of_point^2 + 2 * X2_of_point + 1)
    let B := r_of_s * X2_of_point - (X2_of_point^2 + 2 * X2_of_point + 1)
    change A^2 + (r_of_s + 2) / (r_of_s - 2) * B^2 = 2 * r_of_s / (r_of_s - 2) * (X2_of_point ^ 4 + (r_of_s ^ 2 - 2) * X2_of_point ^ 2 + 1)
    have h3 : A^2 = X2_of_point^ 4 + 2 * (r_of_s + 2) * X2_of_point^3 + ((r_of_s + 2)^2 + 2) * X2_of_point^2 + 2 * (r_of_s + 2) * X2_of_point + 1 := by grind
    have h4 : B^2 = X2_of_point^ 4 - 2 * (r_of_s - 2) * X2_of_point^3 + ((r_of_s - 2)^2 + 2) * X2_of_point^2 - 2 * (r_of_s - 2) * X2_of_point + 1 := by grind
    rw [h3, h4]
    let r_sub_two_ne_zero := r_sub_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have X_pow_four_term : X2_of_point^4 + (r_of_s + 2) / (r_of_s - 2) * X2_of_point^4 = X2_of_point^4 * (2 * r_of_s) / (r_of_s - 2) := by grind
    have X_pow_three_term : X2_of_point^3 * 2 * (r_of_s + 2) + (r_of_s + 2) / (r_of_s - 2) * (-2 * (r_of_s - 2) * X2_of_point^3) = 0 := by grind
    have X_pow_two_term : X2_of_point^2 * (r_of_s^2+ 4 * r_of_s + 6) + (r_of_s + 2) / (r_of_s - 2) * (r_of_s^2 - 4 * r_of_s + 6) * X2_of_point^2 = X2_of_point^2 * (2 * r_of_s * (r_of_s^2 - 2) / (r_of_s - 2)) := by
      nth_rw 3 [mul_comm]
      rw [← mul_add (X2_of_point^2)]
      have h5 : (r_of_s ^ 2 + 4 * r_of_s + 6 + (r_of_s + 2) / (r_of_s - 2) * (r_of_s ^ 2 - 4 * r_of_s + 6)) = ((r_of_s ^ 2 + 4 * r_of_s + 6) * (r_of_s - 2) + (r_of_s + 2) * (r_of_s ^ 2 - 4 * r_of_s + 6)) / (r_of_s - 2) := by grind
      rw [h5]
      have h6 : (r_of_s ^ 2 + 4 * r_of_s + 6) * (r_of_s - 2) = r_of_s^3 + 2 * r_of_s^2 - 2 * r_of_s - 12 := by grind
      have h7 : (r_of_s + 2) * (r_of_s ^ 2 - 4 * r_of_s + 6) = r_of_s^3 - 2 * r_of_s^2 - 2 * r_of_s + 12 := by grind
      rw [h6, h7]
      have h8 : r_of_s ^ 3 + 2 * r_of_s ^ 2 - 2 * r_of_s - 12 + (r_of_s ^ 3 - 2 * r_of_s ^ 2 - 2 * r_of_s + 12) = 2 * r_of_s^3 - 4 * r_of_s := by grind
      grind
    have X_pow_one_term : 2 * (r_of_s + 2) * X2_of_point - 2 * (r_of_s + 2) * X2_of_point = 0 := by grind
    have const_term : 1 + (r_of_s + 2) / (r_of_s - 2) = (2 * r_of_s) / (r_of_s - 2) := by grind
    grind

lemma one_sub_d_mul_y_pow_two_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let y := point.val.2
  let d_of_s := d s;
  1 - d_of_s * y^2 ≠ 0 := by
    intro y d_of_s h1
    let d_nonsquare := d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let d_ne_zero := d_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [← add_left_inj (d_of_s * y^2)] at h1
    ring_nf at h1
    rw [mul_comm, ← div_left_inj' d_ne_zero, mul_div_assoc, div_self d_ne_zero, mul_one] at h1
    change 1 / d_of_s = y^2 at h1
    have h2 : IsSquare (1 / d_of_s) := by
      unfold IsSquare
      use y
      grind
    let h3 := one_over_d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change ¬IsSquare (1 / d_of_s) at h3
    contradiction

lemma x_pow_two_of_X2_ne_one_eq1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  :
  let x := point.val.1
  let y := point.val.2
  let d := d s;
  x^2 = (1 - y^2) / (1 - d*y^2) := by
    intro x y d
    have curve_equation := point.prop;
    unfold E_over_F edwards_curve_equation at curve_equation
    let one_sub_d_mul_y_pow_two_ne_zero := one_sub_d_mul_y_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩;
    change 1 - d * y^2 ≠ 0 at one_sub_d_mul_y_pow_two_ne_zero
    rw [Set.mem_setOf_eq] at curve_equation
    change x^2 + y^2 = 1 + d * x^2 * y^2  at curve_equation
    rw [← add_left_inj (-d * x^2 * y^2 - y^2)] at curve_equation
    ring_nf at curve_equation
    nth_rw 1 [← mul_one (x^2)] at curve_equation
    rw [mul_assoc, ← mul_sub (x^2)] at curve_equation
    nth_rw 2 [mul_comm] at curve_equation
    rw [← div_left_inj' one_sub_d_mul_y_pow_two_ne_zero] at curve_equation
    grind

lemma x_pow_two_of_X2_ne_one_eq2_of_X2_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (y_eq_one : point.val.2 ≠ 1)
  :
  let x := point.val.1
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r := r s
  X ≠ 1 → x^2 = (2 * (r -2) * X^2 * (1 + X)^2) / (X^5 + (r^2 - 2) * X^3 + X) := by
    intro x X r Xh
    let y := point.val.2
    let d := d s;
    let x_pow_two_of_X2_ne_one_eq1 := x_pow_two_of_X2_ne_one_eq1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    change x^2 = (1 - y^2) / (1 - d*y^2) at x_pow_two_of_X2_ne_one_eq1
    let y_with_X2 := y_with_X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_eq_one
    change y = (r * X - (1 + X)^2) / (r * X + (1 + X)^2) at y_with_X2
    let y_divisor_ne_zero_with_X2_for_X := y_divisor_ne_zero_with_X2_for_X s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩
    change r * X + (1 + X)^2 ≠ 0 at y_divisor_ne_zero_with_X2_for_X
    have h1 : (r * X + (1 + X)^2)^2 ≠ 0 := by grind
    have h2 : 1 = ((r * X + (1 + X)^2)^2) / ((r * X + (1 + X)^2)^2) := by grind
    let X2_observation1_of_X2_ne_one := X2_observation1_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_eq_one
    change X ≠ 1 → (r * X + (1 + X)^2)^2 * (1 - y^2) = 4 * r * X * (1 + X)^2 at X2_observation1_of_X2_ne_one
    have h3 : (r * X + (1 + X)^2)^2 * (1 - y^2) = 4 * r * X * (1 + X)^2 := by grind
    let X2_observation2_of_X2_ne_one := X2_observation2_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_eq_one
    change X ≠ 1 → (r * X + (1 + X)^2)^2 * (1 - d * y^2) = ((2 * r) / (r - 2)) * (X^4 + (r^2 - 2) * X^2 + 1) at X2_observation2_of_X2_ne_one
    have h4 : (r * X + (1 + X)^2)^2 * (1 - d * y^2) = ((2 * r) / (r - 2)) * (X^4 + (r^2 - 2) * X^2 + 1) := by grind
    let X_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩
    change X ≠ 0 at X_ne_zero
    calc
      x^2 = (1 - y^2) / (1 - d*y^2) := by grind
      _ = (4 * r * X * (1 + X)^2) / ((2 * r) / (r - 2) * (X^4 + (r^2 - 2) * X^2 + 1)) := by
        rw [← one_mul (1 - y ^ 2), ← one_mul (1 - d * y ^ 2)]
        nth_rw 1 [h2]
        rw [mul_div_assoc, div_mul_div_comm]
        grind
      _ = (2 * (r - 2) * X * (1 + X)^2) / (X^4 + (r^2 - 2) * X^2 + 1) := by
        -- TODO cleanup proof
        let r_sub_two_ne_zero := r_sub_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        change r - 2 ≠ 0 at r_sub_two_ne_zero
        have rh : 1 = (r - 2) / (r - 2) := by grind
        rw [← one_mul ((4 * r * X * (1 + X)^2) / ((2 * r) / (r - 2) * (X^4 + (r^2 - 2) * X^2 + 1)))]
        nth_rw 1 [rh]
        rw [div_mul_div_comm]
        nth_rw 2 [← mul_assoc]
        nth_rw 1 [← mul_div_assoc]
        rw [mul_comm (r - 2) (2 * r), mul_div_assoc]
        nth_rw 2 [mul_div_assoc]
        rw [div_self r_sub_two_ne_zero, ← mul_div_assoc]
        have helper : (r - 2) * (4 * r * X * (1 + X) ^ 2) / (2 * r * 1 * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)) = (r - 2) * (2 * X * (1 + X) ^ 2) / ((X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)) := by
          have h_1 : (4 * r) / (2 * r) = 2 := by
            let two_ne_zero := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
            let r_ne_zero := (r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
            rw [← mul_left_inj' two_ne_zero]
            ring_nf
            rw [mul_inv_cancel₀ r_ne_zero]
            grind
          have h_2 : (r - 2) * (4 * r * X * (1 + X) ^ 2) / (2 * r * 1 * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)) = ((r - 2) * (X * (1 + X) ^ 2)) * (4 * r) / ((2 * r) * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)) := by grind
          rw [h_2, div_mul_eq_div_div, mul_div_assoc, h_1]
          grind
        rw [helper]
        grind
      _ = (2 * (r -2) * X^2 * (1 + X)^2) / (X^5 + (r^2 - 2) * X^3 + X) := by
        have h5 : 1 = X / X := by grind
        nth_rw 1 [← one_mul ((2 * (r - 2) * X * (1 + X)^2) / (X^4 + (r^2 - 2) * X^2 + 1)), h5]
        rw [div_mul_div_comm]
        ring_nf

/-- `Y'` is the `Y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def Y'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  : F :=
  let x := point.val.1
  let c := c s
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  -- This is just `def x` with the denominator `Y` replaced by `x` of point
  (c - 1) * s * X * (1 + X) / x

lemma Y'_pow_two_eq_of_X2_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r := r s
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  -- This is just `def x` with the denominator `Y` replaced by `x` of point
  X ≠ 1 → Y^2 = X^5 + (r^2 - 2) * X^3 + X := by
    intro X r Y Xh
    let c := c s
    let x := point.val.1
    let h1 := x_pow_two_of_X2_ne_one_eq2_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props y_eq_one
    let two_ne_zero := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2 : x^2 = (2 * (r -2) * X^2 * (1 + X)^2) / (X^5 + (r^2 - 2) * X^3 + X) := by exact h1 Xh
    calc
     Y^2 = (c - 1)^2 * s^2 * X^2 * (1 + X)^2 / (x^2) := by
      unfold Y Y'
      change ((c - 1) * s * X * (1 + X) / x)^2 = (c - 1)^2 * s^2 * X^2 * (1 + X)^2 / (x^2)
      rw [div_pow]
      repeat rw [← mul_pow]
    _ = 2 * (r - 2) * X^2 * (1 + X)^2 / (x^2) := by
      have h : (c - 1)^2 * s^2 = 2 * (r - 2) := by
        unfold r Elligator1.r c Elligator1.c
        grind
      grind
    _ = X^5 + (r^2 - 2) * X^3 + X := by
      have h : (2 * (r - 2) * X^2 * (1 + X)^2) ≠ 0 := by
        let X2_add_one_ne_zero := X2_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_eq_one
        let r_sub_two_ne_zero := r_sub_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        let X2_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩
        rw [add_comm]
        apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · exact two_ne_zero
            · exact r_sub_two_ne_zero
          · exact FiniteFieldBasic.pow_two_ne_zero X2_ne_zero
        · apply FiniteFieldBasic.pow_two_ne_zero X2_add_one_ne_zero
      rw [h2]
      nth_rw 1 [← div_one (2 * (r - 2) * X ^ 2 * (1 + X) ^ 2)]
      rw [div_div_div_comm, div_self h]
      grind

lemma X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X2_of_point ≠ 1 → X2_of_point ≠ 1 ∧ X2_of_point ≠ -1 := by
    intro X2_of_point h1
    let h1 := X2_ne_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_ne_one
    grind
