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
public import Elligator.Elligator1.uProperties
public import Elligator.Elligator1.vProperties
public import Elligator.Elligator1.XProperties

@[expose] public section

/-!
# Y Variable Properties

In this file we introduce some generally helpful lemmas for `Y` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section YProperties

variable {F : Type*} [Field F] [Fintype F]
variable {s : F} (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

lemma Y_ne_zero
  (s_h1 : s ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let Y_of_t := Y t s q
  Y_of_t ≠ 0 := by
    let u_of_t := u t
    let v_of_t := v t s
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t
    let c_of_s := c s
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t
    let χ_of_sum := LegendreSymbol.χ (u_of_t^2 + 1 / c_of_s^2)
    intro Y_of_t
    change (χ_of_v_of_t * v_of_t)^((q + 1) / 4) * χ_of_v_of_t * χ_of_sum ≠ 0
    let v_ne_zero := v_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3 t
    apply mul_ne_zero
    · apply mul_ne_zero
      · rw [mul_pow (χ_of_v_of_t) (v_of_t) ((q + 1) / 4)]
        apply mul_ne_zero
        · apply pow_ne_zero (((q + 1) / 4) : ℕ)
          apply LegendreSymbol.χ_a_ne_zero v_ne_zero field_cardinality
        · apply pow_ne_zero (((q + 1) / 4) : ℕ)
          apply v_ne_zero
      · apply LegendreSymbol.χ_a_ne_zero v_ne_zero field_cardinality
    · apply LegendreSymbol.χ_a_ne_zero (v_h1_third_factor_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3 t) field_cardinality

lemma X_mul_Y_ne_zero
  (s_h1 : s ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X_of_t := X t s
  let Y_of_t := Y t s q
  X_of_t * Y_of_t ≠ 0 := by
    apply mul_ne_zero
    · apply X_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3 t
    · apply Y_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3 t

lemma one_add_X_ne_zero
  (s_h1 : s ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X_of_t := X t s
  (1 + X_of_t) ≠ (0 : F) := by
    let u_of_t := u t
    let v_of_t := v t s
    let r_of_s := r s
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t
    let v_ne_zero := v_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3 t
    intro X
    change 1 + χ_of_v_of_t * u_of_t ≠ 0
    intro h
    have h1 : χ_of_v_of_t * u_of_t = -1 := by
      rw [← add_right_inj (-1)] at h
      rw [add_zero] at h
      have h1_1 : (-1 : F) + (1 : F) = 0 := by ring
      rw [← add_assoc] at h
      rw [h1_1] at h
      rw [zero_add] at h
      exact h
    have h2 : u_of_t = -χ_of_v_of_t := by
      rw [← neg_one_mul (χ_of_v_of_t)]
      change u_of_t = -1 * LegendreSymbol.χ v_of_t
      rw [← LegendreSymbol.one_over_χ_of_a_eq_χ_a field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [← mul_left_inj' (LegendreSymbol.χ_a_ne_zero v_ne_zero field_cardinality)]
      ring_nf
      rw [mul_inv_cancel₀ (LegendreSymbol.χ_a_ne_zero v_ne_zero field_cardinality)]
      rw [mul_comm]
      change χ_of_v_of_t * u_of_t = -1
      exact h1
    have h3 : v_of_t = -χ_of_v_of_t * (1 + r_of_s^2 - 2 + 1) := by
      change u_of_t^5 + (r_of_s^2 - 2) * u_of_t^3 + u_of_t = -χ_of_v_of_t * (1 + r_of_s^2 - 2 + 1)
      repeat rw [h2]
      have h3_1: Odd 5 := by
        apply Nat.odd_iff.2
        norm_num
      rw [← neg_one_mul, mul_pow, mul_pow]
      rw [LegendreSymbol.χ_of_a_pow_n_eq_χ_a v_of_t ⟨5, h3_1⟩ field_cardinality q_prime_power q_mod_4_congruent_3]
      have h3_2: Odd 3 := by
        apply Nat.odd_iff.2
        norm_num
      rw [LegendreSymbol.χ_of_a_pow_n_eq_χ_a v_of_t ⟨3, h3_2⟩ field_cardinality q_prime_power q_mod_4_congruent_3]
      change (-1) ^ 5 * χ_of_v_of_t + (r_of_s ^ 2 - 2) * ((-1) ^ 3 * χ_of_v_of_t) + -1 * χ_of_v_of_t = -1 * χ_of_v_of_t * (1 + r_of_s ^ 2 - 2 + 1)
      ring
    have h4 : v_of_t = -χ_of_v_of_t * r_of_s^2 := by
      rw [add_comm] at h3
      rw [← add_sub_assoc] at h3
      rw [← add_assoc] at h3
      have h4_1 : (1 : F) + (1 : F) = 2 := by ring
      rw [h4_1] at h3
      rw [add_comm] at h3
      rw [add_sub_assoc] at h3
      have h4_2 : (2 : F) - (2 : F) = 0 := by ring
      rw [h4_2, add_zero] at h3
      exact h3
    have h5 : χ_of_v_of_t = -χ_of_v_of_t := by
      rw [h2] at h1
      change LegendreSymbol.χ v_of_t * -χ_of_v_of_t = -1 at h1
      rw [h4] at h1
      rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b] at h1
      nth_rw 1 [← neg_one_mul] at h1
      rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b] at h1
      rw [LegendreSymbol.χ_of_neg_one_eq_neg_one field_cardinality q_prime_power q_mod_4_congruent_3] at h1
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a field_cardinality q_prime_power q_mod_4_congruent_3] at h1
      change -1 * χ_of_v_of_t * LegendreSymbol.χ (r_of_s ^ 2) * -χ_of_v_of_t = -1 at h1
      have h5_1 : r_of_s^2 ≠ 0 := by
        rw [pow_two]
        apply mul_ne_zero
        · apply r_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3
        · apply r_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3
      have h5_2 : IsSquare (r_of_s^2) := by
        rw [pow_two]
        apply IsSquare.mul_self r_of_s
      rw [LegendreSymbol.χ_a_eq_one h5_1 h5_2 field_cardinality q_mod_4_congruent_3] at h1
      rw [mul_one] at h1
      rw [neg_one_mul] at h1
      have h5_3 : χ_of_v_of_t ≠ 0 := LegendreSymbol.χ_a_ne_zero v_ne_zero field_cardinality
      rw [← mul_left_inj' h5_3] at h1
      change -χ_of_v_of_t * -χ_of_v_of_t * LegendreSymbol.χ v_of_t = -1 * χ_of_v_of_t at h1
      rw [← LegendreSymbol.one_over_χ_of_a_eq_χ_a field_cardinality q_prime_power q_mod_4_congruent_3] at h1
      change -χ_of_v_of_t * -χ_of_v_of_t * (1 / χ_of_v_of_t) = -1 * χ_of_v_of_t at h1
      rw [← inv_eq_one_div χ_of_v_of_t] at h1
      rw [← neg_one_mul] at h1
      ring_nf at h1
      rw [pow_two, mul_assoc] at h1
      rw [mul_inv_cancel₀ h5_3] at h1
      rw [mul_one] at h1
      exact h1
    have h6 : χ_of_v_of_t ≠ -χ_of_v_of_t := LegendreSymbol.neg_χ_a_ne_χ_a v_ne_zero field_cardinality q_prime_power q_mod_4_congruent_3
    contradiction

lemma Y_comparison
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t
  let X1 := X t s
  let Y1 := Y t s q
  let Y2 := Y ⟨t2, h2_2⟩ s q
  Y2 = Y1 / X1^3 := by
    intro t1 t2 h2_2 X1 Y1 Y2
    let c_of_s := c s
    let r_of_s := r s
    let u1 := u t
    let u2 := u ⟨t2, h2_2⟩
    let v1 := v t s
    let v2 := v ⟨t2, h2_2⟩ s
    let x1 := x t s q
    let x2 := x ⟨t2, h2_2⟩ s q
    let y1 := y t s
    let y2 := y ⟨t2, h2_2⟩ s
    let χ_of_u1 := LegendreSymbol.χ u1
    let χ_of_u2 := LegendreSymbol.χ u2
    let χ_of_v1 := LegendreSymbol.χ v1
    let χ_of_v2 := LegendreSymbol.χ v2
    let χ_of_u1_mul_v1  := LegendreSymbol.χ (u1 * v1)
    let u_ne_zero := @u_ne_zero F _ t
    have first_factor : (χ_of_v2 * v2)^((q + 1) / 4) = (χ_of_v1 * v1)^((q + 1) / 4) * χ_of_u1 / u1^3:= by
      have h1_1 : χ_of_v2 * v2 = χ_of_v1 * v1 / u1^6 := by
        unfold χ_of_v2
        rw [v_comparison_implication4 t field_cardinality q_mod_4_congruent_3]
        unfold v2
        rw [v_comparison_implication2 t]
        change χ_of_v1 * (v1 / u1^6) = χ_of_v1 * v1 / u1 ^ 6
        rw [← mul_div_assoc]
      have h1_2 : IsSquare (χ_of_u1 * u1^3) := by
        have h1_2_1 : χ_of_u1 * u1^3 ≠ 0 := by
          apply mul_ne_zero
          · apply LegendreSymbol.χ_a_ne_zero u_ne_zero field_cardinality
          · apply pow_ne_zero 3 u_ne_zero
        apply (LegendreSymbol.χ_a_eq_one_iff_a_square h1_2_1 field_cardinality q_mod_4_congruent_3).mp
        have h : (3 : ℕ) = 1 + 2 := by norm_num
        rw [h, pow_add u1 1 2, ← mul_assoc, pow_one]
        rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
        rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
        rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a field_cardinality q_prime_power q_mod_4_congruent_3]
        rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, ← pow_two]
        have h' : IsSquare (u1^2) := by
          rw [pow_two]
          apply IsSquare.mul_self u1
        have h'' : LegendreSymbol.χ (u1 ^ 2) = 1 := by
          apply (LegendreSymbol.χ_a_eq_one_iff_a_square (FiniteFieldBasic.pow_two_ne_zero u_ne_zero) field_cardinality q_mod_4_congruent_3).mpr
          exact h'
        rw [h'']
        simp
      have h1_3 : (u1^6)^((q + 1) / 4) = χ_of_u1 * u1^3  := by
        have h1_3_1 : 6 = 3 * 2 := by norm_num
        rw [h1_3_1, ← pow_mul, mul_assoc, mul_comm, pow_mul, mul_comm]
        rw [← field_cardinality, add_comm]
        rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two field_cardinality q_mod_4_congruent_3]
        rw [field_cardinality, add_comm, LegendreSymbol.a_pow_q_add_one_over_two_eq_χ_of_a_mul_a field_cardinality q_mod_4_congruent_3]
        change (χ_of_u1 * u1)^3 = χ_of_u1 * u1^3
        have h1_3_2 : Odd 3 := by trivial
        rw [mul_pow, LegendreSymbol.χ_of_a_pow_n_eq_χ_a u1 ⟨3, h1_3_2 ⟩ field_cardinality q_prime_power q_mod_4_congruent_3]
      calc
        (χ_of_v2 * v2)^((q + 1) / 4) = (χ_of_v1 * v1 / u1^6)^((q + 1) / 4) := by
          rw [h1_1]
        _ = (χ_of_v1 * v1)^((q + 1) / 4) * χ_of_u1 / u1^3:= by
          rw [div_pow]
          rw [h1_3]
          unfold χ_of_u1
          nth_rw 2 [← LegendreSymbol.one_over_χ_of_a_eq_χ_a field_cardinality q_prime_power q_mod_4_congruent_3]
          ring_nf
    have second_factor : χ_of_v2 = χ_of_v1 := by exact v_comparison_implication4 t field_cardinality q_mod_4_congruent_3
    have third_factor : LegendreSymbol.χ (u2^2 + 1 / c_of_s^2) = LegendreSymbol.χ (u1 * v1 * (u1^2 + 1 / c_of_s^2)) := by
      calc
        LegendreSymbol.χ (u2^2 + 1 / c_of_s^2) = LegendreSymbol.χ ((c_of_s^2 * u1^4 * (u2^2 + 1 / c_of_s^2)) * (u1^2 + 1 / c_of_s^2)^2) := by
          rw [LegendreSymbol.χ_of_a_eq_χ_a_mul_b_pow_two (c_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3) field_cardinality q_mod_4_congruent_3]
          rw [mul_comm]
          rw [LegendreSymbol.χ_of_a_eq_χ_a_mul_b_pow_two (u_pow_two_ne_zero t) field_cardinality q_mod_4_congruent_3]
          rw [mul_comm]
          rw [LegendreSymbol.χ_of_a_eq_χ_a_mul_b_pow_two (v_h1_third_factor_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3 t) field_cardinality q_mod_4_congruent_3]
          change LegendreSymbol.χ ((u1^2)^2 * (c_of_s^2 * (u2^2 + 1 / c_of_s^2)) * (u1^2 + 1 / c_of_s^2)^2) = LegendreSymbol.χ (c_of_s ^ 2 * u1 ^ 4 * (u2 ^ 2 + 1 / c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2) ^ 2)
          ring_nf
        _ = LegendreSymbol.χ ((u1^2 * (c_of_s^2 + u1^2)) * (u1^2 + 1 / c_of_s^2)^2) := by
          rw [pow_two u2]
          unfold u2
          rw [u_comparison t s]
          change LegendreSymbol.χ (c_of_s ^ 2 * u1 ^ 4 * (1 / u1 * (1 / u1) + 1 / c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2) ^ 2) = LegendreSymbol.χ (u1 ^ 2 * (c_of_s ^ 2 + u1 ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2) ^ 2)
          have h1 : c_of_s ^ 2 * u1 ^ 4 * (1 / u1 * (1 / u1) + 1 / c_of_s ^ 2) = u1^2 * (c_of_s^2 + u1^2) := by
            rw [mul_add]
            ring_nf
            simp
            nth_rw 4 [mul_comm]
            rw [mul_assoc (u1 ^ 4) (c_of_s ^ 2) ((c_of_s ^ 2)⁻¹)]
            rw [mul_inv_cancel₀ (c_pow_two_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3)]
            have h1_2 : 4 = 2 + 2 := by norm_num
            rw [h1_2, pow_add, ← mul_assoc _ (u1^2) (u1^2), mul_assoc (c_of_s^2 * u1^2) (u1^2) _]
            rw [mul_inv_cancel₀ (u_pow_two_ne_zero t)]
            ring_nf
          rw [h1]
        _ = LegendreSymbol.χ (u1 * v1 * (u1^2 + 1 / c_of_s^2)) := by
          nth_rw 1 [pow_two u1]
          rw [pow_two ((u1^2 + 1 / c_of_s^2))]
          repeat rw [← mul_assoc]
          rw [add_comm]
          unfold v1
          rw [v_h1 s_h1 field_cardinality q_prime_power q_mod_4_congruent_3]
          change LegendreSymbol.χ (u1 * u1 * (u1 ^ 2 + c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2)) = LegendreSymbol.χ (u1 * (u1 * (u1 ^ 2 + c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2)) * (u1 ^ 2 + 1 / c_of_s ^ 2))
          repeat rw [← mul_assoc]
    calc
      Y2 = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1^3 := by
        unfold Y2 Y
        change (χ_of_v2 * v2)^((q + 1) / 4) * χ_of_v2 * LegendreSymbol.χ (u2^2 + 1 / c_of_s^2) = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3
        rw [first_factor, second_factor, third_factor]
        rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
        change (χ_of_v1 * v1) ^ ((q + 1) / 4) * χ_of_u1 / u1 ^ 3 * χ_of_v1 * (χ_of_u1_mul_v1 * (LegendreSymbol.χ (u1 ^ 2 + 1 / c_of_s ^ 2) )) = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3
        have h1 : (χ_of_v1 * v1) ^ ((q + 1) / 4) * χ_of_u1 / u1 ^ 3 * χ_of_v1 * (χ_of_u1_mul_v1 * (LegendreSymbol.χ (u1 ^ 2 + 1 / c_of_s ^ 2))) = (χ_of_v1 * v1) ^ ((q + 1) / 4) * χ_of_v1 * (LegendreSymbol.χ (u1 ^ 2 + 1 / c_of_s ^ 2)) * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3 := by ring_nf
        rw [h1]
        change Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3 = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3
        rfl
      _ = Y1 / (χ_of_v1 * u1)^3 := by
        unfold χ_of_u1_mul_v1 χ_of_u1
        rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
        rw [← mul_assoc, mul_assoc Y1 (LegendreSymbol.χ u1) (LegendreSymbol.χ u1)]
        rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
        rw [← pow_two]
        rw [LegendreSymbol.χ_of_a_pow_two_eq_one u_ne_zero field_cardinality q_mod_4_congruent_3]
        rw [← LegendreSymbol.one_over_χ_of_a_eq_χ_a field_cardinality q_prime_power q_mod_4_congruent_3]
        have h2 : Odd 3 := by
          apply Nat.odd_iff.mpr
          norm_num
        let v_ne_zero := v_ne_zero s_h1 field_cardinality q_prime_power q_mod_4_congruent_3 t
        rw [← LegendreSymbol.χ_of_a_pow_n_eq_χ_a v1 ⟨3, h2⟩ field_cardinality q_prime_power q_mod_4_congruent_3]
        change Y1 * 1 * (1 / χ_of_v1^3) / u1 ^ 3 = Y1 / (χ_of_v1 * u1) ^ 3
        simp
        ring_nf
      _ = Y1 / X1^3 := by
        change Y1 / X1^3 = Y1 / X1^3
        rfl
