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

@[expose] public section

/-!
# d Variable Properties

In this file we introduce some generally helpful lemmas for `d` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section dProperties

variable {F : Type*} [Field F] [Fintype F]

lemma d_nonsquare
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  ¬IsSquare d_of_s := by
    intro d_of_s
    rw [isSquare_iff_exists_mul_self d_of_s]
    change ¬∃ r, (-((2 / s^2) + 1)^2 / ((2 / s^2) - 1)^2) = r * r
    rintro ⟨w, Pw⟩
    have h00 : (2 / s^2 - 1)^2 ≠ 0 := by
      rw [pow_two]
      apply mul_ne_zero
      · apply sub_ne_zero.2
        exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      · apply sub_ne_zero.2
        exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h01 : (2 / s^2 + 1)^2 ≠ 0 := by
      rw [pow_two]
      apply mul_ne_zero
      change c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 + 1 ≠ 0
      · intro h
        have h' : (c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) = -1 := by
          rw [← add_right_inj (-1)] at h
          rw [add_zero] at h
          rw [add_comm] at h
          have h8 : (1 : F) + (-1 : F) = 0 := by ring
          rw [add_assoc] at h
          rw [h8] at h
          rw [add_zero] at h
          exact h
        apply c_ne_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 at h'
        exact h'
      · intro h
        have h' : (c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) = -1 := by
          rw [← add_right_inj (-1)] at h
          rw [add_zero] at h
          rw [add_comm] at h
          have h8 : (1 : F) + (-1 : F) = 0 := by ring
          rw [add_assoc] at h
          rw [h8] at h
          rw [add_zero] at h
          exact h
        apply c_ne_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 at h'
        exact h'
    have h1 : w^2 * ((2 / s^2) - 1)^2 / ((2 / s^2) + 1)^2 = -1 := by
      rw [pow_two, ← Pw]
      rw [div_eq_mul_inv]
      rw [div_eq_mul_inv]
      rw [← neg_one_mul]
      rw [mul_assoc (-1 * (2 / s ^ 2 + 1) ^ 2) (((2 / s ^ 2 - 1) ^ 2)⁻¹) ((2 / s ^ 2 - 1) ^ 2)]
      rw [inv_mul_cancel₀ h00]
      rw [mul_one]
      rw [mul_assoc]
      rw [mul_inv_cancel₀ h01]
      rw [mul_one]
    have h2 : IsSquare (-1 : F) := by
      rw [← h1]
      have h3 : IsSquare (w^2) := by
        rw [pow_two]
        apply IsSquare.mul_self w
      have h4 : IsSquare (((2 / s^2) - 1)^2 / ((2 / s^2) + 1)^2) := by
        apply IsSquare.div
        · rw [pow_two]
          apply IsSquare.mul_self (2 / s^2 - 1)
        · rw [pow_two]
          apply IsSquare.mul_self (2 / s^2 + 1)
      rw [mul_div_assoc]
      apply IsSquare.mul h3 h4
    have h5 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h2
      rw [field_cardinality] at h2
      exact h2
    contradiction

lemma d_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  d_of_s ≠ 0 := by
    intro d_of_s
    let d_nonsquare := d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    intro h
    have h1 : IsSquare d_of_s := by
      unfold IsSquare
      use 0
      grind
    contradiction

lemma one_over_d_nonsquare
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  ¬IsSquare (1 / d_of_s) := by
      intro d_of_s h3_1
      unfold IsSquare at h3_1
      let d_nonsquare := d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      let d_ne_zero := d_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      rcases h3_1 with ⟨a, ah⟩
      rw [← pow_two, ← mul_left_inj' d_ne_zero] at ah
      ring_nf at ah
      rw [inv_mul_cancel₀ d_ne_zero] at ah
      change 1 = d_of_s * a^2 at ah
      by_cases h3_2 : a = 0
      · rw [h3_2] at ah
        ring_nf at ah
        let one_ne_zero := FiniteFieldBasic.one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
        contradiction
      · have h3_3 : a^2 ≠ 0 := by grind
        rw [← div_left_inj' h3_3, mul_div_assoc, div_self h3_3, mul_one] at ah
        rw [← one_pow 2, ← div_pow] at ah
        have d_square : IsSquare d_of_s := by
          use 1 / a
          grind
        contradiction

lemma d_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  d_of_s ≠ 1 := by
    intro d_of_s
    let d_nonsquare := d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    intro h
    have h1 : IsSquare d_of_s := by
      unfold IsSquare
      use 0
      grind
    contradiction

lemma d_ne_zero_and_d_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  d_of_s ≠ 0 ∧ d_of_s ≠ 1 := by
    intro d_of_s
    split_ands
    · exact d_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · exact d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma neg_d_eq_r_add_two_over_r_sub_two
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  -d_of_s = (r_of_s + 2) / (r_of_s - 2) := by
    intro r_of_s d_of_s
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      -d_of_s = (c_of_s + 2 + 1 / c_of_s) / (c_of_s - 2 + 1 / c_of_s) := by
        change -(-(c_of_s + 1)^2 / (c_of_s - 1)^2) = (c_of_s + 2 + 1 / c_of_s) / (c_of_s - 2 + 1 / c_of_s)
        rw [← neg_one_mul]
        nth_rw 2 [← neg_one_mul]
        rw [mul_div_assoc, ← mul_assoc]
        rw [add_pow_two, sub_pow_two]
        have h3_1 : 1 / c_of_s ≠ 0 := by
          rw [← inv_eq_one_div]
          apply inv_ne_zero
          apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        have h3_2 : (1 / c_of_s) / (1 / c_of_s) = 1 := by
          rw [div_self h3_1]
        have h3_3 : (-1 : F) * (-1) = 1 := by ring
        rw [h3_3]
        nth_rw 1 [← h3_2]
        rw [← mul_div_mul_comm]
        rw [mul_add, mul_add, mul_add, mul_sub, pow_two, ← mul_assoc]
        rw [← inv_eq_one_div, inv_mul_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), one_mul]
        rw [mul_one, ← mul_assoc, mul_comm, ← mul_assoc]
        rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), one_mul]
        ring_nf
      _ = (r_of_s + 2) / (r_of_s - 2) := by
        rw [add_assoc, add_comm 2 (1 / c_of_s), ← add_assoc]
        nth_rw 3 [add_comm]
        rw [← add_sub_assoc]
        nth_rw 3 [add_comm]
        change (r_of_s + 2) / (r_of_s - 2) = (r_of_s + 2) / (r_of_s - 2)
        rfl
