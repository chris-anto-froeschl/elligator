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

@[expose] public section

namespace Elligator.Elligator1

section cProperties

variable {F : Type*} [Field F] [Fintype F]

lemma c_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s
  c_of_s ≠ 0 := by
  change 2 / s^2 ≠ 0
  apply div_ne_zero
  · apply FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
  · rw [pow_two]
    apply mul_ne_zero s_h1 s_h1

lemma c_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s
  c_of_s ≠ 1 := by
  change 2 / s^2 ≠ 1
  apply div_ne_one_of_ne
  apply Ne.symm
  apply s_pow_two_ne_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma c_ne_neg_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s
  c_of_s ≠ -1 := by
  change 2 / s^2 ≠ -1
  intro h
  have h1 : s^2 = -2 := by
    calc
      s^2 = 2 / (-1 : F) := by
        rw [← h]
        ring_nf
        rw [inv_inv]
        rw [mul_assoc]
        rw [mul_comm (2⁻¹) 2]
        rw [mul_inv_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
        rw [mul_one]
      _ = -2 := by norm_num
  apply s_pow_two_ne_neg_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 at h1
  exact h1

lemma c_add_one_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s
  c_of_s + 1 ≠ 0 := by
    intro c_of_s
    intro h
    change 2 / s^2 + 1 = 0 at h
    have h1 : (-1 : F) + 1 = 0 := by norm_num
    rw [← h1] at h
    apply add_right_cancel_iff.1 at h
    have h2 : s^2 = -2 := by
      calc
        s^2 = 2 / (-1 : F) := by
          rw [← h]
          ring_nf
          rw [inv_inv]
          rw [mul_assoc]
          rw [mul_comm (2⁻¹) 2]
          rw [mul_inv_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
          rw [mul_one]
        _ = -2 := by norm_num
    apply s_pow_two_ne_neg_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 at h2
    exact h2

lemma c_sub_one_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s
  c_of_s - 1 ≠ 0 := by
    apply sub_ne_zero.2
    exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma c_h
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s
  c_of_s * (c_of_s - 1) * (c_of_s + 1) ≠ 0 := by
    change (2 / s^2) * ((2 / s^2) - 1) * ((2 / s^2) + 1) ≠ 0
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact c_sub_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · exact c_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma c_pow_two_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s
  c_of_s^2 ≠ (0 : F) := by
    intro c_of_s
    rw [pow_two]
    apply mul_ne_zero
    · exact (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
    · exact (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
