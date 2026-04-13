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
public import Elligator.Elligator1.rProperties
public import Elligator.Elligator1.uProperties

@[expose] public section

/-!
# v Variable Properties

In this file we introduce some generally helpful lemmas for `v` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section vProperties

variable {F : Type*} [Field F] [Fintype F]

lemma v_h1_third_factor_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let u_of_t := u t
  let c_of_s := c s
  u_of_t^2 + 1 / c_of_s^2 ≠ 0 := by
    intro u_of_t c_of_s h1
    have h1_1 : -1 = (u_of_t * c_of_s)^2 := by
      ring
      have h1_1_1 : c_of_s^2 = c_of_s^2 := by rfl
      rw [← div_left_inj' (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
      rw [mul_div_assoc]
      rw [← div_eq_one_iff_eq (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1_1_1
      rw [h1_1_1, mul_one]
      rw [← add_left_inj (1 / c_of_s^2)]
      have h1_1_3 : 1 / c_of_s^2 = 1 / c_of_s^2 := by rfl
      rw [← neg_one_mul, mul_div_assoc, neg_one_mul]
      rw [neg_add_eq_zero.2 h1_1_3]
      symm
      exact h1
    have h1_2 : IsSquare (-1 : F) := by
      rw [h1_1]
      rw [pow_two]
      apply IsSquare.mul_self (u_of_t * c_of_s)
    have h1_3 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h1_2
      rw [field_cardinality] at h1_2
      exact h1_2
    contradiction

lemma v_h1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let v_of_t := v t s
  let c_of_s := c s
  let u_of_t := u t
  v_of_t = u_of_t * (u_of_t^2 + c_of_s^2) * (u_of_t^2 + 1 / c_of_s^2) := by
    intro v_of_t c_of_s u_of_t
    unfold v_of_t v
    let r_of_s := r s
    change u_of_t ^ 5 + (r_of_s ^ 2 - 2) * u_of_t ^ 3 + u_of_t = u_of_t * (u_of_t ^ 2 + c_of_s ^ 2) * (u_of_t ^ 2 + 1 / c_of_s ^ 2)
    rw [r_h1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [mul_add, mul_add, add_mul, add_mul]
    ring_nf
    change u_of_t + u_of_t ^ 3 * c_of_s ^ 2 + u_of_t ^ 3 * c_of_s⁻¹ ^ 2 + u_of_t ^ 5 = u_of_t * c_of_s ^ 2 * c_of_s⁻¹ ^ 2 + u_of_t ^ 3 * c_of_s ^ 2 + u_of_t ^ 3 * c_of_s⁻¹ ^ 2 + u_of_t ^ 5
    simp
    have h1 : c_of_s^2 ≠ 0 := by
      rw [pow_two]
      apply mul_ne_zero
      · exact (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
      · exact (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
    rw [mul_assoc, mul_inv_cancel₀ h1]
    ring_nf

lemma v_h1_second_factor_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let c_of_s := c s
  let u_of_t := u t
  (u_of_t^2 + c_of_s^2) ≠ 0 := by
    intro c_of_s u_of_t h3_1
    have h3_1_1 : -1 = (u_of_t / c_of_s)^2 := by
      rw [← add_left_inj (-c_of_s^2)] at h3_1
      rw [zero_add] at h3_1
      rw [add_assoc] at h3_1
      have h3_1_1_1 : c_of_s^2 = c_of_s^2 := by rfl
      rw [add_neg_eq_zero.2 h3_1_1_1] at h3_1
      rw [add_zero] at h3_1
      rw [← neg_one_mul] at h3_1
      rw [div_pow u_of_t c_of_s 2]
      rw [← div_left_inj' (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3_1
      rw [mul_div_assoc] at h3_1
      rw [← div_eq_one_iff_eq (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3_1_1_1
      rw [h3_1_1_1] at h3_1
      rw [mul_one] at h3_1
      symm at h3_1
      exact h3_1
    have h3_1_2 : IsSquare (-1 : F) := by
      rw [h3_1_1]
      rw [pow_two]
      apply IsSquare.mul_self (u_of_t / c_of_s)
    have h3_1_3 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h3_1_2
      rw [field_cardinality] at h3_1_2
      exact h3_1_2
    contradiction

lemma v_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let v_of_t := v t s
  v_of_t ≠ (0 : F) := by
    rw [v_h1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t
      · exact (v_h1_second_factor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)
    · exact (v_h1_third_factor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)

lemma χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let v_of_t := v t s
  let χ_of_v := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
  (χ_of_v * v_of_t)^((q + 1) / 4) ≠ 0 := by
    intro v_of_t χ_of_v
    rw [mul_pow χ_of_v v_of_t ((q + 1) / 4)]
    apply mul_ne_zero
    · apply pow_ne_zero ((q + 1) / 4) (LegendreSymbol.χ_a_ne_zero v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t) q field_cardinality q_prime_power q_mod_4_congruent_3)
    · apply pow_ne_zero ((q + 1) / 4) (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)

lemma v_comparison
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
  let u1 := u t
  let v2 := v ⟨t2, h2_2⟩ s
  let r_of_s := r s
  v2 = 1 / u1^5 + (r_of_s^2 - 2) * 1 / u1^3 + 1 / u1 := by
    intro t1 t2 h2_2 u1 v2 r_of_s
    let u2 := u ⟨t2, h2_2⟩
    calc
      v2 = u2^5 + (r_of_s^2 - 2) * u2^3 + u2 := by
        unfold v2 v u2
        rfl
      _ = 1 / u1^5 + (r_of_s^2 - 2) * 1/ u1^3 + 1 / u1 := by
        unfold u2 u1 t2 t1
        rw [u_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        ring_nf

lemma v_comparison_implication1
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
  let u1 := u t
  let v1 := v t s
  let v2 := v ⟨t2, h2_2⟩ s
  v2 * u1^6 = v1 := by
    intro t1 t2 h2_2 u1 v1 v2
    let u2 := u ⟨t2, h2_2⟩
    let r_of_s := r s
    calc
      v2 * u1^6 = u1 + (r_of_s^2 - 2) * u1^3 + u1^5 := by
        unfold v2
        rw [v_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        rw [add_mul _ _ (u1^6)]
        rw [add_mul _ _ (u1^6)]
        have u1_ne_zero : u1 ≠ 0 := by
          unfold u1
          exact u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t
        have h2_5_1 : 1 / u1 ^ 5 * u1 ^ 6 = u1 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          have h2_5_1_1 : 5 ≤ 6 := by norm_num
          rw [div_eq_mul_inv, ← pow_sub₀ u1 u1_ne_zero h2_5_1_1]
          simp
        have h2_5_2 : 1 / u1 ^ 3 * u1 ^ 6 = u1^3 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          have h2_5_2_1 : 3 ≤ 6 := by norm_num
          rw [div_eq_mul_inv, ← pow_sub₀ u1 u1_ne_zero h2_5_2_1]
        have h2_5_3 : 1 / u1 * u1 ^ 6 = u1^5 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          have h2_5_3_1 : 1 ≤ 6 := by norm_num
          nth_rw 2 [← pow_one u1]
          rw [div_eq_mul_inv, ← pow_sub₀ u1 u1_ne_zero h2_5_3_1]
        rw [h2_5_1, mul_div_assoc, mul_assoc, h2_5_2, h2_5_3]
      _ = v1 := by
        unfold v1 v u1
        rw [add_assoc]
        nth_rw 2 [add_comm]
        rw [add_comm]

lemma v_comparison_implication2
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
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
  let u1 := u t
  let v1 := v t s
  let v2 := v ⟨t2, h2_2⟩ s
  v2 = v1 / u1^6 := by
    intro t1 t2 h2_2 u1 v1 v2
    let u2 := u ⟨t2, h2_2⟩
    let r_of_s := r s
    have h2_6_1 : u1^6 ≠ 0 := by apply pow_ne_zero 6 (u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t)
    rw [← mul_right_inj' h2_6_1]
    unfold v1
    rw [← v_comparison_implication1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change u1 ^ 6 * v2 = u1 ^ 6 * (v2 * u1 ^ 6 / u1 ^ 6)
    ring_nf
    have h2_6_2 : 6 ≤ 12 := by norm_num
    have u1_ne_zero : u1 ≠ 0 := by
      unfold u1
      exact u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t
    rw [mul_comm (u1^12) v2, inv_pow, mul_assoc, ← pow_sub₀ u1 u1_ne_zero h2_6_2]
    simp
    rw [mul_comm]

lemma v_comparison_implication3
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let u1 := u t
  let χ_of_u1_pow_6 := LegendreSymbol.χ (u1^6) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_u1_pow_6 = 1 := by
    intro u1 χ_of_u1_pow_6
    have h2_7_1 : u1^6 = u1^2 * u1^2 * u1^2 := by ring_nf
    unfold χ_of_u1_pow_6
    rw [h2_7_1]
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (u1^2 * u1^2) (u1^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (u1^2) (u1^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
    have h2_7_2 : u1 ≠ 0 := by exact u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t
    rw [LegendreSymbol.χ_of_a_pow_two_eq_one u1 (u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t) q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma v_comparison_implication4
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
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
  let u1 := u t
  let v1 := v t s
  let v2 := v ⟨t2, h2_2⟩ s
  let χ_of_v1 := LegendreSymbol.χ v1 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v2 := LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_v2 = χ_of_v1 := by
    intro t1 t2 h2_2 u1 v1 v2 χ_of_v1 χ_of_v2
    unfold χ_of_v2 χ_of_v1 v1
    rw [← v_comparison_implication1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (v2 * u1^6) q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v2 (u1^6) q field_cardinality q_prime_power q_mod_4_congruent_3]
    let χ_of_u1_pow_6 := LegendreSymbol.χ (u1^6) q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [v_comparison_implication3 t q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma v_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact FiniteFieldBasic.zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let v_of_t := v ⟨(0 : F), h1⟩ s
  let r_of_s := r s
  v_of_t = r_of_s^2 := by
    intro h1 v_of_t r_of_s
    unfold v_of_t v
    rw [u_of_zero q field_cardinality q_prime_power q_mod_4_congruent_3]
    unfold r_of_s
    ring_nf
