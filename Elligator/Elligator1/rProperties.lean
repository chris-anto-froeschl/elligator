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
# r Variable Properties

In this file we introduce some generally helpful lemmas for `r` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section rProperties

variable {F : Type*} [Field F] [Fintype F]

lemma r_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s
  r_of_s ≠ 0 := by
    change (2 / s^2) + 1 / (2 / s^2) ≠ 0
    intro h
    let c_of_s := c s
    have h1 : c_of_s  = (-1 : F) / c_of_s := by
      change c_of_s + 1 / c_of_s = 0 at h
      rw [← add_right_inj (-1 / c_of_s)] at h
      rw [add_comm] at h
      rw [add_zero] at h
      have h3 : 1 / c_of_s + -1 / c_of_s = 0 := by
        ring_nf
      nth_rw 1 [← add_zero c_of_s]
      rw [← h3]
      rw [← add_assoc]
      exact h
    have h2 : c_of_s^2 = -1 := by
      calc
        c_of_s^2 = -1 / c_of_s * c_of_s := by
          rw [pow_two]
          nth_rw 1 [h1]
        _ = -1 := by
          nth_rw 1 [← neg_one_mul 1]
          ring
          rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
    have h3 : IsSquare (-1 : F) := by
      rw [← h2]
      rw [pow_two]
      apply IsSquare.mul_self c_of_s
    have h4 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h3
      rw [field_cardinality] at h3
      exact h3
    contradiction

lemma aux_neg_one_sq_of_sum_eq_zero (s : F) (hs : s ≠ 0)
    (h2 : (2 : F) ≠ 0) (h : (2 / s ^ 2) ^ 2 + 4 * (2 / s ^ 2) + 1 = 0) :
    IsSquare (-1 : F) := by
      -- Let $a = s^2 + 4$. Then $a^2 = 12$.
      set a : F := s ^ 2 + 4
      have ha : a ^ 2 = 12 := by
        grind;
      -- Let $u = a / 2$. Then $u^2 = 3$.
      set u : F := a / 2
      have hu : u ^ 2 = 3 := by
        grind;
      -- Then $-s^2 = (u - 1)^2$, so $-1 = ((u - 1) / s)^2$.
      have h_neg_one : -1 = ((u - 1) / s) ^ 2 := by
        grind +ring;
      exact ⟨ _, h_neg_one.trans ( sq _ ) ⟩

lemma four_add_r_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s
  4 + r_of_s ≠ 0 := by
    let c_of_s := c s
    change 4 + (c_of_s + 1 / c_of_s) ≠ 0
    intro h
    have hc : c_of_s ≠ 0 := c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2 : (2 : F) ≠ 0 := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    have h_quad : c_of_s ^ 2 + 4 * c_of_s + 1 = 0 := by linear_combination' h * c_of_s - inv_mul_cancel₀ hc
    have h_neg_sq : IsSquare (-1 : F) := by
      set a : F := s ^ 2 + 4
      have ha : a ^ 2 = 12 := by
        unfold c_of_s c at h_quad
        grind
      set u : F := a / 2
      have hu : u ^ 2 = 3 := by
        grind;
      have h_neg_one : -1 = ((u - 1) / s) ^ 2 := by
        grind +ring;
      exact ⟨ _, h_neg_one.trans ( sq _ ) ⟩
    have h_not_sq : ¬ IsSquare (-1 : F) := by
      rw [FiniteField.isSquare_neg_one_iff]
      rw [field_cardinality]
      omega
    exact h_not_sq h_neg_sq

lemma r_h1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s
  let c_of_s := c s
  (r_of_s^2 - 2) = c_of_s^2 + 1 / c_of_s^2 := by
    intro r_of_s c_of_s
    calc
      r_of_s^2 - 2 = (c_of_s + 1 / c_of_s)^2 - 2 := by
        change (c_of_s + 1 / c_of_s)^2 - 2 = (c_of_s + 1 / c_of_s)^2 - 2
        rfl
      _ = c_of_s^2 + 2 * (c_of_s * (1 / c_of_s)) + (1 / c_of_s)^2 - 2 := by
        rw [add_pow_two]
        rw [mul_assoc 2 c_of_s (1 / c_of_s)]
      _ = c_of_s^2 + 2 + 1 / c_of_s^2 - 2 := by
        ring
        rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
        ring
      _ = c_of_s^2 + 1 / c_of_s^2 := by
        ring_nf

lemma r_sub_two_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s
  r_of_s - 2 ≠ 0 := by
    intro r_of_s
    let c_of_s := c s
    let c_ne_zero := c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let c_ne_one := c_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold r_of_s r
    change (c_of_s + 1 / c_of_s) - 2 ≠ 0
    have h1 : (c_of_s + 1 / c_of_s) - 2 = (c_of_s - 1)^2 / c_of_s := by grind
    rw [h1]
    apply div_ne_zero
    · grind
    · exact c_ne_zero
