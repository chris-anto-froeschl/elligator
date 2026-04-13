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

@[expose] public section

/-!
# X Variable Properties

In this file we introduce some generally helpful lemmas for `X` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section XProperties

variable {F : Type*} [Field F] [Fintype F]

lemma X_pow_two_add_one_over_c_pow_two_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let c_of_s := c s
  X_of_t^2 + 1 / c_of_s^2 ≠ 0 := by
    intro X_of_t c_of_s h
    rw [← mul_left_inj' (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h
    rw [← mul_left_inj' (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h
    ring_nf at h
    change X_of_t^2 * c_of_s^2 + c_of_s⁻¹^2 * c_of_s^2 = 0 at h
    rw [inv_pow c_of_s 2, inv_mul_cancel₀ (FiniteFieldBasic.pow_two_ne_zero (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)), ← add_left_inj (-1 : F), ← mul_pow] at h
    simp at h

    have h' : ¬IsSquare (-1 : F) := by exact FiniteFieldBasic.neg_one_non_square q field_cardinality q_prime_power q_mod_4_congruent_3
    have h' : IsSquare (-1 : F) := by
      rw [← h, pow_two]
      apply IsSquare.mul_self
    contradiction

lemma X_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X_of_t ≠ 0 := by
    let u_of_t := u t
    let v_of_t := v t s
    apply mul_ne_zero
    · apply LegendreSymbol.χ_a_ne_zero v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t) q field_cardinality q_prime_power q_mod_4_congruent_3
    · apply u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t

lemma X_comparison
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
  let X1 := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X2 = 1 / X1 := by
    intro t1 t2 h2_2 X1 X2
    let u1 := u t
    let u2 := u ⟨t2, h2_2⟩
    let v1 := v t s
    let v2 := v ⟨t2, h2_2⟩ s
    let χ_of_v1 := LegendreSymbol.χ v1 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v2 := LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      X2 = χ_of_v2 * u2 := by
        change χ_of_v2 * u2 = χ_of_v2 * u2
        rfl
      _ = χ_of_v1 / u1 := by
        unfold χ_of_v2 v2 t2
        rw [v_comparison_implication4 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        unfold u2
        rw [u_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        change χ_of_v1 * (1 / u1) = χ_of_v1 / u1
        ring_nf
      _ = 1 / (χ_of_v1 * u1) := by
        unfold χ_of_v1
        nth_rw 1 [← LegendreSymbol.one_over_χ_of_a_eq_χ_a v1 q field_cardinality q_prime_power q_mod_4_congruent_3]
        ring_nf
      _ = 1 / X1 := by
        change 1 / X1 = 1 / X1
        rfl

lemma X_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact FiniteFieldBasic.zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let X_of_t := X ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  X_of_t = 1 := by
    intro h1 X_of_t
    unfold X_of_t X
    let v_of_t := v ⟨(0 : F), h1⟩ s
    let r_of_s := r s
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [u_of_zero q field_cardinality q_prime_power q_mod_4_congruent_3]
    change χ_of_v_of_t * 1 = 1
    unfold χ_of_v_of_t v_of_t
    rw [v_of_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (LegendreSymbol.χ (r_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) * 1 = 1
    rw [LegendreSymbol.χ_of_a_pow_two_eq_one r_of_s (r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp
