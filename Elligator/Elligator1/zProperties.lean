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
public import Elligator.Elligator1.etaProperties
public import Elligator.Elligator1.X2Properties

@[expose] public section

/-!
# z Properties

In this file we introduce some generally helpful lemmas for `z` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section zProperties

variable {F : Type*} [Field F] [Fintype F]

lemma z_eq_zero
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
  let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  z_of_point = 0 := by
    intro point z_of_point
    unfold z_of_point z
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    repeat rw [X2_eq_neg_one t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change LegendreSymbol.χ ((c_of_s - 1) * s * (-1) * (1 + (-1)) * point.1 * ((-1) ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = 0
    simp
    exact LegendreSymbol.χ_a_zero_eq_zero (0 : F) (rfl) q field_cardinality q_prime_power q_mod_4_congruent_3

/-- `z'` is the `z` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def z'
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
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  LegendreSymbol.χ (Y * (X^2 + 1 / c^2)) q field_cardinality q_prime_power q_mod_4_congruent_3

lemma Y'_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  Y ≠ 0 := by
    intro Y
    let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let x := point.val.1
    let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_add_one_ne_zero := X2_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_ne_one
    let X2_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩
    let c_sub_one_ne_zero := c_sub_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold Y Y'
    change (c - 1) * s * X * (1 + X) / x ≠ 0
    rw [add_comm]
    grind

lemma X_pow_two_add_1_over_c_pow_two_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X^2 + 1 / c^2 ≠ 0 := by
    intro X c h
    rw [← mul_left_inj' (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h
    rw [← mul_left_inj' (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h
    ring_nf at h
    change X^2 * c^2 + c⁻¹^2 * c^2 = 0 at h
    rw [inv_pow c 2, inv_mul_cancel₀ (FiniteFieldBasic.pow_two_ne_zero (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)), ← add_left_inj (-1 : F), ← mul_pow] at h
    simp at h
    have h' : ¬IsSquare (-1 : F) := by exact FiniteFieldBasic.neg_one_non_square q field_cardinality q_prime_power q_mod_4_congruent_3
    have h' : IsSquare (-1 : F) := by
      rw [← h, pow_two]
      apply IsSquare.mul_self
    contradiction

lemma z'_argument_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  Y * (X^2 + 1 / c^2) ≠ 0 := by
    intro Y X c
    let h1 := Y'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let h2 := X_pow_two_add_1_over_c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    grind

lemma z'_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  z ≠ 0 := by
    intro z
    let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let z'_argument_ne_zero := z'_argument_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let a := (Y * (X^2 + 1 / c^2))
    exact LegendreSymbol.χ_a_ne_zero a z'_argument_ne_zero  q field_cardinality q_prime_power q_mod_4_congruent_3

lemma z'_eq_one_or_z'_eq_neg_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  z = 1 ∨ z = -1 := by
    intro z
    let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let a := (Y * (X^2 + 1 / c^2))
    let χ_of_a := LegendreSymbol.χ a q field_cardinality q_prime_power q_mod_4_congruent_3
    have h1 := LegendreSymbol.χ_values a q field_cardinality q_prime_power q_mod_4_congruent_3
    change χ_of_a = 0 ∨ χ_of_a = -1 ∨ χ_of_a = 1 at h1
    have h2 := z'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    change χ_of_a ≠ 0 at h2
    change χ_of_a = 1 ∨ χ_of_a = -1
    simp_all
    grind
