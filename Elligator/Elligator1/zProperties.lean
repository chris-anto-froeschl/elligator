/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.etaProperties
public import Elligator.Elligator1.X2Properties

/-!
# z Properties

In this file we introduce some generally helpful lemmas for `z` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma z_eq_zero
  (t : { t : F // t = 1 ∨ t = -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).val
  let z := z s P q
  z = 0 := by
    intro P z
    unfold z Elligator1.z
    let c := c s
    repeat rw [X2_eq_neg_one t s_h1 s_h2 q_h1 q_h2 q_h3]
    simp_all

/-- `z'` is the `z` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def z'
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  : F :=
  let Y := Y' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  let c := c s
  χ (Y * (X^2 + 1 / c^2))

lemma Y'_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  :
  let Y := Y' s_h2 q_h1 q_h3 P
  Y ≠ 0 := by
    intro Y
    let X2_add_one_ne_zero := X2_add_one_ne_zero s_h1 q_h1 q_h3 ⟨P.val, P_props⟩ y_ne_one
    let X2_ne_zero := X2_ne_zero q_h1 q_h3 ⟨P.val, P_props⟩
    let c_sub_one_ne_zero := c_sub_one_ne_zero s_h2
    unfold Y Y'
    grind

lemma X_pow_two_add_1_over_c_pow_two_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  :
  let X := X2 s P q
  let c := c s
  X^2 + 1 / c^2 ≠ 0 := by
    intro X c h
    rw [← mul_left_inj' (c_ne_zero s_h1 q_h1 q_h3)] at h
    rw [← mul_left_inj' (c_ne_zero s_h1 q_h1 q_h3)] at h
    ring_nf at h
    change X^2 * c^2 + c⁻¹^2 * c^2 = 0 at h
    rw [inv_pow c 2, inv_mul_cancel₀ (pow_two_ne_zero (c_ne_zero s_h1 q_h1 q_h3))] at h
    rw [← add_left_inj (-1 : F), ← mul_pow] at h
    simp only [add_neg_cancel_right, zero_add] at h
    let h' := neg_one_non_square q_h1 q_h3
    have h'' : IsSquare (-1 : F) := by
      rw [← h, pow_two]
      apply IsSquare.mul_self
    contradiction

lemma z'_argument_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  :
  let Y := Y' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  let c := c s
  Y * (X^2 + 1 / c^2) ≠ 0 := by grind [Y'_ne_zero, X_pow_two_add_1_over_c_pow_two_ne_zero]

lemma z'_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  :
  let z := z' s_h2 q_h1 q_h3 P
  z ≠ 0 := by
    intro z
    let Y := Y' s_h2 q_h1 q_h3 P
    let X := X2 s P q
    let c := c s
    let z'_argument_ne_zero := z'_argument_ne_zero s_h1 s_h2 q_h1 q_h3 P P_props x_ne_zero y_ne_one
    let a := (Y * (X^2 + 1 / c^2))
    exact χ_a_ne_zero z'_argument_ne_zero q_h1

lemma z'_eq_one_or_z'_eq_neg_one
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  :
  let z := z' s_h2 q_h1 q_h3 P
  z = 1 ∨ z = -1 := by
    intro z
    let Y := Y' s_h2 q_h1 q_h3 P
    let X := X2 s P q
    let c := c s
    let a := (Y * (X^2 + 1 / c^2))
    let χ_of_a := χ a
    have h1 := @χ_values _ _ _ q a q_h1 q_h2 q_h3
    change χ_of_a = 0 ∨ χ_of_a = -1 ∨ χ_of_a = 1 at h1
    have h2 := z'_ne_zero s_h1 s_h2 q_h1 q_h3 P P_props x_ne_zero y_ne_one
    change χ_of_a ≠ 0 at h2
    change χ_of_a = 1 ∨ χ_of_a = -1
    simp_all
    grind

end Elligator.Elligator1
