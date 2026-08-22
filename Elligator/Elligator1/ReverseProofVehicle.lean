/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.ImageCharacterization
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Reconstruction Coordinates

TODO

## Main Results

* TODO

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.ReverseProofVehicle

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates
open Elligator.Elligator1.ReconstructionCoordinates
open Elligator.Elligator1.ImageCharacterization

section Y'

/-- `Y'` is the `Y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def Y' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
    let x := P.val.1
    let c := c s
    let X := Xbar s P q
    -- This is just `def x` with the denominator `Y` replaced by `x` of P
    (c - 1) * s * X * (1 + X) / x

lemma Y'_pow_two_eq_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (y_eq_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let r := r s
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    -- This is just `def x` with the denominator `Y` replaced by `x` of P
    X ≠ 1 → Y ^ 2 = X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X := by
  intro X r Y Xh
  let c := c s
  let x := P.val.1
  let h := x_pow_two_of_Xbar_ne_one_eq2_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_eq_one
  let two_ne_zero := two_ne_zero hq_card hq_mod
  have h' : x ^ 2 = (2 * (r -2) * X ^ 2 * (1 + X) ^ 2) / (X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X) := h Xh
  calc
    Y ^ 2 = (c - 1) ^ 2 * s ^ 2 * X ^ 2 * (1 + X) ^ 2 / (x ^ 2) := by
      unfold Y Y'
      change ((c - 1) * s * X * (1 + X) / x) ^ 2
        = (c - 1) ^ 2 * s ^ 2 * X ^ 2 * (1 + X) ^ 2 / (x ^ 2)
      rw [div_pow]
      repeat rw [← mul_pow]
  _ = 2 * (r - 2) * X ^ 2 * (1 + X) ^ 2 / (x ^ 2) := by
    have h : (c - 1) ^ 2 * s ^ 2 = 2 * (r - 2) := by
      unfold r CurveParameters.r c CurveParameters.c
      field_simp [hs_ne_zero]
      ring
    rw [h]
  _ = X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X := by
    have h'' : (2 * (r - 2) * X ^ 2 * (1 + X) ^ 2) ≠ 0 := by
      let Xbar_add_one_ne_zero :=
        Xbar_add_one_ne_zero hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_eq_one
      let r_sub_two_ne_zero := r_sub_two_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let Xbar_ne_zero := Xbar_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
      rw [add_comm]
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero two_ne_zero r_sub_two_ne_zero
        · apply pow_ne_zero 2 Xbar_ne_zero
      · apply pow_ne_zero 2 Xbar_add_one_ne_zero
    rw [h']
    nth_rw 1 [← div_one (2 * (r - 2) * X ^ 2 * (1 + X) ^ 2)]
    rw [div_div_div_comm, div_self h'']
    simp_all

lemma Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_ne_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P q
    Xbar ≠ 1 → Xbar ≠ 1 ∧ Xbar ≠ -1 :=
  by grind [Xbar_ne_neg_one]

lemma Y'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    Y ≠ 0 := by
  intro Y
  have Xbar_add_one_ne_zero :=
    Xbar_add_one_ne_zero hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  have Xbar_ne_zero := Xbar_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
  have c_sub_one_ne_zero := c_sub_one_ne_zero sq_ne_pm_two
  unfold Y Y'
  grind

end Y'

section z'

/-- `z'` is the `z` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def z' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  let X := Xbar s P q
  let c := c s
  χ (Y * (X ^ 2 + 1 / c ^ 2))

lemma z'_argument_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    let c := c s
    Y * (X ^ 2 + 1 / c ^ 2) ≠ 0 := by
  grind [Y'_ne_zero, X_pow_two_add_1_div_c_pow_two_ne_zero]

lemma z'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let z := z' sq_ne_pm_two hq_card hq_mod P
    z ≠ 0 := by
  intro z
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  let X := Xbar s P q
  let c := c s
  let z'_argument_ne_zero :=
    z'_argument_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let a := (Y * (X ^ 2 + 1 / c ^ 2))
  exact χ_a_ne_zero z'_argument_ne_zero

lemma z'_eq_one_or_z'_eq_neg_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let z := z' sq_ne_pm_two hq_card hq_mod P
    z = 1 ∨ z = -1 := by
  intro z
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  let X := Xbar s P q
  let c := c s
  let a := (Y * (X ^ 2 + 1 / c ^ 2))
  open Classical in
  let χ_of_a := χ a
  have h1 := χ_values (a := a)
  change χ_of_a = 0 ∨ χ_of_a = -1 ∨ χ_of_a = 1 at h1
  have h2 := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  change χ_of_a ≠ 0 at h2
  change χ_of_a = 1 ∨ χ_of_a = -1
  simp_all
  grind

end z'

section u'

/-- `u'` is the `u` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def u' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let z := z' sq_ne_pm_two hq_card hq_mod P
  let X := Xbar s P q
  z * X

lemma u'_pow_two_eq_X_pow_two
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    u ^ 2 = X ^ 2 := by
  grind [u, u', z', z'_eq_one_or_z'_eq_neg_one]

lemma u'_eq_Xbar_or_u'_eq_neg_Xbar
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    u = X ∨ u = -X := by
  grind [u, u', z'_eq_one_or_z'_eq_neg_one]

lemma u'_ne_neg_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    X ≠ 1 → u ≠ -1 := by
  intro u X h1
  have hz'_cases := z'_eq_one_or_z'_eq_neg_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hXbar_ne_pm_one := Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold u u'
  grind

lemma one_add_u'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    X ≠ 1 → 1 + u ≠ 0 := by
  intro u X h1
  have hz'_cases := z'_eq_one_or_z'_eq_neg_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hXbar_ne_pm_one := Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold u u'
  grind

lemma u'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    X ≠ 1 → u ≠ 0 := by
  intro u X h1
  have hz'_cases := z'_eq_one_or_z'_eq_neg_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hz_ne_zero := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  have hXbar_ne_zero := Xbar_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
  have hXbar_ne_pm_one := Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold u u'
  grind

end u'

section v'

/-- `v'` is the `v` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def v' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let r := r s
  -- Note: this is just the definition of v as in theorem 1
  u ^ 5 + (r ^ 2 - 2) * u ^ 3 + u

lemma v'_eq_z'_mul_Y'_pow_two
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (y_ne_one : P.val.2 ≠ 1) :
    let z := z' sq_ne_pm_two hq_card hq_mod P
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    X ≠ 1 → v = z * Y ^ 2 := by
  intro z Y v X h1
  let r := r s
  let c := c s
  have hXbar_ne_pm_one := Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  have hY'_sq := Y'_pow_two_eq_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_ne_one
  have hz_cube_eq_z : z ^ 3 = z := by
    have := χ_of_a_pow_n_eq_χ_a (Y * (X ^ 2 + 1 / c ^ 2)) ⟨3, by grind⟩
    change z ^ 3 = z at this
    exact this
  have hz_pow5_eq_z : z ^ 5 = z := by
    have := χ_of_a_pow_n_eq_χ_a (Y * (X ^ 2 + 1 / c ^ 2)) ⟨5, by grind⟩
    change z ^ 5 = z at this
    exact this
  let x := P.val.1
  have hv_eq_z_mul_expand : v = z * (X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X) := by
    change (z * X) ^ 5 + (r ^ 2 - 2) * (z * X) ^ 3 + (z * X) = z * (X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X)
    repeat rw [mul_pow]
    rw [hz_cube_eq_z, hz_pow5_eq_z]
    grind
  grind

lemma v'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let v := v' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → v ≠ 0 := by
  intro X v h1
  have hv_eq_z_mul_Y_sq :=
    v'_eq_z'_mul_Y'_pow_two hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  have hv_eq_zY2 : v = z * Y ^ 2 := by grind
  rw [hv_eq_zY2]
  have hY_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  have hz_ne_zero := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  grind

end v'

lemma χ_of_v'_eq_χ_of_z'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let z := z' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let χ_of_v := χ v
    let χ_of_z := χ z
    X ≠ 1 → χ_of_v = χ_of_z := by
  intro X z v χ_of_v χ_of_z h
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  have hv_eq_zY2 :=
    v'_eq_z'_mul_Y'_pow_two hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_ne_one
  unfold χ_of_v v
  rw [hv_eq_zY2 h]
  have hY_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  rw [χ_of_a_eq_χ_a_mul_b_pow_two hY_ne_zero]

lemma χ_of_z'_eq_z' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) :
    let X := Xbar s P q
    let z := z' sq_ne_pm_two hq_card hq_mod P
    let χ_of_z := χ z
    X ≠ 1 → χ_of_z = z := by
  intro X z χ_of_z h1
  exact χ_χ_eq_χ hq_card hq_mod

lemma χ_of_v'_eq_z'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let z := z' sq_ne_pm_two hq_card hq_mod P
    let χ_of_v := χ v
    X ≠ 1 → χ_of_v = z := by
  grind [χ_of_v'_eq_χ_of_z', χ_of_z'_eq_z']

lemma X'_eq_χ_of_v'_mul_u'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let χ_of_v := χ v
    X ≠ 1 → X = χ_of_v * u := by
  intro X v u χ_of_v h1
  have hχv_eq_z := χ_of_v'_eq_z'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  unfold χ_of_v v
  rw [hχv_eq_z h1]
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hz_ne_zero := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  rw [mul_comm, ← div_left_inj' hz_ne_zero]
  rw [mul_div_assoc, div_self hz_ne_zero]
  change X / z = z * X * 1
  have hz_arg_ne_zero :=
    z'_argument_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  let c := c s
  let a := (Y * (X ^ 2 + 1 / c ^ 2))
  nth_rw 1 [← mul_one X]
  unfold z z'
  rw [mul_div_assoc, ← one_div_χ_of_a_eq_χ_a]
  grind

lemma Y'_pow_two_eq_χ_of_v'_mul_v'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let χ_of_v := χ v
    X ≠ 1 → Y ^ 2 = χ_of_v * v := by
  intro X Y v χ_of_v h1
  have hv_eq_zY2 :=
    v'_eq_z'_mul_Y'_pow_two hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hv_eq_zY2' : v = z * Y ^ 2 := by grind
  have hz_ne_zero := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  rw [mul_comm, ← div_left_inj' hz_ne_zero] at hv_eq_zY2'
  rw [mul_div_assoc, div_self hz_ne_zero, mul_one] at hv_eq_zY2'
  change v / z = Y ^ 2 at hv_eq_zY2'
  have hz_arg_ne_zero :=
    z'_argument_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let c := c s
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let r := r s
  let a := u ^ 5 + (r ^ 2 - 2) * u ^ 3 + u
  rw [← hv_eq_zY2', mul_comm]
  unfold χ_of_v v v'
  rw [one_div_χ_of_a_eq_χ_a]
  change v / z = v * (1 / χ_of_v)
  have hχv_eq_z := χ_of_v'_eq_z'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  unfold χ_of_v v
  rw [hχv_eq_z h1]
  grind

lemma χ_of_v'_eq_z'_unfold_of_X'_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let c := c s
    X ≠ 1 → (χ v) = χ (Y * (X ^ 2 + 1 / c ^ 2)) := by
  intro X Y v c h1
  rw [χ_of_v'_eq_z' hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1]
  rfl

lemma χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_div_c_pow_two
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let c := c s
    X ≠ 1 → (χ v) = χ (Y * (u ^ 2 + 1 / c ^ 2)) := by
  grind [χ_of_v'_eq_z'_unfold_of_X'_ne_one, u'_pow_two_eq_X_pow_two]

lemma u'_pow_two_add_one_div_c_pow_two_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let c := c s
    u ^ 2 + 1 / c ^ 2 ≠ 0 := by
  intro u c h
  have hneg_one_sq : -1 = (u * c) ^ 2 := by grind [pow_ne_zero, c_ne_zero]
  have hisSquare : IsSquare (-1 : F) := by
    rw [hneg_one_sq, pow_two]
    apply IsSquare.mul_self (u * c)
  have hmod_ne_three : q % 4 ≠ 3 := by
    rw [FiniteField.isSquare_neg_one_iff, hq_card] at hisSquare
    exact hisSquare
  contradiction

lemma Y'_observation1
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let c := c s
    X ≠ 1 → (χ Y) = (χ v) * χ (u ^ 2 + 1 / c ^ 2) := by
  intro X Y v u c h1
  have hχv_eq_χ_term := χ_of_v'_eq_z'_unfold_of_X'_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  have hχv_eq_χ_Yu := χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_div_c_pow_two
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let term1 := (u ^ 2 + 1 / c ^ 2)
  let term2 := Y * term1
  have hstep2 : (χ v) * χ (u ^ 2 + 1 / c ^ 2) = (χ term2) * χ (u ^ 2 + 1 / c ^ 2) := by grind
  have hstep3 : (χ v) * χ (u ^ 2 + 1 / c ^ 2) = (χ Y) * (χ term1) * χ (u ^ 2 + 1 / c ^ 2) := by
    grind [χ_mul]
  rw [hstep3]
  have hterm1_mul_self_eq_one : (χ term1) * χ (u ^ 2 + 1 / c ^ 2) = 1 := by
    rw [← pow_two]
    have hterm1_ne_zero := u'_pow_two_add_one_div_c_pow_two_ne_zero
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P
    rw [χ_of_a_even_pow_n_eq_one hterm1_ne_zero ⟨2, even_two⟩]
  grind

lemma Y'_observation2
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let c := c s
  X ≠ 1 → Y = ((χ v) * v) ^ ((q + 1) / 4) * (χ v) * χ (u ^ 2 + 1 / c ^ 2) := by
  intro X Y v u c h1
  have hχv_eq_χ_term := χ_of_v'_eq_z'_unfold_of_X'_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  have hχv_eq_χ_Yu := χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_div_c_pow_two
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  have hobs1 := Y'_observation1
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  change (χ Y) = (χ v) * χ (u ^ 2 + 1 / c ^ 2) at hobs1
  have hY_sq := Y'_pow_two_eq_χ_of_v'_mul_v'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  rw [← hY_sq, mul_assoc, ← hobs1]
  rw [← pow_mul, add_comm]
  change Y = Y ^ (2 * ((1 + q) / 4)) * (χ Y)
  nth_rw 2 [mul_comm]
  rw [one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
  rw [add_comm, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_card hq_mod]
  rw [mul_comm, ← mul_assoc]
  rw [← χ_mul, ← pow_two]
  have hY_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  rw [χ_sq hY_ne_zero]
  grind

section t'

/-- `t'` is the `t` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def t' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let u := u' sq_ne_pm_two hq_card hq_mod P
  (1 - u) / (1 + u)

lemma t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → t ≠ 1 ∧ t ≠ -1 := by
  intro X t h1
  unfold t t'
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let u'_eq_Xbar_or_u'_eq_neg_Xbar := u'_eq_Xbar_or_u'_eq_neg_Xbar
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  change u = X ∨ u = -X at u'_eq_Xbar_or_u'_eq_neg_Xbar
  change (1 - u) / (1 + u) ≠ 1 ∧ (1 - u) / (1 + u) ≠ -1
  let one_add_u'_ne_zero := one_add_u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let u'_ne_zero := u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let two_ne_zero := two_ne_zero hq_card hq_mod
  and_intros
  · intro h2
    have h3 : 2 = 0 := by grind
    contradiction
  · intro h2
    have h3 : 2 = 0 := by grind
    contradiction

lemma one_add_t'_ne_zero (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → t + 1 ≠ 0 := by
  grind [t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one]

lemma u'_eq_one_sub_t'_div_one_add_t'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P.val q
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → u = (1 - t) / (1 + t) := by
  intro X u t h1
  unfold t t'
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let one_add_u'_ne_zero := one_add_u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let two_ne_zero := two_ne_zero hq_card hq_mod
  grind

lemma u'_eq_u (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q
      X ≠ 1) :
    let u' := u' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let u := u ⟨t, t_h⟩
    u' = u := by
  grind [u', u, u'_eq_one_sub_t'_div_one_add_t']

lemma v'_eq_v (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P.val q;
      X ≠ 1) :
    let v' := v' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let v := v ⟨t, t_h⟩ s
    v' = v := by
  grind [v', v, u'_eq_one_sub_t'_div_one_add_t', u'_eq_u]

lemma X'_eq_X (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q;
      X ≠ 1) :
    let X' := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let X := X ⟨t, t_h⟩ s
    X' = X := by
  intro X' t t_h X
  let h1 := u'_eq_u hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h2 := v'_eq_v hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h3 := X'_eq_χ_of_v'_mul_u'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold X'
  rw [h3, h1, h2]
  rfl

lemma Y'_eq_Y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q;
      X ≠ 1) :
    let Y' := Y' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let Y := Y ⟨t, t_h⟩ s q
    Y' = Y := by
  intro Y' t t_h Y
  let h1 := u'_eq_u hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h2 := v'_eq_v hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h3 := Y'_observation2
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold Y'
  rw [h3, h1, h2]
  rfl

end t'

section x'

/-- `x'` is the `x` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def x' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let c := c s
  let X' := Xbar s P q
  let Y' := Y' sq_ne_pm_two hq_card hq_mod P
  (c - 1) * s * X' * (1 + X') / Y'

lemma x'_eq_x (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let x := x ⟨t, t_h⟩ s q
    let x' := x' sq_ne_pm_two hq_card hq_mod P
    x' = x := by
  intro t t_h x x'
  unfold x' ReverseProofVehicle.x' x OutputCoordinates.x
  let hY'_eq_Y := Y'_eq_Y hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let hX'_eq_X := X'_eq_X hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

/-- `y'` is the `y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def y' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q)
    (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let X' := Xbar s P q
  let r := r s
  (r * X' - (1 + X') ^ 2) / (r * X' + (1 + X') ^ 2)

lemma y'_eq_y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y' := y' sq_ne_pm_two hq_card hq_mod P
    y' = y := by
  intro t t_h y y'
  unfold y' ReverseProofVehicle.y' y OutputCoordinates.y
  let hX'_eq_X := X'_eq_X
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

theorem x'_and_y'_fulfill_curve_equation
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let x' := x' sq_ne_pm_two hq_card hq_mod P
    let y' := y' sq_ne_pm_two hq_card hq_mod P
    (curve s).Equation x' y' := by
  intro x' y'
  let t := t' sq_ne_pm_two hq_card hq_mod P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let x := x ⟨t, t_h⟩ s q
  let y := y ⟨t, t_h⟩ s
  let x'_eq_x := x'_eq_x hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let y'_eq_y := y'_eq_y hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h := curve_equation ⟨t, t_h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
  rw [curve_equation_iff]
  grind [x'_eq_x, y'_eq_y]

lemma y_eq_y_of_P (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y_of_P := P.val.2
    y = y_of_P := by
  intro t t_h y y_of_P
  let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold y_of_P
  rw [y_with_Xbar]
  unfold y OutputCoordinates.y
  let h := X'_eq_X hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

lemma x_eq_x_of_P (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let x := x ⟨t, t_h⟩ s q
    let x_of_P := P.val.1
    x = x_of_P := by
  intro t t_h x x_of_P
  let Y' := Y' sq_ne_pm_two hq_card hq_mod P
  let c := c s
  let X := Xbar s P q
  let Y'_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  change x_of_P ≠ 0 at x_ne_zero
  have h1 : Y' = (c - 1) * s * X * (1 + X) / x_of_P := by grind [Y', ReverseProofVehicle.Y']
  have h2 : x_of_P = (c - 1) * s * X * (1 + X) / Y' := by
    unfold Y' ReverseProofVehicle.Y'
    rw [← div_left_inj' x_ne_zero, ← mul_left_inj' Y'_ne_zero]
    change x_of_P / x_of_P * Y' = (c - 1) * s * X * (1 + X) / Y' / x_of_P * Y'
    grind
  rw [h2]
  let h3 := Y'_eq_Y
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h4 := X'_eq_X
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold Y' X
  rw [h3, h4]
  rfl

lemma x_y_of_P_eq_x_y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y_of_P := P.val.2
    let x := x ⟨t, t_h⟩ s q
    let x_of_P := P.val.1
    (x, y) = (x_of_P, y_of_P) := by
  grind [x_eq_x_of_P, y_eq_y_of_P]

end x'

end Elligator.Elligator1.ReverseProofVehicle
