/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.XbarProperties
public import Elligator.Elligator1.zProperties

/-!
# ubar Properties

In this file we introduce some generally helpful lemmas for `ubar` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

lemma ubar_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let ubar := ubar s P q
    ubar = 0 := by
  grind [z_eq_zero, ubar]

lemma ubar_eq_u (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      let X := X t s
      let Xbar := Xbar s P q
      Xbar = X) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let u := u t
    let ubar := ubar s P q
    ubar = u := by
  intro P u ubar
  let X := X t s
  let Xbar := Xbar s P q
  let c := c s
  let x := x t s q
  let Y := Y t s q
  let z := z s P q
  let v := v t s;
  let χ_of_v := χ v
  let χ_of_Y := χ Y
  unfold ubar Elligator1.ubar
  rw [hXXbar]
  change z * X = u
  have hXbar_expand_eq_x_mul_Y : (c - 1) * s * Xbar * (1 + Xbar) = x * Y := by
    unfold Xbar
    rw [hXXbar]
    rw [← div_left_inj' (Y_ne_zero hs_ne_zero hq_card hq_mod t)]
    change x = x * Y / Y
    rw [mul_div_assoc, div_self (Y_ne_zero hs_ne_zero hq_card hq_mod t)]
    ring_nf
  have hz_eq_χY_mul_χ_sum : z = χ_of_Y * χ (X ^ 2 + 1 / c ^ 2) := by
    calc
      z = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2)) := by
        unfold z Elligator1.z
        change χ ((c - 1) * s * Xbar * (1 + Xbar) * P.1 * (Xbar ^ 2 + 1 / c ^ 2))
          = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2))
        unfold P ϕ
        simp only [hXbar_expand_eq_x_mul_Y]
        rw [dite_eq_left t.prop]
        change χ (x * Y * x * (Xbar ^ 2 + 1 / c ^ 2)) = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2))
        unfold Xbar X
        rw [hXXbar]
        ring_nf
      _ = χ_of_Y * χ (X ^ 2 + 1 / c ^ 2) := by
        rw [χ_mul, χ_mul]
        rw [χ_a_eq_one (pow_ne_zero 2
          (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t))
          (IsSquare.sq x)]
        unfold χ_of_Y
        ring
  have hχu_sum_eq_χX_sum : χ (u ^ 2 + 1 / c ^ 2) = χ (X ^ 2 + 1 / c ^ 2) := by
    unfold X Elligator1.X
    rw [mul_pow]
    nth_rw 3 [pow_two]
    rw [← χ_mul]
    rw [← pow_two, χ_a_eq_one
      (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod t)) (IsSquare.sq v)]
    unfold u
    simp_all
  have hχY_eq_χv_mul_χ_sum : χ_of_Y = χ_of_v * χ (X ^ 2 + 1 / c ^ 2) := by
    rw [← hχu_sum_eq_χX_sum]
    unfold χ_of_Y Y Elligator1.Y
    let χ_sum := χ (u ^ 2 + 1 / c ^ 2)
    change χ ((χ_of_v * v) ^ ((q + 1) / 4) * χ_of_v * χ_sum) = χ_of_v * χ_sum
    rw [mul_assoc, χ_mul]
    rw [χ_a_eq_one
      (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero t hs_ne_zero hq_card hq_mod)
      (χ_IsSquare_h1 t hs_ne_zero hq_card hq_mod)]
    rw [χ_mul]
    rw [χ_χ_eq_χ hq_card hq_mod]
    rw [χ_χ_eq_χ hq_card hq_mod]
    unfold χ_of_v χ_sum
    simp_all
  have hz_eq_χv : z = χ_of_v := by
    rw [hz_eq_χY_mul_χ_sum, hχY_eq_χv_mul_χ_sum, mul_assoc, ← χ_mul, ← pow_two]
    rw [χ_a_eq_one
      (pow_ne_zero 2 (X_pow_two_add_one_div_c_pow_two_ne_zero hs_ne_zero hq_card hq_mod t))
      (IsSquare.sq (X ^ 2 + 1 / c ^ 2))]
    simp
  rw [hz_eq_χv]
  unfold X Elligator1.X
  change χ_of_v * (χ_of_v * u) = u
  rw [← mul_assoc, ← χ_mul, ← pow_two]
  have hv_sq_isSquare : IsSquare (v ^ 2) := IsSquare.sq v
  rw [χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod t)) hv_sq_isSquare]
  simp

lemma ubar_eq_u' (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
      let Xbar := Xbar s P q
      Xbar = X') :
    let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let u' := u ⟨-t.val, t_h⟩
    let ubar := ubar s P q
    ubar = u' := by
  intro t_h P u' ubar
  let X' := X ⟨-t.val, t_h⟩ s
  let X := X t s
  let Xbar := Xbar s P q
  let c := c s
  let x' := x ⟨-t.val, t_h⟩ s q
  let x := x t s q
  let Y' := Y ⟨-t.val, t_h⟩ s q
  let Y := Y t s q
  let z := z s P q
  let v' := v ⟨-t.val, t_h⟩ s
  let v := v t s;
  unfold ubar Elligator1.ubar
  rw [hXXbar]
  change z * X' = u'
  have hXbar_expand_eq_x'_mul_Y' : (c - 1) * s * Xbar * (1 + Xbar) = x' * Y' := by
    unfold Xbar
    rw [hXXbar]
    rw [← div_left_inj' (Y_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩)]
    change x' = x' * Y' / Y'
    rw [mul_div_assoc, div_self (Y_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩)]
    ring_nf
  have hz_eq_χY'_mul_χ_sum : z = (χ Y') * (χ (X'^2 + 1 / c ^ 2)) := by
    calc
      z = (χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))) := by
        unfold z Elligator1.z
        change χ ((c - 1) * s * Xbar * (1 + Xbar) * P.1 * (Xbar ^ 2 + 1 / c ^ 2))
          = χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))
        unfold P ϕ
        simp only [hXbar_expand_eq_x'_mul_Y']
        rw [dite_eq_left t.prop]
        change χ (x' * Y' * x * (Xbar ^ 2 + 1 / c ^ 2)) = χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))
        unfold Xbar X' x' x
        rw [x_comparison t hs_ne_zero hq_card hq_mod]
        rw [hXXbar]
        ring_nf
      _ = (χ Y') * χ (X'^2 + 1 / c ^ 2) := by
        rw [χ_mul]
        rw [χ_mul]
        rw [χ_a_eq_one (pow_ne_zero 2
          (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod ⟨-t, t_h⟩))
          (IsSquare.sq x')]
        ring_nf
  have hχu'_sum_eq_χX'_sum : (χ (u'^2 + 1 / c ^ 2)) = (χ (X'^2 + 1 / c ^ 2)) := by
    unfold X' Elligator1.X
    rw [mul_pow]
    nth_rw 3 [pow_two]
    rw [← χ_mul]
    rw [← pow_two, χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod ⟨-t, t_h⟩))
      (IsSquare.sq v')]
    unfold u'
    simp_all
  have hχY'_eq_χv'_mul_χ_sum : (χ Y') = (χ v') * (χ (X'^2 + 1 / c ^ 2)) := by
    rw [← hχu'_sum_eq_χX'_sum]
    unfold Y' Elligator1.Y
    let χ_sum := χ (u'^2 + 1 / c ^ 2);
    change (χ (((χ v') * v') ^ ((q + 1) / 4) * (χ v') * χ_sum)) = (χ v') * χ_sum
    rw [mul_assoc, χ_mul]
    rw [χ_a_eq_one
      (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero ⟨-t.val, t_h⟩ hs_ne_zero hq_card hq_mod)
      (χ_IsSquare_h1 ⟨-t.val, t_h⟩ hs_ne_zero hq_card hq_mod)]
    rw [χ_mul, χ_χ_eq_χ hq_card hq_mod]
    rw [χ_χ_eq_χ hq_card hq_mod]
    unfold χ_sum
    simp_all
  have hz_eq_χv' : z = (χ v') := by
    rw [hz_eq_χY'_mul_χ_sum, hχY'_eq_χv'_mul_χ_sum, mul_assoc]
    rw [← χ_mul, ← pow_two]
    rw [χ_a_eq_one (pow_ne_zero 2
        (X_pow_two_add_one_div_c_pow_two_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩))
      (IsSquare.sq (X'^2 + 1 / c ^ 2))]
    simp
  rw [hz_eq_χv']
  unfold X' Elligator1.X
  change (χ v') * ((χ v') * u') = u'
  rw [← mul_assoc, ← χ_mul, ← pow_two]
  have hv'_sq_isSquare : IsSquare (v'^2) := IsSquare.sq v'
  rw [χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩))
    hv'_sq_isSquare]
  simp

lemma ubar_h1 (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let u' := u ⟨-t.val, t_h⟩
    let u := u t
    let ubar := ubar s P.val q
    ubar = u ∨ ubar = u' := by
  intro P t_h u' u ubar
  rcases (Xbar_h4 t hs_ne_zero sq_ne_pm_two hq_card hq_mod) with h | h
  · left
    exact ubar_eq_u t hs_ne_zero sq_ne_pm_two hq_card hq_mod h
  · right
    exact ubar_eq_u' t hs_ne_zero sq_ne_pm_two hq_card hq_mod h

/-- The key step: rewriting `1 + ubar(ϕ(t))` in the main case (t ≠ ±1) to show it is ne_zero,
    using `ubar_h1` which gives `ubar = u(t)` or `ubar = u(-t)`. -/
lemma one_add_ubar_ne_zero_main_case (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : (s : F) ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    let ubar := ubar s P q
    1 + ubar ≠ 0 := by
  intro P ubar
  unfold ubar
  obtain h|h := ubar_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · rw [h]
    exact one_add_u_ne_zero t hq_card hq_mod
  · rw [h]
    have ht_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    exact one_add_u_ne_zero ⟨-t.val, ht_h⟩ hq_card hq_mod

lemma one_add_ubar_ne_zero_base_case (t : {n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    let ubar := ubar s P q
    1 + ubar ≠ 0 := by
  intro P ubar
  unfold ubar
  rw [ubar_eq_zero, add_zero]
  exact one_ne_zero' F

lemma one_add_ubar_ne_zero (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod}) :
    let ubar := ubar s P q
    (1 + ubar) ≠ 0 := by
  intro ubar
  have hP_prop := P.prop
  unfold ϕOverF at hP_prop
  obtain ⟨t, ht⟩ := hP_prop
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · have hne := one_add_ubar_ne_zero_main_case ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
    grind
  · have ht_eq : t = 1 ∨ t = -1 := by grind
    have hne := one_add_ubar_ne_zero_base_case ⟨t, ht_eq⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
    grind

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

end Elligator.Elligator1
