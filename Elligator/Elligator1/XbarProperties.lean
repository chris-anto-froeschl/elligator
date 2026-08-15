/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Elligator.Elligator1.MapProperties
public import Elligator.Elligator1.etaProperties

/-!
# Xbar Variable Properties

In this file we introduce some generally helpful lemmas for `Xbar` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.3, Theorem 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

omit [DecidableEq F] in
lemma Xbar_eq_neg_one
  [DecidableEq F]
  (t : { t : F // t = 1 ∨ t = -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
  let Xbar := Xbar s P.1 q
  Xbar = -1 := by
    intro P Xbar
    unfold Xbar Elligator1.Xbar
    let η := η P.1
    change -(1 + η * (r s)) + ((1 + η * (r s)) ^ 2 - 1) ^ ((q + 1) / 4) = -1
    unfold η
    rw [η_eq_zero t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
    ring_nf
    rw [zero_pow, add_zero]
    exact q_add_one_div_four_ne_zero hq_mod

lemma Xbar_h1
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let η_of_P := η P.val
  let r := r s
  let Xbar := Xbar s P q
  (1 + η_of_P * r + Xbar)^2 = (1 + η_of_P * r)^2 - 1 := by
    intro η_of_P r Xbar
    unfold Xbar Elligator1.Xbar
    let a := ((1 + η_of_P * r)^2 - 1)^((q + 1) / 4)
    let a_sqr := (1 + η_of_P * r)^2 - 1
    change (1 + η_of_P * r + (-(1 + η_of_P * r) + a))^2 = a_sqr
    ring_nf
    unfold a a_sqr
    nth_rw 2 [add_comm]
    rw [← pow_mul, one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
    unfold η_of_P
    nth_rw 2 [add_comm]
    rw [a_pow_q_add_one_div_two_eq_a P.prop.2.1 hq_card hq_mod]

lemma Xbar_h2
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let η := η P.val
  let r := r s
  let Xbar := Xbar s P q
  Xbar^2 + 2 * (1 + η * r) * Xbar + 1 = 0 := by
    intro η r Xbar
    have h := Xbar_h1 hq_card hq_mod P
    grind

omit [DecidableEq F] in
lemma Xbar_h3
  [DecidableEq F]
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
  let X' := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  let X := X t s
  let Xbar := Xbar s P.val q
  (Xbar - X) * (Xbar - X') = 0 := by
    intro t1 t2 P X' X Xbar
    let η := η P.val
    let r := r s
    let P_of_ϕ_fulfills_ϕOverFProps :=
      P_of_ϕ_fulfills_ϕOverFProps t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    calc
      (Xbar - X) * (Xbar - X') = Xbar^2 - (X + X') * Xbar + X * X' := by grind
      _ = Xbar^2 + 2 * (1 + η * r) * Xbar + 1 := by
        rw [X_comparison_implication t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
        change Xbar ^ 2 - -2 * (1 + η * r) * Xbar + X * X' = Xbar ^ 2 + 2 * (1 + η * r) * Xbar + 1
        rw [mul_add, mul_comm X _]
        rw [X_comparison_implication2 t hs_ne_zero hq_card hq_mod]
        grind
      _ = 0 := Xbar_h2 hq_card hq_mod ⟨P.val, P_of_ϕ_fulfills_ϕOverFProps⟩

omit [DecidableEq F] in
lemma Xbar_h4
  [DecidableEq F]
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
  let X' := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  let X := X t s
  let Xbar := Xbar s P q
  Xbar = X ∨ Xbar = X' := by
    intro t1 t2 P X' X Xbar
    have h := Xbar_h3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    grind

lemma Xbar_ne_zero
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let Xbar := Xbar s P q
  Xbar ≠ 0 := by
    intro Xbar
    have h := Xbar_h2 hq_card hq_mod P
    let η := η P.val
    let r := r s
    change Xbar^2 + 2 * (1 + η * r) * Xbar + 1 = 0 at h
    intro h'
    rw [h'] at h
    simp at h

lemma y_divisor_ne_zero_with_Xbar_for_X
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let r := r s
  let Xbar := Xbar s P q
  r * Xbar + (1 + Xbar)^2 ≠ 0 := by
    intro r Xbar h1
    let η := η P.val
    have h2 := Xbar_h2 hq_card hq_mod P
    change Xbar^2 + 2 * (1 + η * r) * Xbar + 1 = 0 at h2
    let y := P.val.2
    have h3 : 2 * η = 1 := by
      have hne : r * Xbar ≠ 0 :=
        mul_ne_zero (r_ne_zero hs_ne_zero hq_card hq_mod) (Xbar_ne_zero hq_card hq_mod P)
      rw [← div_left_inj' hne]
      grind
    have h4 : y - 1 = y + 1 := by
      unfold η Elligator1.η at h3
      grind
    have h5 : y - 1 ≠ y + 1 := by grind
    contradiction

lemma Xbar_ne_neg_one
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let Xbar := Xbar s P q
  Xbar ≠ -1 := by
    intro Xbar h1
    let η := η P.val
    let Xbar_equation := Xbar_h2 hq_card hq_mod P
    let r := r s
    let P_prop := P.prop
    let y := P.val.2
    change Xbar^2 + 2 * (1 + η * r) * Xbar + 1 = 0 at Xbar_equation
    rw [h1] at Xbar_equation
    have h2 : η = 0 := by
      ring_nf at Xbar_equation
      let r_ne_zero := r_ne_zero hs_ne_zero hq_card hq_mod
      rw [← div_left_inj' (two_ne_zero hq_card hq_mod)] at Xbar_equation
      rw [← div_left_inj' r_ne_zero] at Xbar_equation
      ring_nf at Xbar_equation
      have h2_1 : -(η * r * 2⁻¹ * r⁻¹ * 2) = -(η * (r * r⁻¹) * (2 * 2⁻¹)) := by grind
      rw [h2_1] at Xbar_equation
      rw [mul_inv_cancel₀ r_ne_zero, mul_inv_cancel₀ (two_ne_zero hq_card hq_mod)] at Xbar_equation
      grind
    have h3 : η ≠ 0 := by
      unfold η Elligator1.η
      have h3_1 : y - 1 ≠ 0 := by grind
      have h3_2 : 2 * (y + 1) ≠ 0 := by
        intro h3_2_1
        let y_add_one_ne_zero := P_prop.1
        unfold ϕOverFProp1 at y_add_one_ne_zero
        rw [← div_left_inj' (two_ne_zero hq_card hq_mod)] at h3_2_1
        ring_nf at h3_2_1
        rw [inv_mul_cancel₀ (two_ne_zero hq_card hq_mod)] at h3_2_1
        grind
      apply div_ne_zero h3_1 h3_2
    contradiction

lemma Xbar_add_one_ne_zero
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_ne_one : P.val.2 ≠ 1)
  :
  let Xbar := Xbar s P q
  Xbar + 1 ≠ 0 := by grind [Xbar_ne_neg_one]

lemma y_with_Xbar
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let Xbar := Xbar s P.val q
  let r := r s
  let y := P.val.2
  y = (r * Xbar - (1 + Xbar)^2) / (r * Xbar + (1 + Xbar)^2) := by
    intro Xbar r y
    let Xbar_equation := Xbar_h2 hq_card hq_mod P
    let η := η P.val
    let y_add_one_ne_zero := P.prop.1
    let Xbar_ne_zero := Xbar_ne_zero hq_card hq_mod P
    let two_ne_zero := two_ne_zero hq_card hq_mod
    let r_ne_zero := r_ne_zero hs_ne_zero hq_card hq_mod
    change Xbar^2 + 2 * (1 + η * r) * Xbar + 1 = 0 at Xbar_equation
    have h1 : y = (1 + 2 * η) / (1 - 2 * η) := by
      have h1_1 : η = (y - 1) / (2 * (y + 1)) := by simp [η, Elligator1.η, y]
      have h1_2 : (2 * (y + 1)) ≠ 0 := mul_ne_zero two_ne_zero y_add_one_ne_zero
      grind
    have h2 : 2 * η = - ((1 + Xbar)^2) / (r * Xbar) := by
      have h2_1 : 1 + η * r = - (Xbar^2 + 1) / (2 * Xbar) := by
        have h2_1_1 : 2 * Xbar ≠ 0 := mul_ne_zero two_ne_zero Xbar_ne_zero
        rw [← add_left_inj (-Xbar^2), ← add_left_inj (-1)] at Xbar_equation
        rw [← div_left_inj' h2_1_1] at Xbar_equation
        grind
      have h2_2 : 2 * η = -((1 + Xbar)^2) / (r * Xbar) := by
        have h2_2_1 : η = (-(Xbar^2 + 1) / (2 * Xbar) -1) / r := by grind
        have h2_2_2 : η = -(Xbar + 1)^2 / (2 * r * Xbar) := by
          have h2_2_2_1 : (2 * Xbar) / (2 * Xbar) = 1 := by grind
          rw [← h2_2_2_1] at h2_2_1
          rw [h2_2_1]
          ring_nf
          grind
        rw [← mul_left_inj' two_ne_zero] at h2_2_2
        ring_nf
        grind
      grind
    have h3 : (1 + 2 * η) / (1 - 2 * η)
        = ((r * Xbar - (1 + Xbar)^2)) / ((r * Xbar + (1 + Xbar)^2)) := by
      have h3_1 : 1 = (r * Xbar) / (r * Xbar) := by grind
      rw [h2]
      nth_rw 1 [h3_1]
      nth_rw 2 [h3_1]
      rw [← add_div, ← sub_div, div_div]
      grind
    rw [← h3]
    exact h1

lemma y_with_Xbar_of_Xbar_eq_one
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let Xbar := Xbar s P.val q
  let r := r s
  let y := P.val.2
  Xbar = 1 → y = (r - 4) / (r + 4) := by grind [y_with_Xbar]

lemma η_mul_r_eq_neg_two_of_Xbar_eq_one
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let η := η P
  let Xbar := Xbar s P q
  let r := r s
  Xbar = 1 → η * r = -2 := by
    intro η  Xbar r Xbar_h
    let h1 := Xbar_h2 hq_card hq_mod P
    let two_ne_zero := two_ne_zero hq_card hq_mod
    change Xbar^2 + 2 * (1 + η *r) * Xbar + 1 = 0 at h1
    rw [Xbar_h, ← add_left_inj (-4), ← div_left_inj' two_ne_zero] at h1
    ring_nf at h1
    grind

lemma Xbar_observation1_of_Xbar_ne_one
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let Xbar := Xbar s P.val q
  let y := P.val.2
  let r := r s
  Xbar ≠ 1 → (r * Xbar + (1 + Xbar)^2)^2 * (1 - y^2) = 4 * r * Xbar * (1 + Xbar)^2 := by
    intro Xbar y r Xbar_h
    let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod P y_eq_one
    let y_divisor_ne_zero_with_Xbar_for_X :=
      y_divisor_ne_zero_with_Xbar_for_X hs_ne_zero hq_card hq_mod
    change y = (r * Xbar - (1 + Xbar)^2) / (r * Xbar + (1 + Xbar)^2) at y_with_Xbar
    have h1 : (r * Xbar + (1 + Xbar)^2)^2 * (1 - y^2)
      = (r * Xbar + (1 + Xbar)^2)^2 - (r * Xbar - (1 + Xbar)^2)^2 := by
      rw [y_with_Xbar, div_pow, mul_sub, ← mul_div_assoc]
      nth_rw 3 [mul_comm]
      have h1_1 : (r * Xbar + (1 + Xbar) ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (by simp_all; grind)
      rw [mul_div_assoc, div_self h1_1]
      ring_nf
    grind

lemma Xbar_observation2_of_Xbar_ne_one
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let Xbar := Xbar s P.val q
  let y := P.val.2
  let r := r s
  let d := d s;
  Xbar ≠ 1 → (r * Xbar + (1 + Xbar)^2)^2 * (1 - d * y^2)
    = ((2 * r) / (r - 2)) * (Xbar^4 + (r^2 - 2) * Xbar^2 + 1) := by
    intro Xbar y r d Xbar_h
    let neg_d_eq_r_add_two_div_r_sub_two :=
      neg_d_eq_r_add_two_div_r_sub_two hs_ne_zero hq_card hq_mod
    change -d = (r + 2) / (r - 2) at neg_d_eq_r_add_two_div_r_sub_two
    let y_divisor_ne_zero_with_Xbar_for_X :=
      y_divisor_ne_zero_with_Xbar_for_X hs_ne_zero hq_card hq_mod
    let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod P y_eq_one
    change y = (r * Xbar - (1 + Xbar)^2) / (r * Xbar + (1 + Xbar)^2) at y_with_Xbar
    have h1 : (r * Xbar + (1 + Xbar)^2)^2 * (1 - d * y^2)
      = (r * Xbar + (1 + Xbar)^2)^2 + (r + 2) / (r - 2) * ((r * Xbar - (1 + Xbar)^2)^2) := by
      rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← mul_assoc, ← neg_eq_neg_one_mul]
      rw [neg_d_eq_r_add_two_div_r_sub_two, y_with_Xbar, div_pow, mul_add]
      nth_rw 3 [mul_comm]
      have h1_1 : (r * Xbar + (1 + Xbar)^2)^2 ≠ 0 := pow_ne_zero 2 (by simp_all; grind)
      rw [← mul_div_assoc, div_mul, mul_div_assoc, div_self h1_1]
      grind
    have h2 : (1 + Xbar)^2 = Xbar^2 + 2 * Xbar + 1 := by grind
    rw [h1, h2]
    let A := r * Xbar + (Xbar^2 + 2 * Xbar + 1)
    let B := r * Xbar - (Xbar^2 + 2 * Xbar + 1)
    change A^2 + (r + 2) / (r - 2) * B^2 = 2 * r / (r - 2) * (Xbar^4 + (r^2 - 2) * Xbar^2 + 1)
    have h3 : A^2
        = Xbar^ 4 + 2 * (r + 2) * Xbar^3 + ((r + 2)^2 + 2) * Xbar^2 + 2 * (r + 2) * Xbar + 1 := by
      ring
    have h4 : B^2
        = Xbar^ 4 - 2 * (r - 2) * Xbar^3 + ((r - 2)^2 + 2) * Xbar^2 - 2 * (r - 2) * Xbar + 1 := by
      ring
    rw [h3, h4]
    let r_sub_two_ne_zero :=
      r_sub_two_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod
    have X_pow_four_term : Xbar^4 + (r + 2) / (r - 2) * Xbar^4
      = Xbar^4 * (2 * r) / (r - 2) := by grind
    have X_pow_three_term : Xbar^3 * 2 * (r + 2) + (r + 2) / (r - 2) * (-2 * (r - 2) * Xbar^3)
        = 0 := by grind
    have X_pow_two_term : Xbar^2 * (r^2+ 4 * r + 6) + (r + 2) / (r - 2) * (r^2 - 4 * r + 6) * Xbar^2
        = Xbar^2 * (2 * r * (r^2 - 2) / (r - 2)) := by
      nth_rw 3 [mul_comm]
      rw [← mul_add (Xbar^2)]
      have h5 : (r^2 + 4 * r + 6 + (r + 2) / (r - 2) * (r^2 - 4 * r + 6))
        = ((r^2 + 4 * r + 6) * (r - 2) + (r + 2) * (r^2 - 4 * r + 6)) / (r - 2) := by grind
      rw [h5]
      have h6 : (r^2 + 4 * r + 6) * (r - 2) = r^3 + 2 * r^2 - 2 * r - 12 := by ring
      have h7 : (r + 2) * (r^2 - 4 * r + 6) = r^3 - 2 * r^2 - 2 * r + 12 := by ring
      rw [h6, h7]
      have h8 : r^3 + 2 * r^2 - 2 * r - 12 + (r^3 - 2 * r^2 - 2 * r + 12) = 2 * r^3 - 4 * r := by
        ring
      ring
    have X_pow_one_term : 2 * (r + 2) * Xbar - 2 * (r + 2) * Xbar = 0 := by ring
    have const_term : 1 + (r + 2) / (r - 2) = (2 * r) / (r - 2) := by grind
    grind

lemma one_sub_d_mul_y_pow_two_ne_zero
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let y := P.val.2
  let d := d s;
  1 - d * y^2 ≠ 0 := by
    intro y d h1
    let d_ne_zero := d_ne_zero sq_ne_pm_two hq_card hq_mod
    rw [← add_left_inj (d * y^2)] at h1
    ring_nf at h1
    rw [mul_comm, ← div_left_inj' d_ne_zero, mul_div_assoc, div_self d_ne_zero, mul_one] at h1
    change 1 / d = y^2 at h1
    have h2 : IsSquare (1 / d) := by
      unfold IsSquare
      use y
      grind
    let h3 := one_div_d_nonsquare sq_ne_pm_two hq_card hq_mod
    change ¬IsSquare (1 / d) at h3
    contradiction

lemma x_pow_two_of_Xbar_ne_one_eq1
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod})
  (P_props : ϕOverFProps s P)
  :
  let x := P.val.1
  let y := P.val.2
  let d := d s;
  x^2 = (1 - y^2) / (1 - d*y^2) := by
    intro x y d
    have curve_equation := P.prop;
    unfold EOverF at curve_equation
    simp_all only [edwardsCurveEquation_iff]
    let one_sub_d_mul_y_pow_two_ne_zero :=
      one_sub_d_mul_y_pow_two_ne_zero sq_ne_pm_two hq_card hq_mod ⟨P.val, P_props⟩
    change 1 - d * y^2 ≠ 0 at one_sub_d_mul_y_pow_two_ne_zero
    rw [Set.mem_setOf_eq] at curve_equation
    change x^2 + y^2 = 1 + d * x^2 * y^2  at curve_equation
    rw [← add_left_inj (-d * x^2 * y^2 - y^2)] at curve_equation
    ring_nf at curve_equation
    nth_rw 1 [← mul_one (x^2)] at curve_equation
    rw [mul_assoc, ← mul_sub (x^2)] at curve_equation
    nth_rw 2 [mul_comm] at curve_equation
    rw [← div_left_inj' one_sub_d_mul_y_pow_two_ne_zero] at curve_equation
    grind

lemma x_pow_two_of_Xbar_ne_one_eq2_of_Xbar_ne_one
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod})
  (P_props : ϕOverFProps s P)
  (y_eq_one : P.val.2 ≠ 1)
  :
  let x := P.val.1
  let X := Xbar s P q
  let r := r s
  X ≠ 1 → x^2 = (2 * (r -2) * X^2 * (1 + X)^2) / (X^5 + (r^2 - 2) * X^3 + X) := by
    intro x X r Xh
    let y := P.val.2
    let d := d s;
    let x_pow_two_of_Xbar_ne_one_eq1 :=
      x_pow_two_of_Xbar_ne_one_eq1 sq_ne_pm_two hq_card hq_mod P P_props
    change x^2 = (1 - y^2) / (1 - d*y^2) at x_pow_two_of_Xbar_ne_one_eq1
    let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_eq_one
    change y = (r * X - (1 + X)^2) / (r * X + (1 + X)^2) at y_with_Xbar
    let y_divisor_ne_zero_with_Xbar_for_X :=
      y_divisor_ne_zero_with_Xbar_for_X hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
    change r * X + (1 + X)^2 ≠ 0 at y_divisor_ne_zero_with_Xbar_for_X
    have h1 : (r * X + (1 + X)^2)^2 ≠ 0 := by grind
    have h2 : 1 = ((r * X + (1 + X)^2)^2) / ((r * X + (1 + X)^2)^2) := by grind
    let Xbar_observation1_of_Xbar_ne_one :=
      Xbar_observation1_of_Xbar_ne_one hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_eq_one
    change X ≠ 1 →
      (r * X + (1 + X)^2)^2 * (1 - y^2) = 4 * r * X * (1 + X)^2 at Xbar_observation1_of_Xbar_ne_one
    have h3 : (r * X + (1 + X)^2)^2 * (1 - y^2) = 4 * r * X * (1 + X)^2 := by grind
    let Xbar_observation2_of_Xbar_ne_one := Xbar_observation2_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod ⟨P.val, P_props⟩ y_eq_one
    change X ≠ 1 → (r * X + (1 + X)^2)^2 * (1 - d * y^2)
      = ((2 * r) / (r - 2)) * (X^4 + (r^2 - 2) * X^2 + 1) at Xbar_observation2_of_Xbar_ne_one
    have h4 : (r * X + (1 + X)^2)^2 * (1 - d * y^2)
      = ((2 * r) / (r - 2)) * (X^4 + (r^2 - 2) * X^2 + 1) := by grind
    let X_ne_zero := Xbar_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
    change X ≠ 0 at X_ne_zero
    calc
      x^2 = (1 - y^2) / (1 - d*y^2) := by grind
      _ = (4 * r * X * (1 + X)^2) / ((2 * r) / (r - 2) * (X^4 + (r^2 - 2) * X^2 + 1)) := by
        rw [← one_mul (1 - y^2), ← one_mul (1 - d * y^2)]
        nth_rw 1 [h2]
        rw [mul_div_assoc, div_mul_div_comm]
        grind
      _ = (2 * (r - 2) * X * (1 + X)^2) / (X^4 + (r^2 - 2) * X^2 + 1) := by
        let r_sub_two_ne_zero := r_sub_two_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod
        change r - 2 ≠ 0 at r_sub_two_ne_zero
        have h' : 1 = (r - 2) / (r - 2) := by grind
        rw [← one_mul ((4 * r * X * (1 + X)^2) / ((2 * r) / (r - 2) * (X^4 + (r^2 - 2) * X^2 + 1)))]
        nth_rw 1 [h']
        rw [div_mul_div_comm]
        nth_rw 2 [← mul_assoc]
        nth_rw 1 [← mul_div_assoc]
        rw [mul_comm (r - 2) (2 * r), mul_div_assoc]
        nth_rw 2 [mul_div_assoc]
        rw [div_self r_sub_two_ne_zero, ← mul_div_assoc]
        have h'' :
          (r - 2) * (4 * r * X * (1 + X)^2) / (2 * r * 1 * (X^4 + (r^2 - 2) * X^2 + 1))
          = (r - 2) * (2 * X * (1 + X)^2) / ((X^4 + (r^2 - 2) * X^2 + 1)) := by
          have h''' : (4 * r) / (2 * r) = 2 := by
            let two_ne_zero := two_ne_zero hq_card hq_mod
            let r_ne_zero := (r_ne_zero hs_ne_zero hq_card hq_mod)
            rw [← mul_left_inj' two_ne_zero]
            ring_nf
            rw [mul_inv_cancel₀ r_ne_zero]
            grind
          have h'''' :
            (r - 2) * (4 * r * X * (1 + X)^2) / (2 * r * 1 * (X^4 + (r^2 - 2) * X^2 + 1))
            = ((r - 2) * (X * (1 + X)^2)) * (4 * r) / ((2 * r) * (X^4 + (r^2 - 2) * X^2 + 1)) := by
              grind
          rw [h'''', div_mul_eq_div_div, mul_div_assoc, h''']
          grind
        rw [h'']
        grind
      _ = (2 * (r -2) * X^2 * (1 + X)^2) / (X^5 + (r^2 - 2) * X^3 + X) := by
        have h5 : 1 = X / X := by grind
        nth_rw 1 [← one_mul ((2 * (r - 2) * X * (1 + X)^2) / (X^4 + (r^2 - 2) * X^2 + 1)), h5]
        rw [div_mul_div_comm]
        ring_nf

/-- `Y'` is the `Y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def Y'
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod})
  : F :=
  let x := P.val.1
  let c := c s
  let X := Xbar s P q
  -- This is just `def x` with the denominator `Y` replaced by `x` of P
  (c - 1) * s * X * (1 + X) / x

lemma Y'_pow_two_eq_of_Xbar_ne_one
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod})
  (P_props : ϕOverFProps s P)
  (y_eq_one : P.val.2 ≠ 1)
  :
  let X := Xbar s P q
  let r := r s
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  -- This is just `def x` with the denominator `Y` replaced by `x` of P
  X ≠ 1 → Y^2 = X^5 + (r^2 - 2) * X^3 + X := by
    intro X r Y Xh
    let c := c s
    let x := P.val.1
    let h := x_pow_two_of_Xbar_ne_one_eq2_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_eq_one
    let two_ne_zero := two_ne_zero hq_card hq_mod
    have h' : x^2 = (2 * (r -2) * X^2 * (1 + X)^2) / (X^5 + (r^2 - 2) * X^3 + X) := h Xh
    calc
     Y^2 = (c - 1)^2 * s^2 * X^2 * (1 + X)^2 / (x^2) := by
      unfold Y Y'
      change ((c - 1) * s * X * (1 + X) / x)^2 = (c - 1)^2 * s^2 * X^2 * (1 + X)^2 / (x^2)
      rw [div_pow]
      repeat rw [← mul_pow]
    _ = 2 * (r - 2) * X^2 * (1 + X)^2 / (x^2) := by
      have h : (c - 1)^2 * s^2 = 2 * (r - 2) := by
        unfold r Elligator1.r c Elligator1.c
        field_simp [hs_ne_zero]
        ring_nf
      rw [h]
    _ = X^5 + (r^2 - 2) * X^3 + X := by
      have h'' : (2 * (r - 2) * X^2 * (1 + X)^2) ≠ 0 := by
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
      nth_rw 1 [← div_one (2 * (r - 2) * X^2 * (1 + X)^2)]
      rw [div_div_div_comm, div_self h'']
      grind

lemma Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_ne_one : P.val.2 ≠ 1)
  :
  let Xbar := Xbar s P q
  Xbar ≠ 1 → Xbar ≠ 1 ∧ Xbar ≠ -1 := by grind [Xbar_ne_neg_one]

end Elligator.Elligator1
