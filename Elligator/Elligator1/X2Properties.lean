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
# X2 Variable Properties

In this file we introduce some generally helpful lemmas for `X2` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a] chapter 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

@[blueprint "lemma:X2_eq_neg_one"]
lemma X2_eq_neg_one
  (t : { t : F // t = 1 ∨ t = -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3
  let X2 := X2 s P.1 q
  X2 = -1 := by
    intro P X2
    unfold X2 Elligator1.X2
    let η := η P.1
    change -(1 + η * (r s)) + ((1 + η * (r s)) ^ 2 - 1) ^ ((q + 1) / 4) = -1
    unfold η
    rw [η_eq_zero t s_h1 s_h2 q_h1 q_h2 q_h3]
    ring_nf
    rw [zero_pow, add_zero]
    exact q_add_one_over_four_ne_zero q_h3

@[blueprint "lemma:X2_h1"]
lemma X2_h1
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let η_of_P := η P.val
  let r := r s
  let X2 := X2 s P q
  (1 + η_of_P * r + X2)^2 = (1 + η_of_P * r)^2 - 1 := by
    intro η_of_P r X2
    unfold X2 Elligator1.X2
    let a := ((1 + η_of_P * r)^2 - 1)^((q + 1) / 4)
    let a_sqr := (1 + η_of_P * r)^2 - 1
    change (1 + η_of_P * r + (-(1 + η_of_P * r) + a))^2 = a_sqr
    ring_nf
    unfold a a_sqr
    rw [← q_h1]
    nth_rw 2 [add_comm]
    rw [← pow_mul, one_add_card_over_four_mul_two_eq_one_add_card_over_two q_h1 q_h3]
    unfold η_of_P
    nth_rw 2 [add_comm]
    rw [q_h1, a_pow_q_add_one_over_two_eq_a P.prop.2.1 q_h1 q_h3]

@[blueprint "lemma:X2_h2"]
lemma X2_h2
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let η := η P.val
  let r := r s
  let X2 := X2 s P q
  X2^2 + 2 * (1 + η * r) * X2 + 1 = 0 := by
    intro η r X2
    have h := X2_h1 q_h1 q_h3 P
    grind

@[blueprint "lemma:X2_h3"]
lemma X2_h3
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let P := ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3
  let X' := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  let X := X t s
  let X2 := X2 s P.val q
  (X2 - X) * (X2 - X') = 0 := by
    intro t1 t2 P X' X X2
    let η := η P.val
    let r := r s
    let P_of_ϕ_fulfills_ϕOverFProps := P_of_ϕ_fulfills_ϕOverFProps t s_h1 s_h2 q_h1 q_h2 q_h3
    calc
      (X2 - X) * (X2 - X') = X2^2 - (X + X') * X2 + X * X' := by grind
      _ = X2^2 + 2 * (1 + η * r) * X2 + 1 := by
        rw [X_comparison_implication t s_h1 s_h2 q_h1 q_h2 q_h3]
        change X2 ^ 2 - -2 * (1 + η * r) * X2 + X * X' = X2 ^ 2 + 2 * (1 + η * r) * X2 + 1
        rw [mul_add, mul_comm X _, X_comparison_implication2 t s_h1 q_h1 q_h2 q_h3]
        grind
      _ = 0 := X2_h2 q_h1 q_h3 ⟨P.val, P_of_ϕ_fulfills_ϕOverFProps⟩

@[blueprint "lemma:X2_h4"]
lemma X2_h4
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let P := ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3
  let X' := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  let X := X t s
  let X2 := X2 s P q
  X2 = X ∨ X2 = X' := by
    intro t1 t2 P X' X X2
    have h := X2_h3 t s_h1 s_h2 q_h1 q_h2 q_h3
    grind

@[blueprint "lemma:X2_ne_zero"]
lemma X2_ne_zero
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let X2 := X2 s P q
  X2 ≠ 0 := by
    intro X2
    have h := X2_h2 q_h1 q_h3 P
    let η := η P.val
    let r := r s
    change X2^2 + 2 * (1 + η * r) * X2 + 1 = 0 at h
    intro h'
    rw [h'] at h
    simp at h

@[blueprint "lemma:y_divisor_ne_zero_with_X"]
lemma y_divisor_ne_zero_with_X2_for_X
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let r := r s
  let X2 := X2 s P q
  r * X2 + (1 + X2)^2 ≠ 0 := by
    intro r X2 h1
    let η := η P.val
    have h2 := X2_h2 q_h1 q_h3 P
    change X2^2 + 2 * (1 + η * r) * X2 + 1 = 0 at h2
    let y := P.val.2
    have h3 : 2 * η = 1 := by
      have hne : r * X2 ≠ 0 := mul_ne_zero (r_ne_zero s_h1 q_h1 q_h2 q_h3) (X2_ne_zero q_h1 q_h3 P)
      rw [← div_left_inj' hne]
      grind
    have h4 : y - 1 = y + 1 := by
      unfold η Elligator1.η at h3
      grind
    have h5 : y - 1 ≠ y + 1 := by grind
    contradiction

@[blueprint "lemma:X2_ne_neg_one"]
lemma X2_ne_neg_one
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let X2 := X2 s P q
  X2 ≠ -1 := by
    intro X2 h1
    let η := η P.val
    let X2_equation := X2_h2 q_h1 q_h3 P
    let r := r s
    let P_prop := P.prop
    let y := P.val.2
    change X2^2 + 2 * (1 + η * r) * X2 + 1 = 0 at X2_equation
    rw [h1] at X2_equation
    have h2 : η = 0 := by
      ring_nf at X2_equation
      let r_ne_zero := r_ne_zero s_h1 q_h1 q_h2 q_h3
      rw [← div_left_inj' (two_ne_zero q_h1 q_h2 q_h3)] at X2_equation
      rw [← div_left_inj' r_ne_zero] at X2_equation
      ring_nf at X2_equation
      have h2_1 : -(η * r * 2⁻¹ * r⁻¹ * 2) = -(η * (r * r⁻¹) * (2 * 2⁻¹)) := by grind
      rw [h2_1] at X2_equation
      rw [mul_inv_cancel₀ r_ne_zero, mul_inv_cancel₀ (two_ne_zero q_h1 q_h2 q_h3)] at X2_equation
      grind
    have h3 : η ≠ 0 := by
      unfold η Elligator1.η
      have h3_1 : y - 1 ≠ 0 := by grind
      have h3_2 : 2 * (y + 1) ≠ 0 := by
        intro h3_2_1
        let y_add_one_ne_zero := P_prop.1
        unfold ϕOverFProp1 at y_add_one_ne_zero
        rw [← div_left_inj' (two_ne_zero q_h1 q_h2 q_h3)] at h3_2_1
        ring_nf at h3_2_1
        rw [inv_mul_cancel₀ (two_ne_zero q_h1 q_h2 q_h3)] at h3_2_1
        grind
      apply div_ne_zero h3_1 h3_2
    contradiction

@[blueprint "lemma:X2_add_one_ne_zero"]
lemma X2_add_one_ne_zero
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_ne_one : P.val.2 ≠ 1)
  :
  let X2 := X2 s P q
  X2 + 1 ≠ 0 := by grind [X2_ne_neg_one]

@[blueprint "lemma:y_with_X2"]
lemma y_with_X2
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let X2 := X2 s P.val q
  let r := r s
  let y := P.val.2
  y = (r * X2 - (1 + X2)^2) / (r * X2 + (1 + X2)^2) := by
    intro X2 r y
    let X2_equation := X2_h2 q_h1 q_h3 P
    let η := η P.val
    let y_add_one_ne_zero := P.prop.1
    let X2_ne_zero := X2_ne_zero q_h1 q_h3 P
    let two_ne_zero := two_ne_zero q_h1 q_h2 q_h3
    let r_ne_zero :=r_ne_zero s_h1 q_h1 q_h2 q_h3
    change X2^2 + 2 * (1 + η * r) * X2 + 1 = 0 at X2_equation
    have h1 : y = (1 + 2 * η) / (1 - 2 * η) := by
      have h1_1 : η = (y - 1) / (2 * (y + 1)) := by simp [η, Elligator1.η, y]
      have h1_2 : (2 * (y + 1)) ≠ 0 := mul_ne_zero two_ne_zero y_add_one_ne_zero
      grind
    have h2 : 2 * η = - ((1 + X2)^2) / (r * X2) := by
      have h2_1 : 1 + η * r = - (X2^2 + 1) / (2 * X2) := by
        have h2_1_1 : 2 * X2 ≠ 0 := mul_ne_zero two_ne_zero X2_ne_zero
        rw [← add_left_inj (-X2^2), ← add_left_inj (-1)] at X2_equation
        rw [← div_left_inj' h2_1_1] at X2_equation
        grind
      have h2_2 : 2 * η = -((1 + X2)^2) / (r * X2) := by
        have h2_2_1 : η = (-(X2^2 + 1) / (2 * X2) -1) / r := by grind
        have h2_2_2 : η = -(X2 + 1)^2 / (2 * r * X2) := by
          have h2_2_2_1 : (2 * X2) / (2 * X2) = 1 := by grind
          rw [← h2_2_2_1] at h2_2_1
          rw [h2_2_1]
          ring_nf
          grind
        rw [← mul_left_inj' two_ne_zero] at h2_2_2
        ring_nf
        grind
      grind
    have h3 : (1 + 2 * η) / (1 - 2 * η) = ((r * X2 - (1 + X2)^2)) / ((r * X2 + (1 + X2)^2)) := by
      have h3_1 : 1 = (r * X2) / (r * X2) := by grind
      rw [h2]
      nth_rw 1 [h3_1]
      nth_rw 2 [h3_1]
      rw [← add_div, ← sub_div, div_div]
      grind
    rw [← h3]
    exact h1

@[blueprint "lemma:y_with_X2_of_X2_eq_one"]
lemma y_with_X2_of_X2_eq_one
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let X2 := X2 s P.val q
  let r := r s
  let y := P.val.2
  X2 = 1 → y = (r - 4) / (r + 4) := by grind [y_with_X2]

@[blueprint "lemma:η_mul_r_eq_neg_two_of_X2_eq_one"]
lemma η_mul_r_eq_neg_two_of_X2_eq_one
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let η := η P
  let X2 := X2 s P q
  let r := r s
  X2 = 1 → η * r = -2 := by
    intro η  X2 r X2_h
    let h1 := X2_h2 q_h1 q_h3 P
    let two_ne_zero := two_ne_zero q_h1 q_h2 q_h3
    change X2^2 + 2 * (1 + η *r) * X2 + 1 = 0 at h1
    rw [X2_h, ← add_left_inj (-4), ← div_left_inj' two_ne_zero] at h1
    ring_nf at h1
    grind

@[blueprint "lemma:X2_observation1_of_X2_ne_one"]
lemma X2_observation1_of_X2_ne_one
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let X2 := X2 s P.val q
  let y := P.val.2
  let r := r s
  X2 ≠ 1 → (r * X2 + (1 + X2)^2)^2 * (1 - y^2) = 4 * r * X2 * (1 + X2)^2 := by
    intro X2 y r X2_h
    let y_with_X2 := y_with_X2 s_h1 q_h1 q_h2 q_h3 P y_eq_one
    let y_divisor_ne_zero_with_X2_for_X := y_divisor_ne_zero_with_X2_for_X s_h1 q_h1 q_h2 q_h3
    change y = (r * X2 - (1 + X2)^2) / (r * X2 + (1 + X2)^2) at y_with_X2
    have h1 : (r * X2 + (1 + X2)^2)^2 * (1 - y^2)
      = (r * X2 + (1 + X2)^2)^2 - (r * X2 - (1 + X2)^2)^2 := by
      rw [y_with_X2, div_pow, mul_sub, ← mul_div_assoc]
      nth_rw 3 [mul_comm]
      have h1_1 : (r * X2 + (1 + X2) ^ 2) ^ 2 ≠ 0 := pow_two_ne_zero (by simp_all; grind)
      rw [mul_div_assoc, div_self h1_1]
      ring_nf
    grind

@[blueprint "lemma:X2_observation2_of_X2_ne_one"]
lemma X2_observation2_of_X2_ne_one
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_eq_one : P.val.2 ≠ 1)
  :
  let X2 := X2 s P.val q
  let y := P.val.2
  let r := r s
  let d := d s;
  X2 ≠ 1 → (r * X2 + (1 + X2)^2)^2 * (1 - d * y^2)
    = ((2 * r) / (r - 2)) * (X2^4 + (r^2 - 2) * X2^2 + 1) := by
    intro X2 y r d X2_h
    let neg_d_eq_r_add_two_over_r_sub_two := neg_d_eq_r_add_two_over_r_sub_two s_h1 q_h1 q_h2 q_h3
    change -d = (r + 2) / (r - 2) at neg_d_eq_r_add_two_over_r_sub_two
    let y_divisor_ne_zero_with_X2_for_X := y_divisor_ne_zero_with_X2_for_X s_h1 q_h1 q_h2 q_h3
    let y_with_X2 := y_with_X2 s_h1 q_h1 q_h2 q_h3 P y_eq_one
    change y = (r * X2 - (1 + X2)^2) / (r * X2 + (1 + X2)^2) at y_with_X2
    have h1 : (r * X2 + (1 + X2)^2)^2 * (1 - d * y^2)
      = (r * X2 + (1 + X2)^2)^2 + (r + 2) / (r - 2) * ((r * X2 - (1 + X2)^2)^2) := by
      rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← mul_assoc, ← neg_eq_neg_one_mul]
      rw [neg_d_eq_r_add_two_over_r_sub_two, y_with_X2, div_pow, mul_add]
      nth_rw 3 [mul_comm]
      have h1_1 : (r * X2 + (1 + X2)^2)^2 ≠ 0 := pow_two_ne_zero (by simp_all; grind)
      rw [← mul_div_assoc, div_mul, mul_div_assoc, div_self h1_1]
      grind
    have h2 : (1 + X2)^2 = X2^2 + 2 * X2 + 1 := by grind
    rw [h1, h2]
    let A := r * X2 + (X2^2 + 2 * X2 + 1)
    let B := r * X2 - (X2^2 + 2 * X2 + 1)
    change A^2 + (r + 2) / (r - 2) * B^2 = 2 * r / (r - 2) * (X2^4 + (r^2 - 2) * X2^2 + 1)
    have h3 : A^2 = X2^ 4 + 2 * (r + 2) * X2^3 + ((r + 2)^2 + 2) * X2^2 + 2 * (r + 2) * X2 + 1 := by
      grind
    have h4 : B^2 = X2^ 4 - 2 * (r - 2) * X2^3 + ((r - 2)^2 + 2) * X2^2 - 2 * (r - 2) * X2 + 1 := by
      grind
    rw [h3, h4]
    let r_sub_two_ne_zero := r_sub_two_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3
    have X_pow_four_term : X2^4 + (r + 2) / (r - 2) * X2^4 = X2^4 * (2 * r) / (r - 2) := by grind
    have X_pow_three_term : X2^3 * 2 * (r + 2) + (r + 2) / (r - 2) * (-2 * (r - 2) * X2^3) = 0 := by
      grind
    have X_pow_two_term : X2^2 * (r^2+ 4 * r + 6) + (r + 2) / (r - 2) * (r^2 - 4 * r + 6) * X2^2
      = X2^2 * (2 * r * (r^2 - 2) / (r - 2)) := by
      nth_rw 3 [mul_comm]
      rw [← mul_add (X2^2)]
      have h5 : (r^2 + 4 * r + 6 + (r + 2) / (r - 2) * (r^2 - 4 * r + 6))
        = ((r^2 + 4 * r + 6) * (r - 2) + (r + 2) * (r^2 - 4 * r + 6)) / (r - 2) := by grind
      rw [h5]
      have h6 : (r^2 + 4 * r + 6) * (r - 2) = r^3 + 2 * r^2 - 2 * r - 12 := by grind
      have h7 : (r + 2) * (r^2 - 4 * r + 6) = r^3 - 2 * r^2 - 2 * r + 12 := by grind
      rw [h6, h7]
      have h8 : r^3 + 2 * r^2 - 2 * r - 12 + (r^3 - 2 * r^2 - 2 * r + 12) = 2 * r^3 - 4 * r := by
        grind
      grind
    have X_pow_one_term : 2 * (r + 2) * X2 - 2 * (r + 2) * X2 = 0 := by grind
    have const_term : 1 + (r + 2) / (r - 2) = (2 * r) / (r - 2) := by grind
    grind

@[blueprint "lemma:one_sub_d_mul_y_pow_two_ne_zero"]
lemma one_sub_d_mul_y_pow_two_ne_zero
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  :
  let y := P.val.2
  let d := d s;
  1 - d * y^2 ≠ 0 := by
    intro y d h1
    let d_ne_zero := d_ne_zero s_h2 q_h1 q_h3
    rw [← add_left_inj (d * y^2)] at h1
    ring_nf at h1
    rw [mul_comm, ← div_left_inj' d_ne_zero, mul_div_assoc, div_self d_ne_zero, mul_one] at h1
    change 1 / d = y^2 at h1
    have h2 : IsSquare (1 / d) := by
      unfold IsSquare
      use y
      grind
    let h3 := one_over_d_nonsquare s_h2 q_h1 q_h3
    change ¬IsSquare (1 / d) at h3
    contradiction

@[blueprint "lemma:x_pow_two_of_X2_ne_one_eq1"]
lemma x_pow_two_of_X2_ne_one_eq1
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
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
      one_sub_d_mul_y_pow_two_ne_zero s_h2 q_h1 q_h3 ⟨P.val, P_props⟩
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

@[blueprint "lemma:x_pow_two_of_X2_ne_one_eq2_of_X2_ne_one"]
lemma x_pow_two_of_X2_ne_one_eq2_of_X2_ne_one
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (y_eq_one : P.val.2 ≠ 1)
  :
  let x := P.val.1
  let X := X2 s P q
  let r := r s
  X ≠ 1 → x^2 = (2 * (r -2) * X^2 * (1 + X)^2) / (X^5 + (r^2 - 2) * X^3 + X) := by
    intro x X r Xh
    let y := P.val.2
    let d := d s;
    let x_pow_two_of_X2_ne_one_eq1 := x_pow_two_of_X2_ne_one_eq1 s_h2 q_h1 q_h3 P P_props
    change x^2 = (1 - y^2) / (1 - d*y^2) at x_pow_two_of_X2_ne_one_eq1
    let y_with_X2 := y_with_X2 s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_eq_one
    change y = (r * X - (1 + X)^2) / (r * X + (1 + X)^2) at y_with_X2
    let y_divisor_ne_zero_with_X2_for_X :=
      y_divisor_ne_zero_with_X2_for_X s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩
    change r * X + (1 + X)^2 ≠ 0 at y_divisor_ne_zero_with_X2_for_X
    have h1 : (r * X + (1 + X)^2)^2 ≠ 0 := by grind
    have h2 : 1 = ((r * X + (1 + X)^2)^2) / ((r * X + (1 + X)^2)^2) := by grind
    let X2_observation1_of_X2_ne_one :=
      X2_observation1_of_X2_ne_one s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_eq_one
    change X ≠ 1 →
      (r * X + (1 + X)^2)^2 * (1 - y^2) = 4 * r * X * (1 + X)^2 at X2_observation1_of_X2_ne_one
    have h3 : (r * X + (1 + X)^2)^2 * (1 - y^2) = 4 * r * X * (1 + X)^2 := by grind
    let X2_observation2_of_X2_ne_one :=
      X2_observation2_of_X2_ne_one s_h1 s_h2 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_eq_one
    change X ≠ 1 → (r * X + (1 + X)^2)^2 * (1 - d * y^2)
      = ((2 * r) / (r - 2)) * (X^4 + (r^2 - 2) * X^2 + 1) at X2_observation2_of_X2_ne_one
    have h4 : (r * X + (1 + X)^2)^2 * (1 - d * y^2)
      = ((2 * r) / (r - 2)) * (X^4 + (r^2 - 2) * X^2 + 1) := by grind
    let X_ne_zero := X2_ne_zero q_h1 q_h3 ⟨P.val, P_props⟩
    change X ≠ 0 at X_ne_zero
    calc
      x^2 = (1 - y^2) / (1 - d*y^2) := by grind
      _ = (4 * r * X * (1 + X)^2) / ((2 * r) / (r - 2) * (X^4 + (r^2 - 2) * X^2 + 1)) := by
        rw [← one_mul (1 - y^2), ← one_mul (1 - d * y^2)]
        nth_rw 1 [h2]
        rw [mul_div_assoc, div_mul_div_comm]
        grind
      _ = (2 * (r - 2) * X * (1 + X)^2) / (X^4 + (r^2 - 2) * X^2 + 1) := by
        let r_sub_two_ne_zero := r_sub_two_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3
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
            let two_ne_zero := two_ne_zero q_h1 q_h2 q_h3
            let r_ne_zero := (r_ne_zero s_h1 q_h1 q_h2 q_h3)
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
@[blueprint "def:Y'"]
noncomputable def Y'
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  : F :=
  let x := P.val.1
  let c := c s
  let X := X2 s P q
  -- This is just `def x` with the denominator `Y` replaced by `x` of P
  (c - 1) * s * X * (1 + X) / x

@[blueprint "lemma:Y'_pow_two_eq_of_X2_ne_one"]
lemma Y'_pow_two_eq_of_X2_ne_one
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (y_eq_one : P.val.2 ≠ 1)
  :
  let X := X2 s P q
  let r := r s
  let Y := Y' s_h2 q_h1 q_h3 P
  -- This is just `def x` with the denominator `Y` replaced by `x` of P
  X ≠ 1 → Y^2 = X^5 + (r^2 - 2) * X^3 + X := by
    intro X r Y Xh
    let c := c s
    let x := P.val.1
    let h := x_pow_two_of_X2_ne_one_eq2_of_X2_ne_one s_h1 s_h2 q_h1 q_h2 q_h3 P P_props y_eq_one
    let two_ne_zero := two_ne_zero q_h1 q_h2 q_h3
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
        field_simp [s_h1]
        ring_nf
      rw [h]
    _ = X^5 + (r^2 - 2) * X^3 + X := by
      have h'' : (2 * (r - 2) * X^2 * (1 + X)^2) ≠ 0 := by
        let X2_add_one_ne_zero := X2_add_one_ne_zero s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_eq_one
        let r_sub_two_ne_zero := r_sub_two_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3
        let X2_ne_zero := X2_ne_zero q_h1 q_h3 ⟨P.val, P_props⟩
        rw [add_comm]
        apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero two_ne_zero r_sub_two_ne_zero
          · apply pow_two_ne_zero X2_ne_zero
        · apply pow_two_ne_zero X2_add_one_ne_zero
      rw [h']
      nth_rw 1 [← div_one (2 * (r - 2) * X^2 * (1 + X)^2)]
      rw [div_div_div_comm, div_self h'']
      grind

@[blueprint "lemma:X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one"]
lemma X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {P : F × F // ϕOverFProps s P})
  (y_ne_one : P.val.2 ≠ 1)
  :
  let X2 := X2 s P q
  X2 ≠ 1 → X2 ≠ 1 ∧ X2 ≠ -1 := by grind [X2_ne_neg_one]

end Elligator.Elligator1
