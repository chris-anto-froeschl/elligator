/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.X2Properties
public import Elligator.Elligator1.zProperties

/-!
# u2 Properties

In this file we introduce some generally helpful lemmas for `u2` as introduced in
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

@[blueprint "lemma:u2_eq_zero"]
lemma u2_eq_zero
  (t : { t : F // t = 1 ∨ t = -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).val
  let u2 := u2 s P q
  u2 = 0 := by grind [z_eq_zero, u2]

@[blueprint "lemma:u2_eq_u"]
lemma u2_eq_u
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (X_h :
    let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).val
    let X := X t s
    let X2 := X2 s P q
    X2 = X)
  :
  let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).val
  let u := u t
  let u2 := u2 s P q
  u2 = u := by
    intro P u u2
    let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let X := X t s
    let X2 := X2 s P q
    let c := c s
    let x := x t s q
    let Y := Y t s q
    let z := z s P q
    let v := v t s;
    let χ_of_v := χ v
    let χ_of_Y := χ Y
    unfold u2 Elligator1.u2
    rw [X_h]
    change z * X = u
    have h1 : (c - 1) * s * X2 * (1 + X2) = x * Y := by
      unfold X2
      rw [X_h]
      rw [← div_left_inj' (Y_ne_zero s_h1 q_h1 q_h2 q_h3 t)]
      change x = x * Y / Y
      rw [mul_div_assoc, div_self (Y_ne_zero s_h1 q_h1 q_h2 q_h3 t)]
      ring_nf
    have h2 : z = χ_of_Y * χ (X^2 + 1 / c^2) := by
      calc
        z = χ (x^2 * Y * (X^2 + 1 / c^2)) := by
          unfold z Elligator1.z
          change χ ((c - 1) * s * X2 * (1 + X2) * P.1 * (X2^2 + 1 / c^2))
            = χ (x^2 * Y * (X^2 + 1 / c^2))
          unfold P ϕ
          simp only [h1]
          rw [dif_pos t.prop]
          change χ (x * Y * x * (X2^2 + 1 / c^2)) = χ (x^2 * Y * (X^2 + 1 / c^2))
          unfold X2 X
          rw [X_h]
          ring_nf
        _ = χ_of_Y * χ (X^2 + 1 / c^2) := by
          rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
          rw [χ_a_eq_one
            (pow_two_ne_zero (x_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 t)) (IsSquare.sq x) q_h1 q_h3]
          unfold χ_of_Y
          ring_nf
    have h3 : χ (u^2 + 1 / c^2) = χ (X^2 + 1 / c^2) := by
      unfold X Elligator1.X
      rw [mul_pow]
      nth_rw 3 [pow_two]
      rw [← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
      rw [← pow_two, χ_a_eq_one
        (pow_two_ne_zero (v_ne_zero s_h1 q_h1 q_h2 q_h3 t)) (IsSquare.sq v) q_h1 q_h3]
      unfold u
      simp_all
    have h4 : χ_of_Y = χ_of_v * χ (X^2 + 1 / c^2) := by
      rw [← h3]
      unfold χ_of_Y Y Elligator1.Y
      let χ_sum := χ (u^2 + 1 / c^2)
      change χ ((χ_of_v * v)^((q + 1) / 4) * χ_of_v * χ_sum) = χ_of_v * χ_sum
      rw [mul_assoc, χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
      rw [χ_a_eq_one
        (χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero t s_h1 q_h1 q_h2 q_h3)
        (χ_IsSquare_h1 t s_h1 q_h1 q_h2 q_h3) q_h1 q_h3]
      rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
      rw [χ_of_χ_of_a_eq_χ_of_a q_h1 q_h2 q_h3, χ_of_χ_of_a_eq_χ_of_a q_h1 q_h2 q_h3]
      unfold χ_of_v χ_sum
      simp_all
    have h5 : z = χ_of_v := by
      rw [h2, h4, mul_assoc, ← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, ← pow_two]
      rw [χ_a_eq_one
        (pow_two_ne_zero (X_pow_two_add_one_over_c_pow_two_ne_zero s_h1 q_h1 q_h2 q_h3 t))
        (IsSquare.sq (X^2 + 1 / c^2)) q_h1 q_h3]
      simp
    rw [h5]
    unfold X Elligator1.X
    change χ_of_v * (χ_of_v * u) = u
    rw [← mul_assoc, ← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, ← pow_two]
    have h6 : IsSquare (v^2) := IsSquare.sq v
    rw [χ_a_eq_one (pow_two_ne_zero (v_ne_zero s_h1 q_h1 q_h2 q_h3 t)) h6 q_h1 q_h3]
    simp

@[blueprint "lemma:u2_eq_u'"]
lemma u2_eq_u'
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (X_h :
    let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).val
    let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let X2 := X2 s P q
    X2 = X')
  :
  let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).val
  let u' := u ⟨-t.val, t_h⟩
  let u2 := u2 s P q
  u2 = u' := by
    intro t_h P u' u2
    let X' := X ⟨-t.val, t_h⟩ s
    let X := X t s
    let X2 := X2 s P q
    let c := c s
    let x' := x ⟨-t.val, t_h⟩ s q
    let x := x t s q
    let Y' := Y ⟨-t.val, t_h⟩ s q
    let Y := Y t s q
    let z := z s P q
    let v' := v ⟨-t.val, t_h⟩ s
    let v := v t s;
    let χ_of_v := χ v
    let χ_of_v' := χ v'
    let χ_of_Y := χ Y
    let χ_of_Y' := χ Y'
    unfold u2 Elligator1.u2
    rw [X_h]
    change z * X' = u'
    have h1 : (c - 1) * s * X2 * (1 + X2) = x' * Y' := by
      unfold X2
      rw [X_h]
      rw [← div_left_inj' (Y_ne_zero s_h1 q_h1 q_h2 q_h3 ⟨-t.val, t_h⟩)]
      change x' = x' * Y' / Y'
      rw [mul_div_assoc, div_self (Y_ne_zero s_h1 q_h1 q_h2 q_h3 ⟨-t.val, t_h⟩)]
      ring_nf
    have h2 : z = χ_of_Y' * (χ (X'^2 + 1 / c^2)) := by
      calc
        z = (χ (x'^2 * Y' * (X'^2 + 1 / c^2))) := by
          unfold z Elligator1.z
          change χ ((c - 1) * s * X2 * (1 + X2) * P.1 * (X2^2 + 1 / c^2))
            = χ (x'^2 * Y' * (X'^2 + 1 / c^2))
          unfold P ϕ
          simp only [h1]
          rw [dif_pos t.prop]
          change χ (x' * Y' * x * (X2^2 + 1 / c^2)) = χ (x'^2 * Y' * (X'^2 + 1 / c^2))
          unfold X2 X' x' x
          rw [x_comparison t s_h1 q_h1 q_h2 q_h3]
          rw [X_h]
          ring_nf
        _ = χ_of_Y' * χ (X'^2 + 1 / c^2) := by
          rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
          rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
          rw [χ_a_eq_one (pow_two_ne_zero (x_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 ⟨-t, t_h⟩))
            (IsSquare.sq x') q_h1 q_h3]
          unfold χ_of_Y'
          ring_nf
    have h3 : (χ (u'^2 + 1 / c^2)) = (χ (X'^2 + 1 / c^2)) := by
      unfold X' Elligator1.X
      rw [mul_pow]
      nth_rw 3 [pow_two]
      rw [← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
      rw [← pow_two, χ_a_eq_one (pow_two_ne_zero (v_ne_zero s_h1 q_h1 q_h2 q_h3 ⟨-t, t_h⟩))
        (IsSquare.sq v') q_h1 q_h3]
      unfold u'
      simp_all
    have h4 : χ_of_Y' = χ_of_v' * (χ (X'^2 + 1 / c^2)) := by
      rw [← h3]
      unfold χ_of_Y' Y' Elligator1.Y
      let χ_sum := χ (u'^2 + 1 / c^2);
      change (χ ((χ_of_v' * v')^((q + 1) / 4) * χ_of_v' * χ_sum)) = χ_of_v' * χ_sum
      rw [mul_assoc, χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
      rw [χ_a_eq_one
        (χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero ⟨-t.val, t_h⟩ s_h1 q_h1 q_h2 q_h3)
        (χ_IsSquare_h1 ⟨-t.val, t_h⟩ s_h1 q_h1 q_h2 q_h3) q_h1 q_h3]
      rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, χ_of_χ_of_a_eq_χ_of_a q_h1 q_h2 q_h3]
      rw [χ_of_χ_of_a_eq_χ_of_a q_h1 q_h2 q_h3]
      unfold χ_of_v' χ_sum
      simp_all
    have h5 : z = χ_of_v' := by
      rw [h2, h4, mul_assoc]
      rw [← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, ← pow_two]
      rw [χ_a_eq_one (pow_two_ne_zero
          (X_pow_two_add_one_over_c_pow_two_ne_zero s_h1 q_h1 q_h2 q_h3 ⟨-t.val, t_h⟩))
        (IsSquare.sq (X'^2 + 1 / c^2)) q_h1 q_h3]
      simp
    rw [h5]
    unfold X' Elligator1.X
    change χ_of_v' * (χ_of_v' * u' ) = u'
    rw [← mul_assoc, ← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, ← pow_two]
    have h6 : IsSquare (v'^2) := IsSquare.sq v'
    rw [χ_a_eq_one (pow_two_ne_zero (v_ne_zero s_h1 q_h1 q_h2 q_h3 ⟨-t.val, t_h⟩)) h6 q_h1 q_h3]
    simp

@[blueprint "lemma:u2_h1"]
lemma u2_h1
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3
  have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let u' := u ⟨-t.val, t_h⟩
  let u := u t
  let u2 := u2 s P.val q
  u2 = u ∨ u2 = u' := by
    intro P t_h u' u u2
    rcases (X2_h4 t s_h1 s_h2 q_h1 q_h2 q_h3) with h | h
    · left
      exact u2_eq_u t s_h1 s_h2 q_h1 q_h2 q_h3 h
    · right
      exact u2_eq_u' t s_h1 s_h2 q_h1 q_h2 q_h3 h

/-- The key step: rewriting `1 + u2(ϕ(t))` in the main case (t ≠ ±1) to show it is ne_zero,
    using `u2_h1` which gives `u2 = u(t)` or `u2 = u(-t)`. -/
@[blueprint "lemma:one_add_u"]
lemma one_add_u2_ne_zero_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s_h1 : (s : F) ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).1
  let u2 := u2 s P q
  1 + u2 ≠ 0 := by
    intro P u2
    unfold u2
    obtain h|h := u2_h1 t s_h1 s_h2 q_h1 q_h2 q_h3
    · rw [h]
      exact one_add_u_ne_zero t q_h1 q_h2 q_h3
    · rw [h]
      let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
      exact one_add_u_ne_zero ⟨-t.val, t_h⟩ q_h1 q_h2 q_h3

@[blueprint "lemma:one_add_u2_ne_zero_base_case"]
lemma one_add_u2_ne_zero_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).1
  let u2 := u2 s P q
  1 + u2 ≠ 0 := by
    intro P u2
    unfold u2
    rw [u2_eq_zero, add_zero]
    exact FiniteFieldBasic.one_ne_zero

@[blueprint "lemma:one_add_u2_ne_zero"]
lemma one_add_u2_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ ϕOverF s_h1 s_h2 q_h1 q_h2 q_h3})
  :
  let u2 := u2 s P q
  (1 + u2) ≠ 0 := by
    intro u2
    let P_prop := P.prop
    unfold ϕOverF at P_prop
    obtain ⟨t, ht⟩ := P_prop
    by_cases h : t ≠ 1 ∧ t ≠ -1
    · let h2 := one_add_u2_ne_zero_main_case ⟨t, h⟩ s_h1 s_h2 q_h1 q_h2 q_h3
      grind
    · have h2 : t = 1 ∨ t = -1 := by grind
      have h3 := one_add_u2_ne_zero_base_case ⟨t, h2⟩ s_h1 s_h2 q_h1 q_h2 q_h3
      grind

/-- `u'` is the `u` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
@[blueprint "def:u'"]
noncomputable def u'
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  : F :=
  let z := z' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  z * X

@[blueprint "lemma:u'_pow_two_eq_X_pow_two"]
lemma u'_pow_two_eq_X_pow_two
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
  let u := u' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  u^2 = X^2 := by grind [u, u', z', z'_eq_one_or_z'_eq_neg_one ]

@[blueprint "lemma:u'_eq_X2_or_u'_eq_neg_X2"]
lemma u'_eq_X2_or_u'_eq_neg_X2
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
  let u := u' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  u = X ∨ u = -X := by grind [u, u', z'_eq_one_or_z'_eq_neg_one]

@[blueprint "lemma:u'_ne_neg_one"]
lemma u'_ne_neg_one
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
  let u := u' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  X ≠ 1 → u ≠ -1 := by
    intro u X h1
    let z'_eq_one_or_z'_eq_neg_one :=
      z'_eq_one_or_z'_eq_neg_one s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let z := z' s_h2 q_h1 q_h3 P
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one :=
      X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_ne_one
    unfold u u'
    grind

@[blueprint "lemma:one_add_u'_ne_zero"]
lemma one_add_u'_ne_zero
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
  let u := u' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  X ≠ 1 → 1 + u ≠ 0 := by
    intro u X h1
    let z'_eq_one_or_z'_eq_neg_one :=
      z'_eq_one_or_z'_eq_neg_one s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let z := z' s_h2 q_h1 q_h3 P
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one :=
      X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_ne_one
    unfold u u'
    grind

@[blueprint "lemma:u'_ne_zero"]
lemma u'_ne_zero
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
  let u := u' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  X ≠ 1 → u ≠ 0 := by
    intro u X h1
    let z'_eq_one_or_z'_eq_neg_one :=
      z'_eq_one_or_z'_eq_neg_one s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let z := z' s_h2 q_h1 q_h3 P
    let z_ne_zero := z'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let X2_ne_zero := X2_ne_zero q_h1 q_h3 ⟨P.val, P_props⟩
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one :=
      X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_ne_one
    unfold u u'
    grind

/-- `v'` is the `v` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
@[blueprint "def:v'"]
noncomputable def v'
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  : F :=
  let u := u' s_h2 q_h1 q_h3 P
  let r := r s
  -- Note: this is just the definition of v as in theorem 1
  u^5 + (r^2 - 2) * u^3 + u

@[blueprint "lemma:v'_eq_z'_mul_Y'_pow_two"]
lemma v'_eq_z'_mul_Y'_pow_two
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (y_ne_one : P.val.2 ≠ 1)
  :
  let z := z' s_h2 q_h1 q_h3 P
  let Y := Y' s_h2 q_h1 q_h3 P
  let v := v' s_h2 q_h1 q_h3 P
  let X := X2 s P q
  X ≠ 1 → v = z * Y^2 := by
    intro z Y v X h1
    let r := r s
    let c := c s
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one :=
      X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_ne_one
    let Y'_pow_two_eq_of_X2_ne_one :=
      Y'_pow_two_eq_of_X2_ne_one s_h1 s_h2 q_h1 q_h2 q_h3 P P_props y_ne_one
    let z_pow_three_eq_z := χ_of_a_pow_n_eq_χ_a (Y * (X^2 + 1 / c^2)) ⟨3, by grind⟩ q_h1 q_h2 q_h3
    change z^3 = z at z_pow_three_eq_z
    let z_pow_five_eq_z := χ_of_a_pow_n_eq_χ_a (Y * (X^2 + 1 / c^2)) ⟨5, by grind⟩ q_h1 q_h2 q_h3
    change z^5 = z at z_pow_five_eq_z
    let x := P.val.1
    have h2 : v = z * (X^5 + (r^2 - 2) * X^3 + X) := by
      change (z * X)^5 + (r^2 - 2) * (z * X)^3 + (z * X) = z * (X^5 + (r^2 - 2) * X^3 + X)
      repeat rw [mul_pow]
      rw [z_pow_three_eq_z, z_pow_five_eq_z]
      grind
    grind

@[blueprint "lemma:v'_ne_zero"]
lemma v'_ne_zero
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
  let X := X2 s P q
  let v := v' s_h2 q_h1 q_h3 P
  X ≠ 1 → v ≠ 0 := by
    intro X v h1
    let v'_eq_z'_mul_Y'_pow_two :=
      v'_eq_z'_mul_Y'_pow_two s_h1 s_h2 q_h1 q_h2 q_h3 P P_props y_ne_one
    let z := z' s_h2 q_h1 q_h3 P
    let Y := Y' s_h2 q_h1 q_h3 P
    have h2 : v = z * Y^2 := by grind
    rw [h2]
    let h3 := Y'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let z_ne_zero := z'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    grind

@[blueprint "lemma:χ_of_v'_eq_χ_of_z'"]
lemma χ_of_v'_eq_χ_of_z'
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
  let X := X2 s P q
  let z := z' s_h2 q_h1 q_h3 P
  let v := v' s_h2 q_h1 q_h3 P
  let χ_of_v := χ v
  let χ_of_z := χ z
  X ≠ 1 → χ_of_v = χ_of_z := by
    intro X z v χ_of_v χ_of_z h
    let Y := Y' s_h2 q_h1 q_h3 P
    let v'_eq_z'_mul_Y'_pow_two :=
      v'_eq_z'_mul_Y'_pow_two s_h1 s_h2 q_h1 q_h2 q_h3 P P_props y_ne_one
    unfold χ_of_v v
    rw [v'_eq_z'_mul_Y'_pow_two h]
    let h' := Y'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    rw [χ_of_a_eq_χ_a_mul_b_pow_two h' q_h1 q_h3]

@[blueprint "lemma:χ_of_z'_eq_z'"]
lemma χ_of_z'_eq_z'
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  :
  let X := X2 s P q
  let z := z' s_h2 q_h1 q_h3 P
  let χ_of_z := χ z
  X ≠ 1 → χ_of_z = z := by
    intro X z χ_of_z h1
    exact χ_of_χ_of_a_eq_χ_of_a q_h1 q_h2 q_h3

@[blueprint "lemma:χ_of_v'_eq_z'"]
lemma χ_of_v'_eq_z'
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
  let X := X2 s P q
  let v := v' s_h2 q_h1 q_h3 P
  let z := z' s_h2 q_h1 q_h3 P
  let χ_of_v := χ v
  X ≠ 1 → χ_of_v = z := by grind [χ_of_v'_eq_χ_of_z', χ_of_z'_eq_z']

@[blueprint "lemma:X'_eq_χ_of_v'_mul_u'"]
lemma X'_eq_χ_of_v'_mul_u'
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
  let X := X2 s P q
  let v := v' s_h2 q_h1 q_h3 P
  let u := u' s_h2 q_h1 q_h3 P
  let χ_of_v := χ v
  X ≠ 1 → X = χ_of_v * u := by
    intro X v u χ_of_v h1
    let χ_of_v'_eq_z' := χ_of_v'_eq_z' s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    unfold χ_of_v v
    rw [χ_of_v'_eq_z' h1]
    let z := z' s_h2 q_h1 q_h3 P
    let z_ne_zero := z'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    rw [mul_comm, ← div_left_inj' z_ne_zero]
    rw [mul_div_assoc, div_self z_ne_zero]
    change X / z = z * X * 1
    let z'_argument_ne_zero :=
      z'_argument_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let Y := Y' s_h2 q_h1 q_h3 P
    let c := c s
    let a := (Y * (X^2 + 1 / c^2))
    nth_rw 1 [← mul_one X]
    unfold z z'
    rw [mul_div_assoc, ← one_over_χ_of_a_eq_χ_a q_h1 q_h2 q_h3]
    grind

@[blueprint "lemma:Y'_pow_two_eq_χ_of_v'_mul_v'"]
lemma Y'_pow_two_eq_χ_of_v'_mul_v'
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
  let X := X2 s P q
  let Y := Y' s_h2 q_h1 q_h3 P
  let v := v' s_h2 q_h1 q_h3 P
  let χ_of_v := χ v
  X ≠ 1 → Y^2 = χ_of_v * v := by
    intro X Y v χ_of_v h1
    let v'_eq_z'_mul_Y'_pow_two :=
      v'_eq_z'_mul_Y'_pow_two s_h1 s_h2 q_h1 q_h2 q_h3 P P_props y_ne_one
    let z :=z' s_h2 q_h1 q_h3 P
    have h2 : v = z * Y^2 := by grind
    let z_ne_zero := z'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    rw [mul_comm, ← div_left_inj' z_ne_zero] at h2
    rw [mul_div_assoc, div_self z_ne_zero, mul_one] at h2
    change v / z = Y^2 at h2
    let z'_argument_ne_zero :=
      z'_argument_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let c := c s
    let u := u' s_h2 q_h1 q_h3 P
    let r := r s
    let a := u^5 + (r^2 - 2) * u^3 + u
    rw [← h2, mul_comm]
    unfold χ_of_v v v'
    rw [one_over_χ_of_a_eq_χ_a q_h1 q_h2 q_h3]
    change v / z = v * (1 / χ_of_v)
    let χ_of_v'_eq_z' := χ_of_v'_eq_z' s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    unfold χ_of_v v
    rw [χ_of_v'_eq_z' h1]
    grind

@[blueprint "lemma:χ_of_v'_eq_z'_unfold_of_X'_ne_one"]
lemma χ_of_v'_eq_z'_unfold_of_X'_ne_one
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
  let X := X2 s P q
  let Y := Y' s_h2 q_h1 q_h3 P
  let v := v' s_h2 q_h1 q_h3 P
  let χ_of_v := χ v
  let c := c s
  let term := Y * (X^2 + 1 / c^2)
  let χ_erm := χ term
  X ≠ 1 → χ_of_v = χ_erm := by
    intro X Y v χ_of_v c term χ_erm h1
    let χ_of_v'_eq_z' := χ_of_v'_eq_z' s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let X2_ne_zero := X2_ne_zero q_h1 q_h3 ⟨P.val, P_props⟩
    change X ≠ 0 at X2_ne_zero
    unfold χ_of_v χ_erm term
    rw [χ_of_v'_eq_z' h1]
    rfl

@[blueprint "lemma:χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two"]
lemma χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two
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
  let X := X2 s P q
  let Y := Y' s_h2 q_h1 q_h3 P
  let v := v' s_h2 q_h1 q_h3 P
  let u := u' s_h2 q_h1 q_h3 P
  let c := c s
  X ≠ 1 → (χ v) = χ (Y * (u^2 + 1 / c^2)) := by
    grind [χ_of_v'_eq_z'_unfold_of_X'_ne_one, u'_pow_two_eq_X_pow_two]

@[blueprint "lemma:u'_pow_two_add_one_over_c_pow_two_ne_zero"]
lemma u'_pow_two_add_one_over_c_pow_two_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  :
  let u := u' s_h2 q_h1 q_h3 P
  let c := c s
  u^2 + 1 / c^2 ≠ 0 := by
    intro u c h
    have h' : -1 = (u * c)^2 := by grind [c_pow_two_ne_zero ]
    have h'' : IsSquare (-1 : F) := by
      rw [h', pow_two]
      apply IsSquare.mul_self (u * c)
    have h''' : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff, q_h1] at h''
      exact h''
    contradiction

@[blueprint "lemma:Y'_observation1"]
lemma Y'_observation1
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
  let X := X2 s P q
  let Y := Y' s_h2 q_h1 q_h3 P
  let v := v' s_h2 q_h1 q_h3 P
  let u := u' s_h2 q_h1 q_h3 P
  let c := c s
  X ≠ 1 → (χ Y) = (χ v) * χ (u^2 + 1 / c^2)  := by
    intro X Y v u c h1
    let χ_of_v'_eq_z'_unfold_of_X'_ne_one :=
      χ_of_v'_eq_z'_unfold_of_X'_ne_one s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one h1
    let χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two :=
      χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two
        s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    let term1 := (u^2 + 1 / c^2)
    let term2 := Y * term1
    let χ_term1 := χ term1
    let χ_term2 := χ term2
    have h2 : (χ v) * χ (u^2 + 1 / c^2) = χ_term2 * χ (u^2 + 1 / c^2) := by grind
    have h3 : (χ v) * χ (u^2 + 1 / c^2) = (χ Y) * χ_term1 * χ (u^2 + 1 / c^2) := by
      grind [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
    rw [h3]
    have h4 : χ_term1 * χ (u^2 + 1 / c^2) = 1 := by
      rw [← pow_two]
      let term1_ne_zero := u'_pow_two_add_one_over_c_pow_two_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P
      rw [χ_of_a_even_pow_n_eq_one term1_ne_zero ⟨2, even_two⟩ q_h1 q_h3]
    grind

@[blueprint "lemma:Y'_observation2"]
lemma Y'_observation2
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
  let X := X2 s P q
  let Y := Y' s_h2 q_h1 q_h3 P
  let v := v' s_h2 q_h1 q_h3 P
  let u := u' s_h2 q_h1 q_h3 P
  let c := c s
  X ≠ 1 → Y = ((χ v) * v)^((q + 1) / 4) * (χ v) * χ (u^2 + 1 / c^2) := by
    intro X Y v u c h1
    let χ_of_v'_eq_z'_unfold_of_X'_ne_one :=
      χ_of_v'_eq_z'_unfold_of_X'_ne_one s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one h1
    let χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two :=
      χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two
        s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one h1
    let Y'_observation1 :=
      Y'_observation1 s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one h1
    change (χ Y) = (χ v) * χ (u^2 + 1 / c^2) at Y'_observation1
    let Y'_pow_two_eq_χ_of_v'_mul_v' :=
      Y'_pow_two_eq_χ_of_v'_mul_v' s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one h1
    rw [← Y'_pow_two_eq_χ_of_v'_mul_v', mul_assoc, ← Y'_observation1]
    rw [← pow_mul, add_comm]
    change Y = Y^(2 * ((1 + q) / 4)) * (χ Y)
    rw [← q_h1]
    nth_rw 2 [mul_comm]
    rw [one_add_card_over_four_mul_two_eq_one_add_card_over_two q_h1 q_h3]
    rw [q_h1, add_comm, a_pow_q_add_one_over_two_eq_χ_of_a_mul_a q_h1 q_h3]
    rw [mul_comm, ← mul_assoc]
    rw [← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, ← pow_two]
    let Y'_ne_zero := Y'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    rw [χ_of_a_pow_two_eq_one Y'_ne_zero q_h1 q_h3]
    grind

end Elligator.Elligator1
