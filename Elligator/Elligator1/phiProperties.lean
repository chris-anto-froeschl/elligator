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
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.MapProperties
public import Elligator.Elligator1.t2Properties

@[expose] public section

/-!
# ϕ Properties

In this file we introduce some generally helpful lemmas for `ϕ`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

-- TODO some defs/lemma are probably better placed in MapProperties.lean
section phiProperties

variable {F : Type*} [Field F] [Fintype F]

lemma x_y_eq_zero_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_eq_zero : point.val.1 = 0)
  :
  point.val = ((0 : F), (1 : F)) := by
    let x := point.val.1
    let y := point.val.2
    have h1 : y + 1 ≠ 0 := by
      unfold ϕ_over_F_props ϕ_over_F_prop1 at point_props
      exact point_props.1
    have h2 : point.val = ((0 : F), (1 : F)) ∨ point.val = ((0 : F), (-1 : F)) := by
      exact x_y_eq_zero_sign_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point x_eq_zero
    change (x, y) = (0, 1)
    rcases h2 with h3 | h3
    · exact h3
    · change (x, y) = (0, -1) at h3
      have h4 := Prod.mk.inj h3
      have h5 : y + 1 = 0 := by
        rw [← add_left_inj (-1)]
        simp
        exact h4.right
      contradiction

lemma y_ne_one
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
  :
  let y := point.val.2
  y ≠ 1 := by
    intro y h1
    let x := point.val.1
    let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2 : x = 0 := by
      have h2_1 : x^2 + y^2 = 1 + d_of_s * x^2 * y^2 := by exact point.prop
      rw [h1] at h2_1
      simp at h2_1
      rw [← add_left_inj (-1), ← add_left_inj (-x^2)] at h2_1
      simp at h2_1
      rw [← neg_one_mul (x^2), ← add_mul, pow_two, ← mul_assoc] at h2_1
      rw [← div_left_inj' (x_ne_zero), ← div_left_inj' (x_ne_zero)] at h2_1
      rw [mul_div_assoc, div_self (x_ne_zero), mul_one] at h2_1
      rw [mul_div_assoc, div_self (x_ne_zero), mul_one] at h2_1
      rw [← add_left_inj 1] at h2_1
      simp at h2_1
      have h2_2 : IsSquare d_of_s := by
        rw [← h2_1, ← one_mul 1, ← pow_two]
        apply IsSquare.sq 1
      have h2_2 : ¬ IsSquare d_of_s := by exact d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      contradiction
    contradiction

lemma η_ne_zero
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
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  η_of_point ≠ 0 := by
    intro η_of_point
    let x := point.val.1
    let y := point.val.2
    unfold η_of_point η
    change (y - 1) / (2 * (y + 1)) ≠ 0
    apply div_ne_zero
    · intro h1
      have h2 : y ≠ 1 := by exact y_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero
      have h3: y = 1 := by
        rw [← add_left_inj 1] at h1
        simp at h1
        exact h1
      contradiction
    · unfold ϕ_over_F_props at point_props
      apply mul_ne_zero
      · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact point_props.1

lemma ϕ_of_t_eq_ϕ_of_neg_t_base_case
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let ϕ_of_neg_t := (ϕ (-t.val) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_t = ϕ_of_neg_t := by
    rcases t.property with h2_1 | h2_1
    · change (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val = (ϕ (-t.val) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
      rw [h2_1]
      unfold ϕ
      simp
    · change (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val = (ϕ (-t.val) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
      rw [h2_1]
      unfold ϕ
      simp

lemma ϕ_of_t_eq_ϕ_of_neg_t_main_case
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let ϕ_of_neg_t := (ϕ (-t.val) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_t = ϕ_of_neg_t := by
    let t1 := t.val
    let t2 := -t.val
    have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let x1 := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y1 := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2_10 : y2 = y1 := by exact y_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2_12 : x2 = x1 := by exact x_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change (ϕ t1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val = (ϕ t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
    unfold ϕ
    simp
    rw [dif_pos h2_2, dif_pos t.property]
    change (x1, y1) = (x2, y2)
    rw [h2_10, h2_12]

-- Original: Theorem 3.1 forward statement, Proof A
lemma ϕ_of_t_eq_ϕ_of_neg_t
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let ϕ_of_neg_t := (ϕ (-t) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_t = ϕ_of_neg_t := by
    intro ϕ_of_t ϕ_of_neg_t
    by_cases h2 : t = 1 ∨ t = -1
    · exact ϕ_of_t_eq_ϕ_of_neg_t_base_case ⟨t, h2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · have h2_1 : (t ≠ 1 ∧ t ≠ -1) := by
        rw [ne_eq, ne_eq]
        rw [← not_or]
        exact h2
      exact ϕ_of_t_eq_ϕ_of_neg_t_main_case ⟨t, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Original: Theorem 3.1 backward statement (Original: Proof B as the very last argument)
theorem ϕ_preimages
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ¬ (∃ (p : { n : F // n ≠ t ∧ n ≠ -t}), (ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val = ϕ_of_t) := by
    intro ϕ_of_t h
    rcases h with ⟨p, hp⟩
    have h1 : p.val = t ∨ p.val = -t := by
      let p_point := ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      let t_point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      let t2_of_p := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 p_point
      let t2_of_t := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t_point
      have h11 : t2_of_p = p ∨ t2_of_p = -p := by
        exact (t2_in_t_or_neg_t p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
      have h12 : t2_of_t = t ∨ t2_of_t = -t := by
        exact (t2_in_t_or_neg_t t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
      unfold t2_of_p p_point at h11
      rw [hp] at h11
      change t2_of_t = p ∨ t2_of_t = -p at h11
      rcases h11
      · rename_i h13
        rw [← h13]
        exact h12
      · rename_i h13
        rw [h13] at h12
        simp at h12
        symm at h12
        nth_rw 2 [← mul_left_inj' (FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h12
        simp at h12
        exact h12
    have h4 : p ≠ t := by exact p.prop.left
    have h5 : p ≠ -t := by exact p.prop.right
    rcases h1
    · contradiction
    · contradiction

-- Implicated by main case of Theorem 3 Proof part B
lemma ϕ_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_zero := (ϕ (0 : F) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let χ_of_c_of_s  := (LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3)
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_zero  = (2 * (c_of_s - 1) * s * χ_of_c_of_s / r_of_s, (r_of_s - 4) / (r_of_s + 4)) := by
    intro ϕ_of_zero c_of_s χ_of_c_of_s r_of_s
    unfold ϕ_of_zero ϕ
    let h1 := FiniteFieldBasic.zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3
    simp only []
    rw [dif_pos h1]
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 ϕ_of_zero
    have h2 : η_of_point * r_of_s = -2 := by
      unfold η_of_point η ϕ_of_zero ϕ
      simp only []
      rw [dif_pos h1]
      let y_of_t := y ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
      let X_of_zero := X ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
      change (y_of_t - 1) / (2 * (y_of_t + 1)) * r_of_s = -2
      -- This has to be proven again here as in y_η_h1 and X_η_h1 since
      -- the lemmas itself do not help with concret t values
      unfold y_of_t
      rw [(y_of_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
      change ((r_of_s - 4) / (r_of_s + 4) - 1) / (2 * ((r_of_s - 4) / (r_of_s + 4) + 1)) * r_of_s = -2
      have h2_2 : 1 = (r_of_s + 4) / (r_of_s + 4) := by
        rw [add_comm]
        rw [div_self (four_add_r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
      nth_rw 1 [h2_2]
      nth_rw 1 [h2_2]
      rw [← sub_div, ← add_div, ← sub_sub, ← add_assoc]
      ring_nf
      rw [inv_inv, mul_comm r_of_s, mul_assoc _ r_of_s, mul_inv_cancel₀ (r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one]
      rw [inv_mul_cancel₀ (four_add_r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), one_mul]
      rw [← mul_neg_one, ← mul_right_inj' (FiniteFieldBasic.four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (FiniteFieldBasic.four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
      ring_nf
    rw [y_η_h1 ⟨0, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2]
    let x_of_t := ϕ_of_zero.1
    have h3 : x_of_t = 2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s := by
      apply point_in_ϕ_over_F_with_prop3 (0 : F) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      exact h2
    unfold x_of_t ϕ_of_zero ϕ at h3
    simp only [] at h3
    rw [dif_pos h1] at h3
    simp at h3
    rw [h3]
    change (2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s, (r_of_s - 4) / (r_of_s + 4)) = (2 * (c_of_s - 1) * s * χ_of_c_of_s / r_of_s, (r_of_s - 4) / (r_of_s + 4))
    ring_nf

-- Used in theorem 3 proof part C
lemma x_y_eq_ϕ_of_zero_of_X2_eq_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let x := point.val.1
  let y := point.val.2
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let ϕ_of_zero  := ϕ 0 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X2_of_point = 1 → ϕ_of_zero = (x, y) := by
    intro x y X2_of_point ϕ_of_zero' X2_h
    let y_with_X2 := y_with_X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_eq_one
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let h2 := point.prop.2.2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_c_of_s := LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1 : η_of_point * r_of_s = -2 := by exact η_mul_r_eq_neg_two_of_X2_eq_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point X2_h
    have h2 : x = 2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s := by exact point.prop.2.2 h1
    have h3 : y = (r_of_s - 4) / (r_of_s + 4) := by exact y_with_X2_of_X2_eq_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_eq_one X2_h
    simp at h3
    rw [h2, h3]
    let ϕ_of_zero'' := ϕ_of_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    grind

-- Used in theorem 3 proof part C
lemma x_y_eq_ϕ_of_t_of_X2_ne_one
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
  let x := point.val.1
  let y := point.val.2
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let ϕ_of_t := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → ϕ_of_t = (x, y) := by
    intro x y X t ϕ_of_t h1
    unfold ϕ_of_t ϕ
    let h2 := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    simp
    rw [dif_pos h2]
    let x_of_t := Elligator1.x ⟨t, h2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y_of_t := Elligator1.y ⟨t, h2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change (x_of_t, y_of_t) = (x, y)
    let h3 := x_y_of_point_eq_x_y_of_t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    grind

lemma ϕ_of_t2_eq_x_y_base_case
  (t : { n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let t' := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let ϕ_of_t' := (ϕ t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_t' = (0, 1) := by
    intro point t' ϕ_of_t'
    unfold ϕ_of_t' ϕ
    have h1 : ¬ (t' ≠ 1 ∧ t' ≠ -1) := by
      unfold t'
      rw [t2_eq_one t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
      simp
    simp only []
    rw [dif_neg h1]

lemma ϕ_of_t2_eq_x_y_main_case
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t' := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let ϕ_of_t' := ϕ t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t' = (x_of_t, y_of_t) := by
    intro point t' ϕ_of_t' x_of_t y_of_t
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold ϕ_of_t' ϕ
    rcases (t2_in_t_or_neg_t t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) with h | h
    · change t' = t at h
      rw [h]
      simp only []
      rw [dif_pos t.prop]
    · change t' = -t at h
      rw [h]
      simp only []
      rw [dif_pos h2_2]
      unfold x_of_t y_of_t
      symm
      exact point_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma ϕ_of_one_eq_zero_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_one := (ϕ (1 : F) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_one = (0, 1) := by
    intro ϕ_of_one
    unfold ϕ_of_one ϕ
    simp

lemma ϕ_of_neg_one_eq_zero_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_neg_one := (ϕ (-1 : F) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_neg_one = (0, 1) := by
    intro ϕ_of_neg_one
    unfold ϕ_of_neg_one ϕ
    simp

lemma ϕ_of_one_in_ϕ_of_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_one := (ϕ (1 : F) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_one ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 := by
    intro ϕ_of_one
    unfold ϕ_over_F
    rw [Set.mem_setOf_eq]
    use (1 : F)

lemma point_in_ϕ_over_F_base_case
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_eq_zero : point.val.1 = 0)
  :
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  point.val ∈ ϕ_over_F := by
    rw [x_y_eq_zero_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_eq_zero]
    rw [← ϕ_of_one_eq_zero_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    exact ϕ_of_one_in_ϕ_of_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma point_in_ϕ_over_F_main_case_with_y_eq_one
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
  (y_eq_one : point.val.2 = 1)
  :
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  point.val ∈ ϕ_over_F := by
    intro ϕ_over_F
    let x := point.val.1
    let y := point.val.2
    -- Note: this differs from original proof, which claims that this implies x = 0, contra
    -- I was not able to see that
    have h4_1 := point.prop;
    unfold E_over_F at h4_1
    rw [Set.mem_setOf_eq] at h4_1
    let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    rw [y_eq_one] at h4_1
    change x ^ 2 + 1 ^ 2 = 1 + d_of_s * x ^ 2 * 1 ^ 2  at h4_1
    rw [← add_right_inj (-1)] at h4_1
    rw [← div_left_inj' x_ne_zero, ← div_left_inj' x_ne_zero] at h4_1
    ring_nf at h4_1
    have h5 : x^2 ≠ 0 := by grind
    rw [inv_pow, mul_inv_cancel₀ h5, one_mul] at h4_1
    let h6 := d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    symm at h4_1
    contradiction

lemma point_in_ϕ_over_F_main_case_with_y_ne_one
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
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  point.val ∈ ϕ_over_F := by
    intro ϕ_over_F
    let x := point.val.1
    let y := point.val.2
    let η_ne_zero := η_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero
    unfold ϕ_over_F Elligator1.ϕ_over_F
    rw [Set.mem_setOf_eq]
    let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    by_cases X2_h : X2_of_point = (1 : F)
    · use 0
      exact x_y_eq_ϕ_of_zero_of_X2_eq_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_ne_one X2_h
    · use t
      exact x_y_eq_ϕ_of_t_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X2_h

lemma point_in_ϕ_over_F_main_case
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
  :
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  point.val ∈ ϕ_over_F := by
    intro ϕ_over_F
    let x := point.val.1
    let y := point.val.2
    by_cases y_h : y = 1
    · exact point_in_ϕ_over_F_main_case_with_y_eq_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_h
    · exact point_in_ϕ_over_F_main_case_with_y_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_h

-- Original: Theorem 3.2 Proof C (3.2 reverse statement)
theorem point_in_ϕ_over_F_of_point_props
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  → point.val ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  := by
    intro h1
    let x := point.val.1
    let y := point.val.2
    by_cases h2 : x = 0
    · exact point_in_ϕ_over_F_base_case s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point h1 h2
    · rw [← not_ne_iff, not_not] at h2
      exact point_in_ϕ_over_F_main_case s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point h1 h2
