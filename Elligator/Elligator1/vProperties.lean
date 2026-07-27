/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.cProperties
public import Elligator.Elligator1.rProperties
public import Elligator.Elligator1.uProperties

/-!
# v Variable Properties

In this file we introduce some generally helpful lemmas for `v` as introduced in
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

@[blueprint "lemma:v_h"]
lemma v_h1_third_factor_ne_zero
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : (u t)^2 + 1 / (c s)^2 ≠ 0 := by
    intro h
    have h' : -1 = ((u t) * (c s))^2 := by grind [c_pow_two_ne_zero, div_left_inj']
    have h'' : IsSquare (-1 : F) := by
      rw [h', pow_two]
      apply IsSquare.mul_self
    rw [FiniteField.isSquare_neg_one_iff] at h''
    rw [q_h1] at h''
    contradiction

@[blueprint "lemma:v_h"]
lemma v_h1
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let v := v t s
  let c := c s
  let u := u t
  v = u * (u^2 + c^2) * (u^2 + 1 / c^2) := by
    intro v c u
    let r := r s
    change u^5 + (r^2 - 2) * u^3 + u = u * (u^2 + c^2) * (u^2 + 1 / c^2)
    have h1 : c^2 ≠ 0 := by exact pow_two_ne_zero (c_ne_zero s_h1 q_h1 q_h2 q_h3)
    grind [r_h1]

@[blueprint "lemma:v_h"]
lemma v_h1_second_factor_ne_zero
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : (u t)^2 + (c s)^2 ≠ 0 := by
    intro h
    let c := c s
    let u := u t
    have h' : -1 = (u / c)^2 := by
      let h'' := (c_pow_two_ne_zero s_h1 q_h1 q_h2 q_h3)
      grind
    have h'' : IsSquare (-1 : F) := by
      rw [h', pow_two]
      apply IsSquare.mul_self (u / c)
    rw [FiniteField.isSquare_neg_one_iff, q_h1] at h''
    contradiction

@[blueprint "lemma:v_ne_zero"]
lemma v_ne_zero
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : v t s ≠ (0 : F) := by
    rw [v_h1 s_h1 q_h1 q_h2 q_h3 t]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply u_ne_zero t
      · exact (v_h1_second_factor_ne_zero s_h1 q_h1 q_h2 q_h3 t)
    · exact (v_h1_third_factor_ne_zero s_h1 q_h1 q_h2 q_h3 t)

@[blueprint "lemma:χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero"]
lemma χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let v := v t s
  ((χ v) * v)^((q + 1) / 4) ≠ 0 := by
    intro v
    rw [mul_pow (χ v) v ((q + 1) / 4)]
    apply mul_ne_zero
    · apply pow_ne_zero ((q + 1) / 4) (χ_a_ne_zero (v_ne_zero s_h1 q_h1 q_h2 q_h3 t) q_h1)
    · apply pow_ne_zero ((q + 1) / 4) (v_ne_zero s_h1 q_h1 q_h2 q_h3 t)

omit [Fintype F] in
@[blueprint "lemma:v_comparison"]
lemma v_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
  let t1 := t.val
  let t2 := -t1
  let u1 := u t
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  let r := r s
  v2 = 1 / u1^5 + (r^2 - 2) * 1 / u1^3 + 1 / u1 := by
    intro t1 t2 u1 v2 r_of_s
    let u2 := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
    calc
      v2 = u2^5 + (r_of_s^2 - 2) * u2^3 + u2 := by rfl
      _ = 1 / u1^5 + (r_of_s^2 - 2) * 1/ u1^3 + 1 / u1 := by
        unfold u2 u1 t2 t1
        rw [u_comparison t]
        ring_nf

omit [Fintype F] in
@[blueprint "lemma:v_comparison_implication"]
lemma v_comparison_implication1 (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
  let t1 := t.val
  let t2 := -t1
  let u1 := u t
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  v2 * u1^6 = v1 := by
    intro t1 t2 u1 v1 v2
    let r := r s
    calc
      v2 * u1^6 = u1 + (r^2 - 2) * u1^3 + u1^5 := by
        unfold v2
        rw [v_comparison t]
        grind
      _ = v1 := by grind [v]

omit [Fintype F] in
@[blueprint "lemma:v_comparison_implication"]
lemma v_comparison_implication2 (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
  let t1 := t.val
  let t2 := -t1
  let u1 := u t
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  v2 = v1 / u1^6 := by
    intro t1 t2 u1 v1 v2
    have h2_6_1 : u1^6 ≠ 0 := by apply pow_ne_zero 6 (u_ne_zero t)
    rw [← mul_right_inj' h2_6_1]
    unfold v1
    rw [← v_comparison_implication1 t]
    grind

@[blueprint "lemma:v_comparison_implication"]
lemma v_comparison_implication3
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  : χ ((u t)^6) = 1 := by
    let u := u t
    have h : u^6 = u^2 * u^2 * u^2 := by ring_nf
    rw [h]
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
    rw [LegendreSymbol.χ_of_a_pow_two_eq_one (u_ne_zero t) q_h1 q_h3]
    simp

@[blueprint "lemma:v_comparison_implication"]
lemma v_comparison_implication4
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  χ v2 = χ v1 := by
    intro t1 t2 v1 v2
    let u := u t
    unfold v1
    rw [← v_comparison_implication1 t]
    change χ v2= χ (v2 * u^6)
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
    rw [v_comparison_implication3 t q_h1 q_h3]
    simp

omit [Fintype F] in
@[blueprint "lemma:v_of_zero"]
lemma v_of_zero :
  let v := v ⟨(0 : F), zero_h1⟩ s
  v = (r s)^2 := by
    intro v_of_t
    unfold v_of_t v
    rw [u_of_zero]
    ring_nf

end Elligator.Elligator1
