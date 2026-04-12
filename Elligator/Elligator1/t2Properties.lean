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
public import Elligator.Elligator1.zProperties
public import Elligator.Elligator1.u2Properties

@[expose] public section

/-!
# t2 Variable Properties

In this file we introduce some generally helpful lemmas for `t2` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/


namespace Elligator.Elligator1

section t2Properties

variable {F : Type*} [Field F] [Fintype F]

lemma t2_eq_one
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  t2_of_point = 1 := by
    intro point t2_of_point
    unfold t2_of_point t2
    let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    change (1 - u2_of_point) / (1 + u2_of_point) = 1
    unfold u2_of_point
    rw [u2_eq_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma t2_eq_t
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (X_h :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    X2_of_t = X_of_t
  )
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  t2_of_point = t := by
    intro point t2_of_point
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1 : u2_of_t = u_of_t := by exact u2_eq_u t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 X_h
    unfold u_of_t u at h1
    unfold t2_of_point t2
    change (1 - u2_of_t) / (1 + u2_of_t) = t.val
    change u2_of_t = (1 - t.val) / (1 + t.val) at h1
    rw [h1]
    rw [sub_div' (FiniteFieldBasic.one_add_t_ne_zero t)]
    rw [add_div' (1 - t.val) 1 (1 + t.val) (FiniteFieldBasic.one_add_t_ne_zero t)]
    simp
    rw [div_div_div_eq]
    norm_num
    have h2 : ((1 + t.val) * 2) ≠ 0 := by
      apply mul_ne_zero
      · exact FiniteFieldBasic.one_add_t_ne_zero t
      · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [← two_mul t.val, mul_comm 2 t.val, mul_assoc, mul_comm 2, mul_div_assoc, div_self h2]
    simp

lemma t2_eq_t'
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (X_h :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let X'_of_t := X ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    X2_of_t = X'_of_t
  )
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let t' := -t.val
  t2_of_point = t' := by
    intro point t2_of_point t'
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let u'_of_t := u ⟨t', h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1 : u2_of_t = u'_of_t := by exact u2_eq_u' t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 X_h
    unfold u'_of_t u at h1
    unfold t2_of_point t2
    change (1 - u2_of_t) / (1 + u2_of_t) = t'
    change u2_of_t = (1 - t') / (1 + t') at h1
    rw [h1]
    rw [sub_div' (FiniteFieldBasic.one_add_t_ne_zero ⟨t', h2_2⟩)]
    rw [add_div' (1 - t') 1 (1 + t') (FiniteFieldBasic.one_add_t_ne_zero ⟨t', h2_2⟩)]
    simp
    rw [div_div_div_eq]
    norm_num
    have h2 : ((1 + t') * 2) ≠ 0 := by
      apply mul_ne_zero
      · exact FiniteFieldBasic.one_add_t_ne_zero ⟨t', h2_2⟩
      · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [← two_mul t', mul_comm 2 t', mul_assoc, mul_comm 2, mul_div_assoc, div_self h2]
    simp

lemma t2_in_t_or_neg_t
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t' := -t
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  t2_of_point = t ∨ t2_of_point = t' := by
    intro point t' t2_of_point
    by_cases h : t ≠ 1 ∧ t ≠ -1
    · rcases (X2_h4 ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) with h1 | h1
      · left
        exact t2_eq_t ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1
      · right
        exact t2_eq_t' ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1
    · have h' : t = 1 ∨ t = -1 := by
        rw [← not_ne_iff, ← not_ne_iff, ← Lean.Grind.not_and]
        exact h
      unfold t2_of_point t'
      rw [t2_eq_one ⟨t, h'⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
      have h'' : 1 = t ∨ 1 = -t := by
        nth_rw 2 [← mul_left_inj' (FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
        simp
        nth_rw 1 [eq_comm]
        nth_rw 2 [eq_comm]
        exact h'
      exact h''

/-- `t'` is the `t` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def t'
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
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  (1 - u) / (1 + u)

lemma t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
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
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  X ≠ 1 → t ≠ 1 ∧ t ≠ -1 := by
    intro X t h1
    unfold t t'
    let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let u'_eq_X2_or_u'_eq_neg_X2 := u'_eq_X2_or_u'_eq_neg_X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    change u = X ∨ u = -X at u'_eq_X2_or_u'_eq_neg_X2
    change (1 - u) / (1 + u) ≠ 1 ∧ (1 - u) / (1 + u) ≠ -1
    let one_add_u'_ne_zero := one_add_u'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    let u'_ne_zero := u'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    let two_ne_zero := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    and_intros
    · intro h2
      have h3 : 2 = 0 := by grind
      contradiction
    · intro h2
      have h3 : 2 = 0 := by grind
      contradiction

lemma one_add_t'_ne_zero
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
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  X ≠ 1 → t + 1 ≠ 0 := by
    intro X t h1
    let t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    grind

lemma u'_eq_one_sub_t'_over_one_add_t'
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
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  X ≠ 1 → u = (1 - t) / (1 + t) := by
    intro X u t h1
    unfold t t'
    let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let one_add_u'_ne_zero := one_add_u'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    let two_ne_zero := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    grind

lemma u'_eq_u
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
  (X_h :
    let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X ≠ 1
  )
  :
  let u' := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let u := u ⟨t, t_h⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  u' = u := by
    intro u' t t_h u
    let h1 := u'_eq_one_sub_t'_over_one_add_t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    unfold u' u
    rw [h1]
    unfold Elligator1.u
    grind

lemma v'_eq_v
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
  (X_h :
    let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X ≠ 1
  )
  :
  let v' := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let v := v ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  v' = v := by
    intro v' t t_h v
    let h1 := u'_eq_one_sub_t'_over_one_add_t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := u'_eq_u s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    unfold v' v Elligator1.v' Elligator1.v
    rw [h1]
    grind

lemma X'_eq_X
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
  (X_h :
    let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X ≠ 1
  )
  :
  let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let X := X ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X' = X := by
    intro X' t t_h X
    let h1 := u'_eq_one_sub_t'_over_one_add_t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := u'_eq_u s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h3 := v'_eq_v s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h4 := X'_eq_χ_of_v'_mul_u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    unfold X'
    rw [h4, h2, h3]
    change X = X
    rfl

lemma Y'_eq_Y
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
  (X_h :
    let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X ≠ 1
  )
  :
  let Y' := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let Y := Y ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  Y' = Y := by
    intro Y' t t_h Y
    let h2 := u'_eq_u s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h3 := v'_eq_v s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h4 := Y'_observation2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    unfold Y'
    rw [h4, h2, h3]
    change Y = Y
    rfl

/-- `x'` is the `x` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def x'
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
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
  let Y' := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  (c - 1) * s * X' * (1 + X') / Y'

lemma x'_eq_x
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
  (X_h :
    let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X' ≠ 1
  )
  :
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let x := x ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x' := x' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  x' = x := by
    intro t t_h x x'
    unfold x' Elligator1.x' x Elligator1.x
    let h1 := u'_eq_u s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := v'_eq_v s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := Y'_eq_Y s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := X'_eq_X s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    grind

/-- `y'` is the `y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def y'
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
  let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
  let r := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (r * X' - (1 + X')^2) / (r * X' + (1 + X')^2)

lemma y'_eq_y
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
  (X_h :
    let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X' ≠ 1
  )
  :
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let y := y ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y' := y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  y' = y := by
    intro t t_h y y'
    unfold y' Elligator1.y' y Elligator1.y
    let h1 := u'_eq_u s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := v'_eq_v s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := Y'_eq_Y s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := X'_eq_X s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    grind

theorem x'_and_y'_fulfill_curve_equation
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
  (X_h :
    let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X' ≠ 1
  )
  :
  let x' := x' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let y' := y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let d := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  have d_h : d ≠ 0 ∧ d ≠ 1 := by exact d_ne_zero_and_d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  edwards_curve_equation x' y' ⟨d, d_h⟩ := by
    intro x' y' d
    let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let x := x ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y := y ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x'_eq_x := x'_eq_x s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let y'_eq_y := y'_eq_y s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h1 := x_pow_two_add_y_pow_two_eq_one_add_d_mul_x_pow_two_mul_y_pow_two ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold edwards_curve_equation x' y'
    rw [x'_eq_x, y'_eq_y]
    change x^2 + y^2 = 1 + d * x^2 * y^2
    grind

-- TODO how to do jump to point.val.(1|2) = (x'|y')?
-- They have the same formulas (i.e x'/y' = x/y), but always only using point as a builder

lemma y_of_t_eq_y_of_point
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
  (X_h :
    let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X' ≠ 1
  )
  :
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let y_of_t := y ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_point := point.val.2
  y_of_t = y_of_point := by
    intro t t_h y_of_t y_of_point
    let y_with_X2 := y_with_X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_ne_one
    unfold y_of_point
    rw [y_with_X2]
    unfold y_of_t Elligator1.y
    let h2 := X'_eq_X s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    grind

lemma x_of_t_eq_x_of_point
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
  (X_h :
    let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X' ≠ 1
  )
  :
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let x_of_t := x ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x_of_point := point.val.1
  x_of_t = x_of_point := by
    intro t t_h x_of_t x_of_point
    let Y' := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let Y'_ne_zero := Y'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    change x_of_point ≠ 0 at x_ne_zero
    have h1 : Y' = (c - 1) * s * X * (1 + X) / x_of_point := by
      unfold Y' Elligator1.Y'
      grind
    have h2 : x_of_point = (c - 1) * s * X * (1 + X) / Y' := by
      unfold Y' Elligator1.Y'
      rw [← div_left_inj' x_ne_zero, ← mul_left_inj' Y'_ne_zero]
      change x_of_point / x_of_point * Y' = (c - 1) * s * X * (1 + X) / Y' / x_of_point * Y'
      grind
    rw [h2]
    let h3 := Y'_eq_Y s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h4 := X'_eq_X s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    unfold Y' X
    rw [h3, h4]
    change x_of_t = x_of_t
    rfl

lemma x_y_of_point_eq_x_y_of_t
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
  (X_h :
    let X' := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val;
    X' ≠ 1
  )
  :
  let t := t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
  let y_of_t := y ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_point := point.val.2
  let x_of_t := x ⟨t, t_h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x_of_point := point.val.1
  (x_of_t, y_of_t) = (x_of_point, y_of_point) := by
    intro t t_h y_of_t y_of_point
    let h1 := x_of_t_eq_x_of_point s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    let h2 := y_of_t_eq_y_of_point s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one X_h
    grind
