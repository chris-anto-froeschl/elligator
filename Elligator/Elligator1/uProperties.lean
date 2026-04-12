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
public import Elligator.Elligator1.rProperties

@[expose] public section

/-!
# u Variable Properties

In this file we introduce some generally helpful lemmas for `u` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section uProperties

variable {F : Type*} [Field F] [Fintype F]

lemma u_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  u t q field_cardinality q_prime_power q_mod_4_congruent_3 ≠ (0 : F) := by
    change (1 - t.val) / (1 + t.val) ≠ 0
    apply div_ne_zero (FiniteFieldBasic.one_sub_t_ne_zero t) (FiniteFieldBasic.one_add_t_ne_zero t)

lemma u_pow_two_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  u_of_t^2 ≠ (0 : F) := by
    intro u_of_t
    rw [pow_two]
    apply mul_ne_zero
    · exact (u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t)
    · exact (u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t)

lemma u_comparison
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let u1 := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  u2 = 1 / u1 := by
    intro t1 t2 h2_2 u1 u2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      u2 = (1 - t2) / (1 + t2) := by
        unfold u2 u
        simp
     _ = (1 + t) / (1 - t) := by
       unfold t2 t1
       simp
       ring_nf
     _ = 1 / u1 := by
       unfold u1 u
       simp

lemma u_of_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact FiniteFieldBasic.zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let u_of_t := u ⟨(0 : F), h1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3;
  u_of_t = 1 := by
    intro h1 u_of_t
    unfold u_of_t u
    simp

lemma one_add_u_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  {q : ℕ}
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let u := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  1 + u ≠ 0 := by
    intro u
    unfold u Elligator1.u;
    rw [add_div' _ _ _ (by exact FiniteFieldBasic.one_add_t_ne_zero t)]
    norm_num
    split_ands
    · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3;
    · exact FiniteFieldBasic.one_add_t_ne_zero t
