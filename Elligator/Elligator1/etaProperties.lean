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

@[expose] public section

/-!
# η Properties

In this file we introduce some generally helpful lemmas for `η` as introduced in `Elligator.Elligator1.Variables`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section etaProperties

variable {F : Type*} [Field F] [Fintype F]

lemma η_eq_zero
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  η_of_point = 0 := by
    intro point η_of_point
    unfold η_of_point η
    let y_of_t := point.2
    change (y_of_t - 1) / (2 * (y_of_t + 1)) = 0
    unfold y_of_t point
    rw [ϕ_of_t_eq_zero_one t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp
