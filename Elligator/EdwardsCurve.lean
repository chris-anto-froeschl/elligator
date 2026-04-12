/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.dProperties

@[expose] public section

/-!
# Edwards Curve

In this file we give a basic framework to talk about Edwards Curves

TODO does this fit into some existing ECC lib part?

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section EdwardsCurve

variable {F : Type*} [Field F] [Fintype F]

-- TODO generalize to actual characteristic ≠ 2
/-- An \emph{Edwards curve} over a field $K$ (with $\mathrm{char}(K) \neq 2$) is a plane algebraic curve defined by an equation of the form
\[
x^2 + y^2 = 1 + d x^2 y^2,
\]
where $d \in K \setminus \{0,1\}$. -/
def edwards_curve_equation
  (x y : F)
  (d : {d : F // d ≠ 0 ∧ d ≠ 1})
  : Prop := x^2 + y^2 = 1 + d * x^2 * y^2

/-- `E_over_F` is the set of points fulfilling the `edwards_curve_equation`. -/
def E_over_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : Set (F × F) :=
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  have d_h : d_of_s ≠ 0 ∧ d_of_s ≠ 1 := by exact d_ne_zero_and_d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  {p | edwards_curve_equation p.fst p.snd ⟨d_of_s, d_h⟩}

lemma zero_one_fulfill_edwards_curve_equation
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  have d_h : d_of_s ≠ 0 ∧ d_of_s ≠ 1 := by exact d_ne_zero_and_d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  edwards_curve_equation (0 : F) (1 : F) ⟨d_of_s, d_h⟩ := by
    intro d_of_s d_h
    unfold edwards_curve_equation
    ring
