/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.dProperties

/-!
# Edwards Curve

In this file we give a basic framework to talk about Edwards Curves.

TODO provided by some existing ECC lib part? I don't intend to define the most general defs here

## References

See [bernstein2013a] chapter 3.
-/

@[expose] public section

namespace Elligator.Elligator1

section EdwardsCurve

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

/-- `edwardsCurveEquation` is the standard edwards curve equation. -/
@[blueprint "def:edwardsCurveEquation"]
def edwardsCurveEquation (x y : F) (d : {d : F // d ≠ 0 ∧ d ≠ 1})
  : Prop := x^2 + y^2 = 1 + d * x^2 * y^2

/-- `EOverF` is the set of points fulfilling the `edwardsCurveEquation`. -/
@[blueprint "def:EOverF"]
def EOverF
  {s : F}
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : Set (F × F) :=
  let d := d s
  let d_h : d ≠ 0 ∧ d ≠ 1 :=
    d_ne_zero_and_d_ne_one s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
  {p | edwardsCurveEquation p.fst p.snd ⟨d, d_h⟩}

@[blueprint "lemma:zero_one_fulfill_edwardsCurveEquation"]
lemma zero_one_fulfill_edwardsCurveEquation
  {s : F}
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d := d s
  let d_h : d ≠ 0 ∧ d ≠ 1 :=
    d_ne_zero_and_d_ne_one s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
  edwardsCurveEquation (0 : F) (1 : F) ⟨d, d_h⟩ := by
    intro d_of_s d_h
    unfold edwardsCurveEquation
    ring

end EdwardsCurve

end Elligator.Elligator1
