/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.TwistedEdwardsCurve
public import Elligator.Elligator1.dProperties

/-!
# The Edwards curve used by Elligator 1

This file specializes the general `Elligator.TwistedEdwardsCurve` API to the untwisted Edwards
curve and parameter produced by Elligator 1.

The general curve definition deliberately does not depend on a finite field, its cardinality, or
the Elligator parameter `s`; those assumptions occur only in the specialization proving that
`d s` is a valid coefficient.

## References

See [bernstein2013a] chapter 3.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

/-- The general Edwards curve with coefficient `d`.
This is an alias for the `a = 1` specialization of a twisted Edwards curve. -/
def edwardsCurve (d : F) : TwistedEdwardsCurve F := TwistedEdwardsCurve.ofD d

/-- `edwardsCurveEquation` is the standard Edwards curve equation.
The subtype argument is preserved for compatibility.  New generic developments should normally
use `(edwardsCurve d).Equation x y`, and carry coefficient validity separately via
`TwistedEdwardsCurve.IsValid`.
-/
@[blueprint "def:edwardsCurveEquation"]
def edwardsCurveEquation (x y : F) (d : {d : F // d ≠ 0 ∧ d ≠ 1}) : Prop :=
  (edwardsCurve (F := F) d.val).Equation x y

omit [Fintype F] in
@[simp]
theorem edwardsCurveEquation_iff (x y : F) (d : {d : F // d ≠ 0 ∧ d ≠ 1}) :
  edwardsCurveEquation x y d ↔ x^2 + y^2 = 1 + d * x^2 * y^2 := by
    simp [edwardsCurveEquation, edwardsCurve]

/-- The Edwards curve selected by the Elligator 1 parameter `s`. -/
noncomputable def curve (s : F) : TwistedEdwardsCurve F :=
  edwardsCurve (d s)

/-- The Elligator 1 coefficient hypotheses imply that its specialized curve is valid. -/
theorem curve_isValid
  {s : F}
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3) :
  (curve s).IsValid := by
    rw [curve, edwardsCurve, TwistedEdwardsCurve.ofD_isValid_iff]
    exact d_ne_zero_and_d_ne_one s_h2 q_h1 q_h3

/-- `EOverF` is the set of affine points on the Edwards curve selected by Elligator 1.
See `EOverF_eq_affinePoints` for the generic curve view. -/
@[blueprint "def:EOverF"]
def EOverF
  {s : F}
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3) : Set (F × F) :=
  let d := d s
  let d_h : d ≠ 0 ∧ d ≠ 1 :=
    d_ne_zero_and_d_ne_one s_h2 q_h1 q_h3
  {p | edwardsCurveEquation p.fst p.snd ⟨d, d_h⟩}

/-- The compatibility set `EOverF` is exactly the affine point set of the general curve model. -/
theorem EOverF_eq_affinePoints
  {s : F}
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3) :
    EOverF s_h2 q_h1 q_h3 = (curve s).affinePoints := by
  rfl

@[blueprint "lemma:zero_one_fulfill_edwardsCurveEquation"]
lemma zero_one_fulfill_edwardsCurveEquation
  {s : F}
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  :
  let d := d s
  let d_h : d ≠ 0 ∧ d ≠ 1 := d_ne_zero_and_d_ne_one s_h2 q_h1 q_h3
  edwardsCurveEquation (0 : F) (1 : F) ⟨d, d_h⟩ := by
    intro d_of_s d_h
    unfold edwardsCurveEquation
    simp [edwardsCurve]

end Elligator.Elligator1
