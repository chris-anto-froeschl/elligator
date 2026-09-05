/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Primitives.ECC.EdwardsCurve
public import Elligator.Elligator1.CurveParameters

/-!
# The Edwards curve used by Elligator 1

This file specializes the general Edwards curve API of `Elligator.Primitives.ECC.EdwardsCurve` to
the curve and coefficient produced by Elligator 1.

## Main results

* `curve`: the Edwards curve with the paper's coefficient `d(s)`.
* `curve_isValid`: the Elligator hypotheses imply that `d(s)` is a valid Edwards coefficient.
* `EOverF s`: the set of affine field-valued points satisfying the Elligator 1 curve equation.
* `EOverF s_eq_affinePoints`: `EOverF s` agrees with the general Edwards affine-point set.

## References

See [Bernstein2013a], Section 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.Primitives.ECC
open Elligator.Elligator1.CurveParameters

variable {F : Type*} [Field F]
variable {s : F}
variable (D : ParamData F)

/-- The Edwards curve selected by the Elligator 1 parameter `s`. -/
def curve (s : F) : TwistedEdwardsCurve F := edwardsCurve (d s)

def _root_.Elligator.Elligator1.ParamData.curve : TwistedEdwardsCurve F :=
    Elligator1.curve D.s

/-- The curve equation of the Elligator 1 curve, in explicit form. -/
lemma curve_equation_iff (x y : F) :
    D.curve.Equation x y ↔ x ^ 2 + y ^ 2 = 1 + D.d * x ^ 2 * y ^ 2 :=
  edwardsCurve_equation_iff D.d x y

/-- The Elligator 1 coefficient hypotheses imply that its specialized curve is valid. -/
lemma curve_isValid [Fintype F] [IsRegularParam D.s] [IsCardThreeModFour F] :
    D.curve.IsValid := by
  unfold ParamData.curve curve
  rw [edwardsCurve_isValid_iff]
  exact d_ne_zero_and_d_ne_one D

/-- `EOverF s` is the set of affine points on the Edwards curve selected by Elligator 1. -/
@[blueprint "def:EOverF"
  (title := "The point set $E(\\mathbb{F}_q)$")
  (statement := /--
  With $d = -(c + 1) ^ 2/(c - 1) ^ 2$ as in Theorem 1, let
  $$
  E(\mathbb{F}_q) = \{(x, y) \in \mathbb{F}_q \times \mathbb{F}_q :
    x ^ 2 + y ^ 2 = 1 + d x ^ 2 y ^ 2\}
  $$
  be the set of affine points of the complete Edwards curve $E$.
  -/)]
def EOverF (s : F) : Set (F × F) := (curve s).affinePoints

def _root_.Elligator.Elligator1.ParamData.EOverF : Set (F × F) :=
    Elligator1.EOverF D.s

/-- The compatibility set `EOverF s` is exactly the affine point set of the general curve model. -/
lemma EOverF_s_eq_affinePoints : D.EOverF = D.curve.affinePoints := by rfl

/-- Membership in `EOverF s`, written out as the Edwards curve equation. -/
lemma mem_EOverF_iff (p : F × F) :
    p ∈ D.EOverF ↔ p.1 ^ 2 + p.2 ^ 2 = 1 + D.d * p.1 ^ 2 * p.2 ^ 2 :=
  curve_equation_iff D p.1 p.2

/-- The neutral point `(0, 1)` lies in `EOverF s`; a specialization of
`Elligator.edwardsCurveEquation_zero_one`. -/
lemma zero_mem_EOverF : ((0 : F), (1 : F)) ∈ D.EOverF := D.curve.zero_mem_affinePoints

end Elligator.Elligator1
