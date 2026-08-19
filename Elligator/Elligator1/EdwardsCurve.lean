/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Primitives.ECC.EdwardsCurve
public import Elligator.Elligator1.dProperties

/-!
# The Edwards curve used by Elligator 1

This file specializes the general Edwards curve API of `Elligator.ECCPrimitives.EdwardsCurve` to
the curve and coefficient produced by Elligator 1.

## Main results

* `curve`: the Edwards curve with the paper's coefficient `d(s)`.
* `curve_isValid`: the Elligator hypotheses imply that `d(s)` is a valid Edwards coefficient.
* `EOverF`: the set of affine field-valued points satisfying the Elligator 1 curve equation.
* `EOverF_eq_affinePoints`: `EOverF` agrees with the general Edwards affine-point set.

## References

See [Bernstein2013a], Section 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.Primitives.ECC

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

/-- The Edwards curve selected by the Elligator 1 parameter `s`. -/
def curve (s : F) : TwistedEdwardsCurve F := edwardsCurve (d s)

omit [Fintype F] in
/-- The curve equation of the Elligator 1 curve, in explicit form. -/
theorem curve_equation_iff (s x y : F) :
    (curve s).Equation x y ↔ x ^ 2 + y ^ 2 = 1 + d s * x ^ 2 * y ^ 2 :=
  edwardsCurve_equation_iff (d s) x y

/-- The Elligator 1 coefficient hypotheses imply that its specialized curve is valid. -/
theorem curve_isValid {s : F} (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (curve s).IsValid := by
  rw [curve, edwardsCurve_isValid_iff]
  exact d_ne_zero_and_d_ne_one sq_ne_pm_two hq_card hq_mod

/-- `EOverF` is the set of affine points on the Edwards curve selected by Elligator 1.

The hypotheses record that `d s` is a valid Edwards coefficient, see `curve_isValid`.
-/
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
def EOverF {s : F} (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) : Set (F × F) :=
  have _hvalid : (curve s).IsValid := curve_isValid sq_ne_pm_two hq_card hq_mod
  (curve s).affinePoints

/-- The compatibility set `EOverF` is exactly the affine point set of the general curve model. -/
theorem EOverF_eq_affinePoints {s : F} (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    EOverF sq_ne_pm_two hq_card hq_mod = (curve s).affinePoints := by
  rfl

/-- Membership in `EOverF`, written out as the Edwards curve equation. -/
theorem mem_EOverF_iff {s : F} (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) (p : F × F) :
    p ∈ EOverF sq_ne_pm_two hq_card hq_mod ↔
      p.1 ^ 2 + p.2 ^ 2 = 1 + d s * p.1 ^ 2 * p.2 ^ 2 :=
  curve_equation_iff s p.1 p.2

/-- The neutral point `(0, 1)` lies in `EOverF`; a specialization of
`Elligator.edwardsCurveEquation_zero_one`. -/
theorem zero_mem_EOverF {s : F} (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    ((0 : F), (1 : F)) ∈ EOverF sq_ne_pm_two hq_card hq_mod :=
  (curve s).zero_mem_affinePoints

end Elligator.Elligator1
