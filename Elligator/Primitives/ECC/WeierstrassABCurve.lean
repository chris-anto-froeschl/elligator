/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module
public import Elligator.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Weierstrass curves with a rational point of order two

A curve of the shape `y ^ 2 = x ^ 3 + A * x ^ 2 + B * x` is the curve shape handled by
Elligator 2, see [Bernstein2013a], Section 5: it is exactly the Weierstrass shape carrying the
visible point `(0, 0)` of order two, and it includes all Montgomery curves
`y ^ 2 = x ^ 3 + A * x ^ 2 + x` except `y ^ 2 = x ^ 3 + x`.

The definitions are made over a commutative ring, in the same style as
`Elligator.Primitives.ECC.TwistedEdwardsCurve`: coefficients, an affine equation, a set of affine
points, a bundled point type, and a nonsingularity predicate. The relation to Mathlib's general
Weierstrass model is recorded by `WeierstrassABCurve.toWeierstrassCurve`,
`WeierstrassABCurve.equation_iff_weierstrass`, `WeierstrassABCurve.affinePoints_eq_weierstrass`
and `WeierstrassABCurve.isValid_iff_Delta_ne_zero`, so that nothing here is a new curve notion:
this structure is a two-parameter slice of `WeierstrassCurve`, not an alternative to it.

## Why a separate structure rather than `WeierstrassCurve` directly

`WeierstrassCurve` carries the five coefficients `a₁, a₃, a₂, a₄, a₆`, while Section 5 of
[Bernstein2013a] works throughout with the two coefficients `A`, `B` of
`y ^ 2 = x ^ 3 + A x ^ 2 + B x` and with the factorisation `x (x ^ 2 + A x + B)` of its right
hand side. Keeping `A` and `B` as the fields of the structure keeps every statement in the
formalisation literally the statement of the paper, keeps `Elligator 2` parallel to the
`TwistedEdwardsCurve` used for Elligator 1, and gives the affine solution set as a plain
`Set (R × R)`, which is what the counting and bijection results of Theorems 7 and 8 talk about
(Mathlib's `WeierstrassCurve.Affine.Point` additionally contains the point at infinity and is
built for the group law, which Elligator 2 never uses). The lemmas above make the two views
interchangeable whenever Mathlib's Weierstrass API is wanted.

## Main definitions

* `WeierstrassABCurve`: the coefficients `A`, `B` of the model
  `y ^ 2 = x ^ 3 + A * x ^ 2 + B * x`, with its equation `WeierstrassABCurve.Equation`, its
  affine points `WeierstrassABCurve.affinePoints` and the nonsingularity condition
  `WeierstrassABCurve.IsValid`.
* `WeierstrassABCurve.toWeierstrassCurve`: the same curve as a Mathlib `WeierstrassCurve`.

## TODO

- Move into mathlib next to Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

## References

* [Bernstein2013a], Section 5.
-/

@[expose] public section
namespace Elligator.Primitives.ECC

/-- Coefficients of the Weierstrass equation `y ^ 2 = x ^ 3 + A * x ^ 2 + B * x`. -/
@[ext]
structure WeierstrassABCurve (R : Type*) where
  /-- coefficient of `x ^ 2` -/
  A : R
  /-- coefficient of `x` -/
  B : R

variable {R : Type*} [CommRing R]

namespace WeierstrassABCurve

/-- The proposition that `(x, y)` is an affine point of `y ^ 2 = x ^ 3 + A * x ^ 2 + B * x`. -/
def Equation (E : WeierstrassABCurve R) (x y : R) : Prop :=
    y ^ 2 = x ^ 3 + E.A * x ^ 2 + E.B * x

/-- The right hand side `x ^ 3 + A * x ^ 2 + B * x` of the curve equation. -/
def rhs (E : WeierstrassABCurve R) (x : R) : R := x ^ 3 + E.A * x ^ 2 + E.B * x

/-- The quadratic factor `x ^ 2 + A * x + B` of the right hand side. -/
def rhsFactor (E : WeierstrassABCurve R) (x : R) : R := x ^ 2 + E.A * x + E.B

lemma rhs_eq_mul_rhsFactor (E : WeierstrassABCurve R) (x : R) :
    E.rhs x = x * E.rhsFactor x := by
  simp only [rhs, rhsFactor]
  ring

lemma equation_iff_rhs (E : WeierstrassABCurve R) (x y : R) :
    E.Equation x y ↔ y ^ 2 = E.rhs x := Iff.rfl

/-- The set of affine coordinate pairs on the curve. -/
def affinePoints (E : WeierstrassABCurve R) : Set (R × R) := {p | E.Equation p.1 p.2}

/-- A bundled affine point of the curve. -/
abbrev Point (E : WeierstrassABCurve R) := {p : R × R // p ∈ E.affinePoints}

/-- Membership in `affinePoints`, written out as the curve equation. -/
lemma mem_affinePoints_iff (E : WeierstrassABCurve R) (p : R × R) :
    p ∈ E.affinePoints ↔ p.2 ^ 2 = p.1 ^ 3 + E.A * p.1 ^ 2 + E.B * p.1 := Iff.rfl

/-- The point of order two visible in this curve shape. -/
def twoTorsion : R × R := (0, 0)

lemma twoTorsion_mem_affinePoints (E : WeierstrassABCurve R) :
    twoTorsion ∈ E.affinePoints := by
  change (0 : R) ^ 2 = 0 ^ 3 + E.A * 0 ^ 2 + E.B * 0
  ring

/-- Negation of affine coordinates on the curve. -/
def neg (p : R × R) : R × R := (p.1, -p.2)

lemma neg_mem_affinePoints (E : WeierstrassABCurve R) (p : R × R) :
    neg p ∈ E.affinePoints ↔ p ∈ E.affinePoints := by
  change (-p.2) ^ 2 = p.1 ^ 3 + E.A * p.1 ^ 2 + E.B * p.1 ↔
    p.2 ^ 2 = p.1 ^ 3 + E.A * p.1 ^ 2 + E.B * p.1
  rw [neg_pow_two]

/-- Nonsingularity of the model `y ^ 2 = x ^ 3 + A * x ^ 2 + B * x`, i.e. `B (A ^ 2 - 4B) ≠ 0`.
Over a field of characteristic not `2` this is equivalent to the nonvanishing of the
discriminant, see `Delta_eq`. -/
def IsValid (E : WeierstrassABCurve R) : Prop := E.B * (E.A ^ 2 - 4 * E.B) ≠ 0

/-- The same curve, as a Mathlib `WeierstrassCurve`. -/
def toWeierstrassCurve (E : WeierstrassABCurve R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := E.A
  a₃ := 0
  a₄ := E.B
  a₆ := 0

/-- The equation used here is the affine Weierstrass equation of the associated
`WeierstrassCurve`. -/
lemma equation_iff_weierstrass (E : WeierstrassABCurve R) (x y : R) :
    E.Equation x y ↔ E.toWeierstrassCurve.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [toWeierstrassCurve, Equation]
  constructor <;> intro h <;> linear_combination h

/-- The affine points used here are the affine solutions of the associated `WeierstrassCurve`. -/
lemma affinePoints_eq_weierstrass (E : WeierstrassABCurve R) :
    E.affinePoints = {p : R × R | E.toWeierstrassCurve.toAffine.Equation p.1 p.2} := by
  ext p
  exact E.equation_iff_weierstrass p.1 p.2

/-- The discriminant of `y ^ 2 = x ^ 3 + A * x ^ 2 + B * x` is `16 B ^ 2 (A ^ 2 - 4B)`. -/
lemma Delta_eq (E : WeierstrassABCurve R) :
    E.toWeierstrassCurve.Δ = 16 * E.B ^ 2 * (E.A ^ 2 - 4 * E.B) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, toWeierstrassCurve]
  ring

/-- Over a field of characteristic not `2`, `IsValid` is exactly the nonvanishing of Mathlib's
discriminant of the associated `WeierstrassCurve`. -/
lemma isValid_iff_Delta_ne_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (E : WeierstrassABCurve F) : E.IsValid ↔ E.toWeierstrassCurve.Δ ≠ 0 := by
  have h16 : (16 : F) ≠ 0 := by
    have : (16 : F) = 2 ^ 4 := by norm_num
    rw [this]
    exact pow_ne_zero _ h2
  have key : E.toWeierstrassCurve.Δ = 16 * E.B * (E.B * (E.A ^ 2 - 4 * E.B)) := by
    rw [Delta_eq]; ring
  rw [key]
  constructor
  · intro h
    refine mul_ne_zero (mul_ne_zero h16 ?_) h
    intro hB
    exact h (by rw [hB]; ring)
  · intro h hz
    exact h (by rw [hz, mul_zero])

end WeierstrassABCurve

end Elligator.Primitives.ECC
