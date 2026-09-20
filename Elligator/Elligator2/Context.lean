/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Context
public import Elligator.SquareRootFunction
public import Elligator.Primitives.ECC.WeierstrassABCurve

/-!
# Bundled data and hypotheses for Elligator 2

Section 5 of [Bernstein2013a] fixes, once and for all,

* an odd prime power `q`, i.e. a finite field `F` of odd characteristic (`IsOddCard F`),
* curve coefficients `A`, `B` with `AB(A ^ 2 - 4B) ≠ 0` (`IsRegularABParam`),
* a non-square `u` (`IsNonsquareParam`),
* a square-root function `sqrt` (`IsSqrtFun`),

and then studies the map `ψ` on the set `R` of admissible inputs.

The same two mechanisms as in `Elligator.Context` are used: the data is bundled into
`ParamData`, `MapData` and `PointData`, whereas the hypotheses are unbundled into one class per
hypothesis, so that a statement lists exactly the hypotheses it needs and instance resolution
supplies them.

## Main definitions

* `IsRegularABParam A B`: the curve condition `AB(A ^ 2 - 4B) ≠ 0` of Theorem 5.
* `IsNonsquareDisc A B`: the extra condition that `A ^ 2 - 4B` is a non-square, used for `R = F`.
* `ParamData`: the tuple `(A, B, u, sqrt)` parametrizing Elligator 2.
* `ParamData.curve`, `ParamData.EOverF`: the curve `y ^ 2 = x ^ 3 + A x ^ 2 + B x` and its set
  of affine points `E(F_q)`.
* `ParamData.R`: the set of admissible inputs
  `{r : 1 + u r ^ 2 ≠ 0, A ^ 2 u r ^ 2 ≠ B (1 + u r ^ 2) ^ 2}`.

## References

See [Bernstein2013a], Section 5.2, Theorem 5.
-/

@[expose] public section

namespace Elligator.Elligator2

open Elligator.Primitives.ECC

variable {F : Type*} [Field F]

/-- The curve coefficients satisfy `AB(A ^ 2 - 4B) ≠ 0`, the standing hypothesis of Theorem 5.

The factor `B(A ^ 2 - 4B)` is the nonsingularity of `y ^ 2 = x ^ 3 + A x ^ 2 + B x`; the extra
factor `A` excludes the curves of `j`-invariant `1728`, for which Elligator 2 is not defined. -/
class IsRegularABParam {F : Type*} [Field F] (A B : F) : Prop where
  /-- The coefficients satisfy `A * B * (A ^ 2 - 4 * B) ≠ 0`. -/
  AB_disc_ne_zero : A * B * (A ^ 2 - 4 * B) ≠ 0

/-- The discriminant `A ^ 2 - 4B` is a non-square.

Together with `q ≡ 1 (mod 4)` this is the hypothesis under which the admissible set `R` is all
of `F`, see Theorem 5 and Theorem 8. -/
class IsNonsquareDisc {F : Type*} [Field F] (A B : F) : Prop where
  /-- `A ^ 2 - 4 * B` is not a square. -/
  disc_nonsquare : ¬IsSquare (A ^ 2 - 4 * B)

export IsRegularABParam (AB_disc_ne_zero)
export IsNonsquareDisc (disc_nonsquare)

/-- The parameters of Elligator 2, bundled: the curve coefficients `A`, `B`, the non-square `u`
and the square-root function `sqrt`. -/
structure ParamData (F : Type*) [Field F] where
  /-- The coefficient of `x ^ 2` in `y ^ 2 = x ^ 3 + A x ^ 2 + B x`. -/
  A : F
  /-- The coefficient of `x` in `y ^ 2 = x ^ 3 + A x ^ 2 + B x`. -/
  B : F
  /-- The non-square parametrizing the map. -/
  u : F
  /-- The square-root function parametrizing the map. -/
  sqrt : F → F

namespace ParamData

variable (P : ParamData F)

/-- The Weierstrass curve `y ^ 2 = x ^ 3 + A x ^ 2 + B x` selected by the parameters. -/
def curve : WeierstrassABCurve F := ⟨P.A, P.B⟩

@[simp] lemma curve_A : P.curve.A = P.A := rfl

@[simp] lemma curve_B : P.curve.B = P.B := rfl

/-- The right hand side `t ^ 3 + A t ^ 2 + B t` of the curve equation. -/
def rhs (t : F) : F := P.curve.rhs t

/-- The quadratic factor `t ^ 2 + A t + B` of the right hand side. -/
def rhsFactor (t : F) : F := P.curve.rhsFactor t

lemma rhs_eq (t : F) : P.rhs t = t ^ 3 + P.A * t ^ 2 + P.B * t := rfl

lemma rhsFactor_eq (t : F) : P.rhsFactor t = t ^ 2 + P.A * t + P.B := rfl

lemma rhs_eq_mul_rhsFactor (t : F) : P.rhs t = t * P.rhsFactor t :=
  P.curve.rhs_eq_mul_rhsFactor t

/-- The set of affine points `E(F_q)` of the Elligator 2 curve. -/
@[blueprint "def:E2OverF"
  (title := "The point set $E(\\mathbb{F}_q)$ of Elligator 2")
  (statement := /--
  For $A, B \in \mathbb{F}_q$ with $AB(A ^ 2 - 4B) \neq 0$, let
  $$
  E(\mathbb{F}_q) = \{(x, y) \in \mathbb{F}_q \times \mathbb{F}_q :
    y ^ 2 = x ^ 3 + A x ^ 2 + B x\}
  $$
  be the set of affine points of the Weierstrass curve $E$.
  -/)]
def EOverF : Set (F × F) := P.curve.affinePoints

lemma mem_EOverF_iff (p : F × F) : p ∈ P.EOverF ↔ p.2 ^ 2 = P.rhs p.1 := Iff.rfl

/-- The set `R` of admissible inputs of Theorem 5. -/
@[blueprint "def:R"
  (title := "The admissible set $R$")
  (statement := /--
  In the situation of Theorem 5, define $R$ as the set
  $$
  \{r \in \mathbb{F}_q : 1 + u r ^ 2 \neq 0, \ A ^ 2 u r ^ 2 \neq B(1 + u r ^ 2) ^ 2\} .
  $$
  -/)]
def R : Set F :=
  {r : F | 1 + P.u * r ^ 2 ≠ 0 ∧ P.A ^ 2 * P.u * r ^ 2 ≠ P.B * (1 + P.u * r ^ 2) ^ 2}

lemma mem_R_iff (r : F) :
    r ∈ P.R ↔ 1 + P.u * r ^ 2 ≠ 0 ∧ P.A ^ 2 * P.u * r ^ 2 ≠ P.B * (1 + P.u * r ^ 2) ^ 2 :=
  Iff.rfl

end ParamData

/-- The parameters together with an admissible input `r ∈ R`: the data of Theorem 5.

The membership in `R` is data rather than a hypothesis: it is exactly the domain on which the
paper defines `ψ`. -/
structure MapData (F : Type*) [Field F] extends ParamData F where
  /-- The input of the Elligator 2 map. -/
  r : F
  /-- The input is admissible. -/
  r_mem_R : r ∈ toParamData.R

/-- The parameters together with a point of the plane: the data of Theorem 7. -/
structure PointData (F : Type*) [Field F] extends ParamData F where
  /-- The point. -/
  P : F × F

namespace ParamData

variable (P : ParamData F)

/-- The `MapData` assembled from the parameters and an admissible input `r ∈ R`. -/
@[reducible]
def withInput (r : F) (hr : r ∈ P.R) : MapData F :=
  { toParamData := P, r := r, r_mem_R := hr }

/-- The `PointData` assembled from the parameters and a point of the plane. -/
@[reducible]
def withPoint (Q : F × F) : PointData F := { toParamData := P, P := Q }

end ParamData

namespace MapData

variable (M : MapData F)

/-- The input `r` replaced by `-r`, the parameters kept. Admissibility only depends on `r ^ 2`. -/
def neg : MapData F where
  toParamData := M.toParamData
  r := -M.r
  r_mem_R := by
    have h := M.r_mem_R
    rw [ParamData.mem_R_iff] at h ⊢
    rwa [neg_pow_two]

@[simp] lemma neg_r : M.neg.r = -M.r := rfl

@[simp] lemma neg_toParamData : M.neg.toParamData = M.toParamData := rfl

end MapData

namespace PointData

variable (Q : PointData F)

/-- The `x`-coordinate of the point. -/
def x : F := Q.P.1

/-- The `y`-coordinate of the point. -/
def y : F := Q.P.2

lemma P_eq : Q.P = (Q.x, Q.y) := rfl

end PointData

end Elligator.Elligator2
