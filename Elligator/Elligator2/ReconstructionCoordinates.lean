/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator2.Map

/-!
# The reconstruction coordinate `rbar` of Elligator 2

[Bernstein2013a], Theorem 7.3, reconstructs an input from a point `(x, y)` of the image by

```
rbar = sqrt (-x / ((x + A) u))   if y ∈ sqrt(F²) ,
rbar = sqrt (-(x + A) / (u x))   if y ∉ sqrt(F²) .
```

This file introduces `rbar` and proves, for a point satisfying the three conditions of Theorem 7.2,
all the intermediate steps of the paper's computation: `rbar` is defined, `1 + u rbar ^ 2` and
`vbar` are computed in both cases, `rbar ∈ R`, and finally `xbar = x` and `ybar = y`.

## Main results

* `ψOverRProps`: the three conditions of Theorem 7.2 on a point `(x, y)`.
* `rbar`: the reconstruction formula of Theorem 7.3.
* `v_rbar_of_isSqrtValue`, `v_rbar_of_not_isSqrtValue`: "so `1 + u rbar ^ 2 = A/(x + A)` so
  `vbar = -x - A`" and "so `1 + u rbar ^ 2 = -A/x` so `vbar = x`".
* `rbar_mem_R`: "In both cases we have `vbar ^ 2 + A vbar + B = x ^ 2 + A x + B ≠ 0` so
  `A ^ 2 u rbar ^ 2 ≠ B(1 + u rbar ^ 2) ^ 2`".
* `x_rbar`, `y_rbar`: "Consequently `xbar = x` and `ybar = y`".

## References

See [Bernstein2013a], Section 5.3, Theorem 7.
-/

@[expose] public section

namespace Elligator.Elligator2

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.SquareRootFunction
open Elligator.Primitives.ECC
open Elligator.Elligator2.CurveParameters

variable {F : Type*} [Field F] [DecidableEq F]

namespace PointData

variable (Q : PointData F)

/-- The three conditions of [Bernstein2013a], Theorem 7.2, describing the image `ψ(R)` inside
`E(F_q)`: `x ≠ -A`, `y = 0` implies `x = 0`, and `-u x (x + A)` is a square. -/
@[blueprint "def:psiOverRProps"
  (title := "The image conditions of Theorem 7.2")
  (statement := /--
  For a point $(x, y) \in E(\mathbb{F}_q)$ consider the three conditions
  \begin{itemize}
  \item $x \neq -A$,
  \item if $y = 0$ then $x = 0$, and
  \item $-u x (x + A)$ is a square in $\mathbb{F}_q$.
  \end{itemize}
  -/)]
def ψOverRProps : Prop :=
  Q.x + Q.A ≠ 0 ∧ (Q.y = 0 → Q.x = 0) ∧ IsSquare (-(Q.u * (Q.x * (Q.x + Q.A))))

/-- The square whose square root is the reconstructed input `rbar` of Theorem 7.3. -/
def rbarSquare : F :=
  if IsSqrtValue Q.sqrt Q.y then -Q.x / ((Q.x + Q.A) * Q.u) else -(Q.x + Q.A) / (Q.u * Q.x)

/-- The reconstructed input `rbar` of [Bernstein2013a], Theorem 7.3. -/
@[blueprint "def:rbar"
  (title := "The reconstruction $\\bar r$")
  (statement := /--
  In the situation of Definition 6, for $(x, y) \in \psi(R)$ define
  $$
  \bar r =
  \begin{cases}
    \sqrt{-x/((x + A)u)} & \text{if } y \in \sqrt{\mathbb{F}_q^2} ,\\
    \sqrt{-(x + A)/(ux)} & \text{if } y \notin \sqrt{\mathbb{F}_q^2} .
  \end{cases}
  $$
  -/)]
def rbar : F := Q.sqrt Q.rbarSquare

end PointData

namespace ReconstructionCoordinates

variable (Q : PointData F)

section basic

omit [DecidableEq F] in
/-- On the curve, a point with `y ≠ 0` has `x ≠ 0`. -/
lemma x_ne_zero_of_y_ne_zero (hcurve : Q.P ∈ Q.EOverF) (hy : Q.y ≠ 0) : Q.x ≠ 0 := by
  intro hx
  apply hy
  have h : Q.y ^ 2 = Q.toParamData.rhs Q.x := hcurve
  rw [ParamData.rhs_eq_mul_rhsFactor, hx, zero_mul] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

omit [DecidableEq F] in
/-- The quadratic factor `x ^ 2 + A x + B` is nonzero at a point with `y ≠ 0`. -/
lemma rhsFactor_x_ne_zero (hcurve : Q.P ∈ Q.EOverF) (hy : Q.y ≠ 0) :
    Q.toParamData.rhsFactor Q.x ≠ 0 := by
  intro h
  apply hy
  have hcurve' : Q.y ^ 2 = Q.toParamData.rhs Q.x := hcurve
  rw [ParamData.rhs_eq_mul_rhsFactor, h, mul_zero] at hcurve'
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hcurve'

variable [IsNonsquareParam Q.u] [IsSqrtFun Q.sqrt]

omit [DecidableEq F] [IsSqrtFun Q.sqrt] in
/-- The first branch of `rbar` is a square: `-x/((x + A)u) = (-u x (x + A))/(u(x + A)) ^ 2`. -/
lemma isSquare_first_branch (hprops : Q.ψOverRProps) :
    IsSquare (-Q.x / ((Q.x + Q.A) * Q.u)) := by
  obtain ⟨hxA, -, hsq⟩ := hprops
  obtain ⟨w, hw⟩ := hsq
  refine ⟨w / (Q.u * (Q.x + Q.A)), ?_⟩
  have hu := u_ne_zero Q.toParamData
  field_simp
  linear_combination hw

omit [DecidableEq F] [IsSqrtFun Q.sqrt] in
/-- The second branch of `rbar` is a square: `-(x + A)/(u x) = (-u x (x + A))/(u x) ^ 2`. -/
lemma isSquare_second_branch (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0) :
    IsSquare (-(Q.x + Q.A) / (Q.u * Q.x)) := by
  obtain ⟨hxA, -, hsq⟩ := hprops
  obtain ⟨w, hw⟩ := hsq
  refine ⟨w / (Q.u * Q.x), ?_⟩
  have hu := u_ne_zero Q.toParamData
  field_simp
  linear_combination hw

omit [IsSqrtFun Q.sqrt] in
lemma isSquare_rbarSquare (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0) : IsSquare Q.rbarSquare := by
  rw [PointData.rbarSquare]
  split
  · exact isSquare_first_branch Q hprops
  · exact isSquare_second_branch Q hprops hx

/-- `rbar` really is a square root of the displayed expression. -/
lemma rbar_sq (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0) : Q.rbar ^ 2 = Q.rbarSquare :=
  sq_sqrt Q.sqrt (isSquare_rbarSquare Q hprops hx)

omit [IsSqrtFun Q.sqrt] in
lemma rbarSquare_ne_zero (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0) : Q.rbarSquare ≠ 0 := by
  have hu := u_ne_zero Q.toParamData
  have hxA := hprops.1
  rw [PointData.rbarSquare]
  split
  · exact div_ne_zero (neg_ne_zero.mpr hx) (mul_ne_zero hxA hu)
  · exact div_ne_zero (neg_ne_zero.mpr hxA) (mul_ne_zero hu hx)

lemma rbar_ne_zero (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0) : Q.rbar ≠ 0 := by
  intro h
  refine rbarSquare_ne_zero Q hprops hx ?_
  rw [← rbar_sq Q hprops hx, h]
  ring

end basic

section principal

variable [IsRegularABParam Q.A Q.B] [IsNonsquareParam Q.u] [IsSqrtFun Q.sqrt]

omit [IsRegularABParam Q.A Q.B] [IsNonsquareParam Q.u] [IsSqrtFun Q.sqrt] in
/-- The first branch of the definition of `rbar`. -/
lemma rbarSquare_of_isSqrtValue (hval : IsSqrtValue Q.sqrt Q.y) :
    Q.rbarSquare = -Q.x / ((Q.x + Q.A) * Q.u) := by
  simp [PointData.rbarSquare, hval]

omit [IsRegularABParam Q.A Q.B] [IsNonsquareParam Q.u] [IsSqrtFun Q.sqrt] in
/-- The second branch of the definition of `rbar`. -/
lemma rbarSquare_of_not_isSqrtValue (hval : ¬IsSqrtValue Q.sqrt Q.y) :
    Q.rbarSquare = -(Q.x + Q.A) / (Q.u * Q.x) := by
  simp [PointData.rbarSquare, hval]

omit [IsRegularABParam Q.A Q.B] in
/-- First case of Theorem 7: if `y ∈ sqrt(F²)` then `1 + u rbar ^ 2 = A/(x + A)`. -/
lemma one_add_u_rbar_sq_of_isSqrtValue (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0)
    (hval : IsSqrtValue Q.sqrt Q.y) :
    1 + Q.u * Q.rbar ^ 2 = Q.A / (Q.x + Q.A) := by
  have hu := u_ne_zero Q.toParamData
  have hxA := hprops.1
  rw [rbar_sq Q hprops hx, rbarSquare_of_isSqrtValue Q hval]
  field_simp
  ring

/-- First case of Theorem 7: if `y ∈ sqrt(F²)` then `vbar = -x - A`. -/
lemma v_rbar_of_isSqrtValue (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0)
    (hval : IsSqrtValue Q.sqrt Q.y) :
    Q.toParamData.v Q.rbar = -(Q.x + Q.A) := by
  have hA := A_ne_zero Q.toParamData
  have hxA := hprops.1
  rw [ParamData.v, one_add_u_rbar_sq_of_isSqrtValue Q hprops hx hval]
  field_simp

omit [IsRegularABParam Q.A Q.B] in
/-- Second case of Theorem 7: if `y ∉ sqrt(F²)` then `1 + u rbar ^ 2 = -A/x`. -/
lemma one_add_u_rbar_sq_of_not_isSqrtValue (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0)
    (hval : ¬IsSqrtValue Q.sqrt Q.y) :
    1 + Q.u * Q.rbar ^ 2 = -Q.A / Q.x := by
  have hu := u_ne_zero Q.toParamData
  rw [rbar_sq Q hprops hx, rbarSquare_of_not_isSqrtValue Q hval]
  field_simp
  ring

/-- Second case of Theorem 7: if `y ∉ sqrt(F²)` then `vbar = x`. -/
lemma v_rbar_of_not_isSqrtValue (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0)
    (hval : ¬IsSqrtValue Q.sqrt Q.y) :
    Q.toParamData.v Q.rbar = Q.x := by
  have hA := A_ne_zero Q.toParamData
  rw [ParamData.v, one_add_u_rbar_sq_of_not_isSqrtValue Q hprops hx hval]
  field_simp

/-- In both cases `1 + u rbar ^ 2 ≠ 0`. -/
lemma one_add_u_rbar_sq_ne_zero (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0) :
    1 + Q.u * Q.rbar ^ 2 ≠ 0 := by
  have hA := A_ne_zero Q.toParamData
  have hxA := hprops.1
  by_cases hval : IsSqrtValue Q.sqrt Q.y
  · rw [one_add_u_rbar_sq_of_isSqrtValue Q hprops hx hval]
    exact div_ne_zero hA hxA
  · rw [one_add_u_rbar_sq_of_not_isSqrtValue Q hprops hx hval]
    exact div_ne_zero (neg_ne_zero.mpr hA) hx

/-- In both cases `vbar ^ 2 + A vbar + B = x ^ 2 + A x + B`. -/
lemma rhsFactor_v_rbar (hprops : Q.ψOverRProps) (hx : Q.x ≠ 0) :
    Q.toParamData.rhsFactor (Q.toParamData.v Q.rbar) = Q.toParamData.rhsFactor Q.x := by
  by_cases hval : IsSqrtValue Q.sqrt Q.y
  · rw [v_rbar_of_isSqrtValue Q hprops hx hval, ParamData.rhsFactor_eq, ParamData.rhsFactor_eq]
    ring
  · rw [v_rbar_of_not_isSqrtValue Q hprops hx hval]

/-- The reconstructed input is admissible: this is the paper's step "In both cases we have
`vbar ^ 2 + A vbar + B = x ^ 2 + A x + B ≠ 0` so `A ^ 2 u rbar ^ 2 ≠ B(1 + u rbar ^ 2) ^ 2`". -/
lemma rbar_mem_R_of_y_ne_zero (hcurve : Q.P ∈ Q.EOverF) (hprops : Q.ψOverRProps) (hy : Q.y ≠ 0) :
    Q.rbar ∈ Q.toParamData.R := by
  have hx := x_ne_zero_of_y_ne_zero Q hcurve hy
  refine (mem_R_iff_rhsFactor_v_ne_zero Q.toParamData (one_add_u_rbar_sq_ne_zero Q hprops hx)).mpr
    ?_
  rw [rhsFactor_v_rbar Q hprops hx]
  exact rhsFactor_x_ne_zero Q hcurve hy

end principal

section decode

variable [Fintype F] [IsOddCard F] [IsRegularABParam Q.A Q.B] [IsNonsquareParam Q.u]
  [IsSqrtFun Q.sqrt]

omit [IsOddCard F] [IsRegularABParam Q.A Q.B] [IsNonsquareParam Q.u] [IsSqrtFun Q.sqrt] in
/-- The quadratic character of the right hand side at a point of the curve with `y ≠ 0`. -/
lemma χ_rhs_x_eq_one (hcurve : Q.P ∈ Q.EOverF) (hy : Q.y ≠ 0) :
    χ (Q.toParamData.rhs Q.x) = 1 := by
  have h : Q.toParamData.rhs Q.x = Q.y ^ 2 := (hcurve : Q.y ^ 2 = _).symm
  rw [h]
  exact χ_sq hy

/-- First case of Theorem 7: "`χ(vbar) = χ(-x - A) = χ(u x) = -χ(x)`". -/
lemma χ_v_rbar_of_isSqrtValue (hcurve : Q.P ∈ Q.EOverF) (hprops : Q.ψOverRProps) (hy : Q.y ≠ 0)
    (hval : IsSqrtValue Q.sqrt Q.y) :
    χ (Q.toParamData.v Q.rbar) = -χ Q.x := by
  have hx := x_ne_zero_of_y_ne_zero Q hcurve hy
  have hxA := hprops.1
  have hu := u_ne_zero Q.toParamData
  have hS : -(Q.u * (Q.x * (Q.x + Q.A))) = -(Q.x + Q.A) * (Q.u * Q.x) := by ring
  have hne : -(Q.u * (Q.x * (Q.x + Q.A))) ≠ 0 := by
    rw [hS]
    exact mul_ne_zero (neg_ne_zero.mpr hxA) (mul_ne_zero hu hx)
  have h1 : χ (-(Q.u * (Q.x * (Q.x + Q.A)))) = 1 := χ_a_eq_one hne hprops.2.2
  rw [hS, χ_mul, χ_mul, χ_u_eq_neg_one Q.toParamData] at h1
  have hxx : χ Q.x * χ Q.x = 1 := χ_mul_self_eq_one hx
  rw [v_rbar_of_isSqrtValue Q hprops hx hval]
  linear_combination (-χ Q.x) * h1 + (-χ (-(Q.x + Q.A))) * hxx

/-- First case of Theorem 7: "`epsbar = χ(vbar ^ 3 + A vbar ^ 2 + B vbar)
= -χ(x ^ 3 + A x ^ 2 + B x) = -1`". -/
lemma ε_rbar_of_isSqrtValue (hcurve : Q.P ∈ Q.EOverF) (hprops : Q.ψOverRProps) (hy : Q.y ≠ 0)
    (hval : IsSqrtValue Q.sqrt Q.y) :
    Q.toParamData.ε Q.rbar = -1 := by
  have hx := x_ne_zero_of_y_ne_zero Q hcurve hy
  have hrhs := χ_rhs_x_eq_one Q hcurve hy
  rw [ParamData.rhs_eq_mul_rhsFactor, χ_mul] at hrhs
  rw [ParamData.ε, ParamData.rhs_eq_mul_rhsFactor, χ_mul,
    χ_v_rbar_of_isSqrtValue Q hcurve hprops hy hval, rhsFactor_v_rbar Q hprops hx]
  linear_combination -hrhs

omit [IsOddCard F] in
/-- Second case of Theorem 7: "`vbar ^ 3 + A vbar ^ 2 + B vbar = x ^ 3 + A x ^ 2 + B x`
so `epsbar = 1`". -/
lemma ε_rbar_of_not_isSqrtValue (hcurve : Q.P ∈ Q.EOverF) (hprops : Q.ψOverRProps) (hy : Q.y ≠ 0)
    (hval : ¬IsSqrtValue Q.sqrt Q.y) :
    Q.toParamData.ε Q.rbar = 1 := by
  have hx := x_ne_zero_of_y_ne_zero Q hcurve hy
  rw [ParamData.ε, v_rbar_of_not_isSqrtValue Q hprops hx hval]
  exact χ_rhs_x_eq_one Q hcurve hy

/-- The paper's conclusion "Consequently `xbar = x`" of Theorem 7. -/
lemma x_rbar (hcurve : Q.P ∈ Q.EOverF) (hprops : Q.ψOverRProps) (hy : Q.y ≠ 0) :
    Q.toParamData.x Q.rbar = Q.x := by
  have hx := x_ne_zero_of_y_ne_zero Q hcurve hy
  by_cases hval : IsSqrtValue Q.sqrt Q.y
  · rw [x_of_ε_eq_neg_one Q.toParamData (ε_rbar_of_isSqrtValue Q hcurve hprops hy hval),
      v_rbar_of_isSqrtValue Q hprops hx hval]
    ring
  · rw [x_of_ε_eq_one Q.toParamData (ε_rbar_of_not_isSqrtValue Q hcurve hprops hy hval),
      v_rbar_of_not_isSqrtValue Q hprops hx hval]

/-- The paper's conclusion "and `ybar = y`" of Theorem 7. -/
lemma y_rbar (hcurve : Q.P ∈ Q.EOverF) (hprops : Q.ψOverRProps) (hy : Q.y ≠ 0) :
    Q.toParamData.y Q.rbar = Q.y := by
  have hrhs : Q.toParamData.rhs Q.x = Q.y ^ 2 := (hcurve : Q.y ^ 2 = _).symm
  rw [ParamData.y, x_rbar Q hcurve hprops hy, hrhs]
  by_cases hval : IsSqrtValue Q.sqrt Q.y
  · rw [ε_rbar_of_isSqrtValue Q hcurve hprops hy hval, show Q.sqrt (Q.y ^ 2) = Q.y from hval]
    ring
  · rw [ε_rbar_of_not_isSqrtValue Q hcurve hprops hy hval,
      sqrt_sq_eq_neg_of_not_isSqrtValue Q.sqrt hval]
    ring

omit [Fintype F] [IsOddCard F] [IsRegularABParam Q.A Q.B] [IsNonsquareParam Q.u] in
/-- If `y = 0` then the reconstruction gives `rbar = 0`, whose image is the point `(0, 0)`. -/
lemma rbar_of_y_eq_zero (hprops : Q.ψOverRProps) (hy : Q.y = 0) : Q.rbar = 0 := by
  have hx : Q.x = 0 := hprops.2.1 hy
  have hval : IsSqrtValue Q.sqrt Q.y := by
    rw [IsSqrtValue, hy]
    simpa using sqrt_zero Q.sqrt
  rw [PointData.rbar, rbarSquare_of_isSqrtValue Q hval, hx]
  simpa using sqrt_zero Q.sqrt

omit [Fintype F] [IsOddCard F] in
/-- The reconstructed input `rbar` is admissible, also in the degenerate case `y = 0`. -/
lemma rbar_mem_R (hcurve : Q.P ∈ Q.EOverF) (hprops : Q.ψOverRProps) :
    Q.rbar ∈ Q.toParamData.R := by
  rcases eq_or_ne Q.y 0 with hy | hy
  · rw [rbar_of_y_eq_zero Q hprops hy]
    exact zero_mem_R Q.toParamData
  · exact rbar_mem_R_of_y_ne_zero Q hcurve hprops hy

/-- The paper's conclusion of Theorem 7.3: `ψ(rbar) = (x, y)`. -/
@[blueprint "lemma:psi_rbar"
  (title := "$\\psi(\\bar r) = (x, y)$")
  (statement := /--
  In the situation of Theorem 7, let $(x, y) \in E(\mathbb{F}_q)$ satisfy the three conditions of
  Theorem 7.2. Then $\bar r$ is defined, $\bar r \in R$, and $\psi(\bar r) = (x, y)$.
  -/)]
lemma ψ_rbar (hcurve : Q.P ∈ Q.EOverF) (hprops : Q.ψOverRProps) :
    Q.toParamData.ψ Q.rbar = Q.P := by
  rcases eq_or_ne Q.y 0 with hy | hy
  · have hx : Q.x = 0 := hprops.2.1 hy
    rw [rbar_of_y_eq_zero Q hprops hy, ParamData.ψ_zero, Q.P_eq, hx, hy]
  · have hx := x_ne_zero_of_y_ne_zero Q hcurve hy
    rw [ParamData.ψ_of_ne_zero Q.toParamData (rbar_ne_zero Q hprops hx),
      x_rbar Q hcurve hprops hy, y_rbar Q hcurve hprops hy, Q.P_eq]

end decode

end ReconstructionCoordinates

end Elligator.Elligator2
