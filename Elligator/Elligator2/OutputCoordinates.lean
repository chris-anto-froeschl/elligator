/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator2.AuxiliaryCoordinates

/-!
# The output coordinates `x` and `y` of Elligator 2

[Bernstein2013a], Theorem 5, defines for each nonzero `r ∈ R`

```
x = ε v - (1 - ε) A / 2,   y = -ε * sqrt (x ^ 3 + A x ^ 2 + B x) ,
```

and the last two steps of its proof show that `x ^ 3 + A x ^ 2 + B x` is a nonzero square with
`x ≠ 0`, and that `y` is defined, nonzero and satisfies `y ^ 2 = x ^ 3 + A x ^ 2 + B x`.

The proof splits into the two cases `ε = 1` (where `x = v`) and `ε = -1` (where
`x = -v - A = v u r ^ 2`), exactly as in the paper.

## Main results

* `x_of_ε_eq_one`, `x_of_ε_eq_neg_one`, `x_eq_v_mul_u_mul_sq`: the two cases for `x`.
* `x_mul_x_add_A`, `rhsFactor_x_eq`: the paper's computation `x(x + A) = v(v + A)`, hence
  `x ^ 2 + A x + B = v ^ 2 + A v + B`.
* `x_ne_zero`, `χ_rhs_x`, `isSquare_rhs_x`: "`x ^ 3 + A x ^ 2 + B x` is a nonzero square and
  `x ≠ 0`".
* `y_sq`, `y_ne_zero`: "`y` is defined, `y ^ 2 = x ^ 3 + A x ^ 2 + B x`, and `y ≠ 0`".
* `x_add_A_ne_zero`, `isSquare_neg_u_mul_x_mul_x_add_A`: the two conditions of Theorem 7.2 that
  are already visible here.

## References

See [Bernstein2013a], Section 5.2, Theorem 5.
-/

@[expose] public section

namespace Elligator.Elligator2

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.SquareRootFunction
open Elligator.Elligator2.CurveParameters

variable {F : Type*} [Field F]

namespace ParamData

variable (P : ParamData F) [Fintype F] [DecidableEq F]

/-- The output coordinate `x = ε v - (1 - ε) A / 2` of Theorem 5. -/
@[blueprint "def:x2"
  (title := "The output coordinate $x$")
  (statement := /--
  In the situation of Theorem 5, for each nonzero $r \in R$ define
  $$
  x = \varepsilon v - (1 - \varepsilon)A/2 .
  $$
  -/)]
def x (r : F) : F := P.ε r * P.v r - (1 - P.ε r) * P.A / 2

/-- The output coordinate `y = -ε sqrt (x ^ 3 + A x ^ 2 + B x)` of Theorem 5. -/
@[blueprint "def:y2"
  (title := "The output coordinate $y$")
  (statement := /--
  In the situation of Theorem 5, for each nonzero $r \in R$ define
  $$
  y = -\varepsilon \sqrt{x ^ 3 + A x ^ 2 + B x} .
  $$
  -/)]
def y (r : F) : F := -P.ε r * P.sqrt (P.rhs (P.x r))

end ParamData

namespace CurveParameters

variable (P : ParamData F) {r : F} [Fintype F] [DecidableEq F]

section cases

/-- First case of Theorem 5: if `ε = 1` then `x = v`. -/
lemma x_of_ε_eq_one (h : P.ε r = 1) : P.x r = P.v r := by
  rw [ParamData.x, h]
  ring

/-- Second case of Theorem 5: if `ε = -1` then `x = -v - A`. -/
lemma x_of_ε_eq_neg_one [IsOddCard F] (h : P.ε r = -1) : P.x r = -P.v r - P.A := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card
  rw [ParamData.x, h]
  field_simp
  ring

/-- Second case of Theorem 5: if `ε = -1` then `x = -v - A = v u r ^ 2`. -/
lemma x_eq_v_mul_u_mul_sq [IsOddCard F] (hw : 1 + P.u * r ^ 2 ≠ 0) (h : P.ε r = -1) :
    P.x r = P.v r * P.u * r ^ 2 := by
  rw [x_of_ε_eq_neg_one P h]
  linear_combination -v_add_A P hw

/-- The paper's computation `x(x + A) = v(v + A)`, valid in both cases. -/
lemma x_mul_x_add_A [IsOddCard F] [IsRegularABParam P.A P.B] (hr : r ∈ P.R) :
    P.x r * (P.x r + P.A) = P.v r * (P.v r + P.A) := by
  rcases ε_eq_one_or_eq_neg_one P hr with h | h
  · rw [x_of_ε_eq_one P h]
  · rw [x_of_ε_eq_neg_one P h]
    ring

/-- Consequently `x ^ 2 + A x + B = v ^ 2 + A v + B`. -/
lemma rhsFactor_x_eq [IsOddCard F] [IsRegularABParam P.A P.B] (hr : r ∈ P.R) :
    P.rhsFactor (P.x r) = P.rhsFactor (P.v r) := by
  have h := x_mul_x_add_A P hr
  rw [ParamData.rhsFactor_eq, ParamData.rhsFactor_eq]
  linear_combination h

/-- `x ≠ 0` for every nonzero admissible `r`. -/
lemma x_ne_zero [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u]
    (hr : r ∈ P.R) (hr0 : r ≠ 0) : P.x r ≠ 0 := by
  rcases ε_eq_one_or_eq_neg_one P hr with h | h
  · rw [x_of_ε_eq_one P h]
    exact v_ne_zero P hr.1
  · rw [x_eq_v_mul_u_mul_sq P hr.1 h]
    exact mul_ne_zero (mul_ne_zero (v_ne_zero P hr.1) (u_ne_zero P)) (pow_ne_zero 2 hr0)

end cases

section square

variable [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u]

omit [IsRegularABParam P.A P.B] in
/-- In the second case `χ(x) = χ(v)χ(u) = -χ(v)`. -/
lemma χ_x_of_ε_eq_neg_one (hr : r ∈ P.R) (hr0 : r ≠ 0) (h : P.ε r = -1) :
    χ (P.x r) = -χ (P.v r) := by
  rw [x_eq_v_mul_u_mul_sq P hr.1 h, χ_of_a_eq_χ_a_mul_b_pow_two hr0, χ_mul, χ_u_eq_neg_one P]
  ring

/-- The paper's step "`x ^ 3 + A x ^ 2 + B x` is a nonzero square". -/
@[blueprint "lemma:χ_rhs_x"
  (title := "$\\chi(x ^ 3 + A x ^ 2 + B x) = 1$")
  (statement := /--
  In the situation of Theorem 5, let $r \in R$ with $r \neq 0$. There are two cases. First case:
  $\varepsilon = 1$, i.e. $v ^ 3 + A v ^ 2 + B v$ is a nonzero square. Then $x = v$, so
  $x ^ 3 + A x ^ 2 + B x$ is a nonzero square. Second case: $\varepsilon = -1$. Then
  $x = -v - A = v u r ^ 2$ and $\chi(x) = \chi(v)\chi(u) = -\chi(v)$; furthermore
  $x(x + A) = v(v + A)$, so $x ^ 2 + A x + B = v ^ 2 + A v + B$ and therefore
  $\chi(x ^ 3 + A x ^ 2 + B x) = -\chi(v ^ 3 + A v ^ 2 + B v) = -\varepsilon = 1$.
  -/)]
lemma χ_rhs_x (hr : r ∈ P.R) (hr0 : r ≠ 0) : χ (P.rhs (P.x r)) = 1 := by
  rcases ε_eq_one_or_eq_neg_one P hr with h | h
  · rw [x_of_ε_eq_one P h]
    exact h
  · -- `χ (rhs x) = χ x * χ (rhsFactor x) = -χ v * χ (rhsFactor v) = -ε = 1`
    rw [ParamData.rhs_eq_mul_rhsFactor, χ_mul, rhsFactor_x_eq P hr,
      χ_x_of_ε_eq_neg_one P hr hr0 h]
    have hε : P.ε r = χ (P.v r) * χ (P.rhsFactor (P.v r)) := by
      rw [ParamData.ε, ParamData.rhs_eq_mul_rhsFactor, χ_mul]
    rw [h] at hε
    linear_combination hε

lemma rhs_x_ne_zero (hr : r ∈ P.R) (hr0 : r ≠ 0) : P.rhs (P.x r) ≠ 0 := by
  intro h
  have := χ_rhs_x P hr hr0
  rw [h, χ_zero] at this
  exact zero_ne_one this

lemma isSquare_rhs_x (hr : r ∈ P.R) (hr0 : r ≠ 0) : IsSquare (P.rhs (P.x r)) :=
  (χ_eq_one_iff_isSquare_of_odd_card (rhs_x_ne_zero P hr hr0)).mp (χ_rhs_x P hr hr0)

end square

section output

variable [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u] [IsSqrtFun P.sqrt]

/-- The paper's step "`y` is defined and `y ^ 2 = x ^ 3 + A x ^ 2 + B x`". -/
@[blueprint "lemma:y2_sq"
  (title := "$y ^ 2 = x ^ 3 + A x ^ 2 + B x$")
  (statement := /--
  In the situation of Theorem 5, $x ^ 3 + A x ^ 2 + B x$ is a nonzero square, so
  $\sqrt{x ^ 3 + A x ^ 2 + B x}$ is defined; all factors in
  $y = -\varepsilon\sqrt{x ^ 3 + A x ^ 2 + B x}$ are nonzero, and
  $y ^ 2 = x ^ 3 + A x ^ 2 + B x$.
  -/)]
lemma y_sq (hr : r ∈ P.R) (hr0 : r ≠ 0) : P.y r ^ 2 = P.rhs (P.x r) := by
  rw [ParamData.y, mul_pow, neg_pow_two, ε_sq P hr, one_mul,
    sq_sqrt P.sqrt (isSquare_rhs_x P hr hr0)]

lemma y_ne_zero (hr : r ∈ P.R) (hr0 : r ≠ 0) : P.y r ≠ 0 := by
  rw [ParamData.y]
  refine mul_ne_zero (neg_ne_zero.mpr (ε_ne_zero P hr)) ?_
  exact sqrt_ne_zero P.sqrt (isSquare_rhs_x P hr hr0) (rhs_x_ne_zero P hr hr0)

/-- The coordinates produced from a nonzero admissible input satisfy the curve equation. -/
lemma equation_x_y (hr : r ∈ P.R) (hr0 : r ≠ 0) : P.curve.Equation (P.x r) (P.y r) :=
  y_sq P hr hr0

end output

section image

variable [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u]

/-- `x ≠ -A`, the first condition of Theorem 7.2. -/
lemma x_add_A_ne_zero (hr : r ∈ P.R) (hr0 : r ≠ 0) : P.x r + P.A ≠ 0 := by
  rcases ε_eq_one_or_eq_neg_one P hr with h | h
  · -- `x = v`, and `v + A = -(v u r ^ 2) ≠ 0`
    rw [x_of_ε_eq_one P h, v_add_A P hr.1, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (v_ne_zero P hr.1) (u_ne_zero P)) (pow_ne_zero 2 hr0)
  · -- `x = -v - A`, so `x + A = -v ≠ 0`
    rw [x_of_ε_eq_neg_one P h]
    simpa using v_ne_zero P hr.1

omit [IsNonsquareParam P.u] in
/-- `-u x (x + A) = u ^ 2 v ^ 2 r ^ 2` is a square, the third condition of Theorem 7.2. -/
lemma isSquare_neg_u_mul_x_mul_x_add_A (hr : r ∈ P.R) :
    IsSquare (-(P.u * (P.x r * (P.x r + P.A)))) := by
  have h : -(P.u * (P.x r * (P.x r + P.A))) = (P.u * P.v r * r) ^ 2 := by
    rw [x_mul_x_add_A P hr, v_mul_v_add_A P hr.1]
    ring
  exact ⟨P.u * P.v r * r, by rw [h]; ring⟩

end image

section negation

@[simp]
lemma x_neg : P.x (-r) = P.x r := by
  rw [ParamData.x, ParamData.x, v_neg, ε_neg]

@[simp]
lemma y_neg : P.y (-r) = P.y r := by
  rw [ParamData.y, ParamData.y, x_neg, ε_neg]

end negation

end CurveParameters

end Elligator.Elligator2
