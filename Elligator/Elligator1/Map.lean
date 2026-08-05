/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.sProperties
public import Elligator.Elligator1.cProperties
public import Elligator.Elligator1.dProperties
public import Elligator.Elligator1.EdwardsCurve
public import Elligator.Elligator1.uProperties
public import Elligator.Elligator1.vProperties
public import Elligator.Elligator1.XProperties
public import Elligator.Elligator1.YProperties
public import Elligator.Elligator1.xProperties
public import Elligator.Elligator1.yProperties

/-!
# Map

This file formalizes the construction and well-definedness results in Theorem 1 of the Elligator
paper. For a field input `t ≠ ±1`, the auxiliary quantities `u`, `v`, `X`, and `Y` determine a
point `(x, y)` on the complete Edwards curve. The exceptional inputs `t = ±1` are incorporated by
`ϕ`, which sends both to `(0, 1)`.

## Main results

* `u_defined`, `Y_defined`, `x_defined`, `y_defined`: the denominators in the paper's formulas
  are nonzero, so the displayed expressions are defined.
* `map_fulfills_helper_equation`: the auxiliary coordinates satisfy `Y² = X⁵ + (r² - 2)X³ + X`.
* `variable_mul_ne_zero`: the nonvanishing assertion `u * v * X * Y * x * (y + 1) ≠ 0`
  from Theorem 1.
* `map_fulfills_curve_equation`: the resulting `(x, y)` satisfies the Edwards curve equation.
* `ϕ`: Definition 2's total map from field elements to points on the Edwards curve.

## References

See [bernstein2013a], Section 3.2, Theorem 1 and Definition 2.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {s : F} (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
variable {q : ℕ} (hq_card : Fintype.card F = q) (hq_primePow : IsPrimePow q) (hq_mod : q % 4 = 3)

omit [Fintype F] in
@[blueprint
  (title := "$u$ is defined")
  (statement := /--
  In the situation of Theorem 1, for each $t \in \mathbb{F}_q \setminus \{\pm 1\}$ the
  denominator of
  $$
  u = (1 - t)/(1 + t)
  $$
  is nonzero, i.e. $1 + t \neq 0$.
  -/)]
theorem u_defined :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, (1 + t.val) ≠ 0 := by
    intro t
    exact FiniteFieldBasic.one_add_t_ne_zero t

@[blueprint
  (title := "$Y$ is defined")
  (statement := /--
  In the situation of Theorem 1, the quantity
  $$
  Y = (\chi(v)v)^{(q+1)/4}\chi(v)\chi(u^2 + 1/c^2)
  $$
  is defined for each $t \in \mathbb{F}_q \setminus \{\pm 1\}$, since $c^2 \neq 0$.
  -/)]
theorem Y_defined
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (c s)^2 ≠ 0 := by
    exact pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)

@[blueprint
  (title := "$x$ is defined")
  (statement := /--
  In the situation of Theorem 1, $Y \neq 0$ for each $t \in \mathbb{F}_q \setminus \{\pm 1\}$,
  so that
  $$
  x = (c - 1)sX(1 + X)/Y
  $$
  is defined.
  -/)]
theorem x_defined
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, (Y t s q) ≠ 0 := by
    intro t
    exact Y_ne_zero hs_ne_zero hq_card hq_mod t

@[blueprint
  (title := "$y$ is defined")
  (statement := /--
  In the situation of Theorem 1, $rX + (1 + X)^2 \neq 0$ for each
  $t \in \mathbb{F}_q \setminus \{\pm 1\}$, so that
  $$
  y = (rX - (1 + X)^2)/(rX + (1 + X)^2).
  y = (rX - (1 + X)^2)/(rX + (1 + X)^2)
  $$
  is defined.
  -/)]
theorem y_defined
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ((r s) * (X t s) + (1 + (X t s))^2) ≠ 0 := by
    intro t
    exact y_divisor_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod t

/-- The auxiliary coordinates `X` and `Y` satisfy the hyperelliptic equation used in Theorem 1:
`Y² = X⁵ + (r² - 2)X³ + X`. -/
@[blueprint
  (title := "$(X, Y)$ lies on the auxiliary curve")
  (statement := /--
  In the situation of Theorem 1, let $t \in \mathbb{F}_q \setminus \{\pm 1\}$ and let $r$, $X$,
  $Y$ be as above. Then
  $$
  Y^2 = X^5 + (r^2 - 2)X^3 + X .
  $$
  -/)]
theorem map_fulfills_auxiliary_equation
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  :
  let r := r s
  let X := X t s
  let Y := Y t s q
  Y^2 = X^5 + (r^2 - 2) * X^3 + X := by
    intro r_of_s X_of_t Y_of_t
    exact helper_eq t hs_ne_zero hq_card hq_primePow hq_mod

/-- The quantities constructed for a nonexceptional input are all nonzero as asserted in
Theorem 1: `u * v * X * Y * x * (y + 1) ≠ 0`. -/
@[blueprint
  (title := "Nonvanishing of the auxiliary quantities")
  (statement := /--
  In the situation of Theorem 1, let $t \in \mathbb{F}_q \setminus \{\pm 1\}$ and let
  $u, v, X, Y, x, y$ be as above. Then
  $$
  uvXYx(y + 1) \neq 0 .
  $$
  -/)]
theorem variable_mul_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  :
  let u := u t
  let v := v t s
  let X := X t s
  let Y := Y t s q
  let x := x t s q
  let y := y t s
  u * v * X  * Y * x * (y + 1) ≠ 0 :=
    variable_mul_ne_zero' t hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod

/-- The coordinates produced from a nonexceptional input satisfy the Edwards curve equation
`x² + y² = 1 + d * x² * y²`. This is the final conclusion of Theorem 1. -/
@[blueprint
  (title := "$(x, y)$ lies on the Edwards curve")
  (statement := /--
  In the situation of Theorem 1, let $t \in \mathbb{F}_q \setminus \{\pm 1\}$ and let $x$, $y$
  be as above. Then $(x, y)$ is a point of the complete Edwards curve
  $E : x^2 + y^2 = 1 + d x^2 y^2$, i.e.
  $$
  x^2 + y^2 = 1 + d x^2 y^2 .
  $$
  -/)]
theorem map_fulfills_curve_equation
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  :
  let x := x t s q
  let y := y t s
  let d := d s
  have d_h : d ≠ 0 ∧ d ≠ 1 := by exact d_ne_zero_and_d_ne_one sq_ne_pm_two hq_card hq_mod
  edwardsCurveEquation x y ⟨d, d_h⟩ := by
    intro x_of_t y_of_t d_of_s
    rw [edwardsCurveEquation_iff]
    exact curve_equation t hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod

/-- The total Elligator map `ϕ : F → E(F)` from Definition 2 of the paper.

For `t ≠ ±1`, it returns the coordinates `x(t)` and `y(t)` constructed in Theorem 1. The two
exceptional inputs `t = ±1` are both mapped to the neutral point `(0, 1)`. The codomain subtype
records that the result satisfies the Edwards curve equation. -/
@[blueprint "def:ϕ"
  (title := "The decoding function $\\varphi$")
  (statement := /--
  In the situation of Theorem 1, the decoding function for the complete Edwards curve
  $E : x^2 + y^2 = 1 + d x^2 y^2$ is the function
  $\varphi : \mathbb{F}_q \to E(\mathbb{F}_q)$ defined as follows:
  $$
  \varphi(\pm 1) = (0, 1);
  $$
  if $t \notin \{\pm 1\}$ then $\varphi(t) = (x, y)$.
  -/)]
noncomputable def ϕ
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : EOverF sq_ne_pm_two hq_card hq_mod :=
  open scoped Classical in let P := if h : t ≠ 1 ∧ t ≠ -1
    then (x ⟨t, h⟩ s q, y ⟨t, h⟩ s)
    else (0, 1)
  have P_in_EOverF : P ∈ (EOverF sq_ne_pm_two hq_card hq_mod) := by
    unfold EOverF
    rw [Set.mem_setOf_eq]
    unfold P
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · rw [dif_pos h1]
      exact map_fulfills_curve_equation ⟨t, h1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod
    · rw [dif_neg h1]
      simp
  ⟨P, P_in_EOverF⟩

end Elligator.Elligator1
