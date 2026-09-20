/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator2.OutputCoordinates

/-!
# The Elligator 2 map

This file assembles Theorem 5 of [Bernstein2013a] and states Definition 6, the decoding function
`ψ : R → E(F_q)`.

## Main results

* `thm5_ne_zero`: the paper's conclusion "Furthermore `v ε x y ≠ 0`".
* `thm5_curve_equation`: the paper's conclusion "`y ^ 2 = x ^ 3 + A x ^ 2 + B x`".
* `ψ`: Definition 6, `ψ(0) = (0, 0)` and `ψ(r) = (x, y)` for `r ≠ 0`.
* `ψ_mem_EOverF`, `ψPoint`: `ψ` really does take values in `E(F_q)`.
* `ψ_neg`: `ψ(-r) = ψ(r)`, the easy half of Theorem 7.1.
* `ψOverR`: the image `ψ(R)`, the object described by Theorem 7.2.

## References

See [Bernstein2013a], Section 5.2, Theorem 5 and Definition 6.
-/

@[expose] public section

namespace Elligator.Elligator2

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.SquareRootFunction
open Elligator.Primitives.ECC
open Elligator.Elligator2.CurveParameters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (P : ParamData F) {r : F}

section theorem5

variable [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u] [IsSqrtFun P.sqrt]

/-- The nonvanishing conclusion of Theorem 5: `v ε x y ≠ 0`. -/
@[blueprint "thm:thm5-ne-zero"
  (title := "Theorem 5: $v \\varepsilon x y \\neq 0$")
  (statement := /--
  In the situation of Theorem 5, the elements $v$, $\varepsilon$, $x$, $y$ are defined for each
  nonzero $r \in R$ and satisfy
  $$
  v \varepsilon x y \neq 0 .
  $$
  -/)]
theorem thm5_ne_zero (hr : r ∈ P.R) (hr0 : r ≠ 0) :
    P.v r * P.ε r * P.x r * P.y r ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (v_ne_zero P hr.1) (ε_ne_zero P hr))
    (x_ne_zero P hr hr0)) (y_ne_zero P hr hr0)

/-- The curve equation conclusion of Theorem 5: `y ^ 2 = x ^ 3 + A x ^ 2 + B x`. -/
@[blueprint "thm:thm5-curve"
  (title := "Theorem 5: $y ^ 2 = x ^ 3 + A x ^ 2 + B x$")
  (statement := /--
  In the situation of Theorem 5, for each nonzero $r \in R$ the pair $(x, y)$ satisfies
  $$
  y ^ 2 = x ^ 3 + A x ^ 2 + B x ,
  $$
  i.e. it is a point of $E(\mathbb{F}_q)$.
  -/)]
theorem thm5_curve_equation (hr : r ∈ P.R) (hr0 : r ≠ 0) :
    P.curve.Equation (P.x r) (P.y r) :=
  equation_x_y P hr hr0

end theorem5

namespace ParamData

/-- The Elligator 2 decoding function `ψ` of Definition 6.

For `r ≠ 0` it returns the coordinates `(x, y)` constructed in Theorem 5, and `ψ(0) = (0, 0)`,
the point of order two of the curve. -/
@[blueprint "def:psi"
  (title := "The decoding function $\\psi$")
  (statement := /--
  In the situation of Theorem 5, the decoding function for the Weierstrass curve
  $E : y ^ 2 = x ^ 3 + A x ^ 2 + B x$ is the function $\psi : R \to E(\mathbb{F}_q)$ defined as
  follows: $\psi(0) = (0, 0)$; if $r \neq 0$ then $\psi(r) = (x, y)$.
  -/)]
def ψ (r : F) : F × F := if r = 0 then (0, 0) else (P.x r, P.y r)

@[simp] lemma ψ_zero : P.ψ 0 = (0, 0) := by simp [ψ]

lemma ψ_of_ne_zero (hr0 : r ≠ 0) : P.ψ r = (P.x r, P.y r) := by simp [ψ, hr0]

lemma ψ_fst_of_ne_zero (hr0 : r ≠ 0) : (P.ψ r).1 = P.x r := by rw [ψ_of_ne_zero P hr0]

lemma ψ_snd_of_ne_zero (hr0 : r ≠ 0) : (P.ψ r).2 = P.y r := by rw [ψ_of_ne_zero P hr0]

/-- The image `ψ(R)` of the Elligator 2 map. -/
@[blueprint "def:psiOverR"
  (title := "The image $\\psi(R)$")
  (statement := /--
  The set of curve points produced by the Elligator 2 map,
  $$
  \psi(R) = \{\psi(r) : r \in R\} \subseteq E(\mathbb{F}_q) .
  $$
  -/)]
def ψOverR : Set (F × F) := {Q : F × F | ∃ r ∈ P.R, P.ψ r = Q}

lemma mem_ψOverR_iff (Q : F × F) : Q ∈ P.ψOverR ↔ ∃ r ∈ P.R, P.ψ r = Q := Iff.rfl

lemma mem_ψOverR (hr : r ∈ P.R) : P.ψ r ∈ P.ψOverR := ⟨r, hr, rfl⟩

end ParamData

section image

variable [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u] [IsSqrtFun P.sqrt]

/-- `ψ` takes its values in `E(F_q)`, as asserted by Definition 6. -/
lemma ψ_mem_EOverF (hr : r ∈ P.R) : P.ψ r ∈ P.EOverF := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [ParamData.ψ_zero]
    exact P.curve.twoTorsion_mem_affinePoints
  · rw [ParamData.ψ_of_ne_zero P hr0]
    exact thm5_curve_equation P hr hr0

/-- The Elligator 2 map with its codomain restricted to `E(F_q)`, as in Definition 6. -/
def ψPoint (r : F) (hr : r ∈ P.R) : {Q : F × F // Q ∈ P.EOverF} := ⟨P.ψ r, ψ_mem_EOverF P hr⟩

lemma ψOverR_subset_EOverF : P.ψOverR ⊆ P.EOverF := by
  rintro Q ⟨r, hr, rfl⟩
  exact ψ_mem_EOverF P hr

omit [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u] [IsSqrtFun P.sqrt] in
/-- `ψ(r) = ψ(-r)`: the map only depends on `r ^ 2`. This is the easy half of Theorem 7.1. -/
@[blueprint "lemma:psi_neg"
  (title := "$\\psi(-r) = \\psi(r)$")
  (statement := /--
  If $r = 0$ then $r = -r$ so $\psi(r) = \psi(-r)$. If $r \neq 0$ then Theorem 5 defines
  $\psi(r)$ purely in terms of $r ^ 2$, so $\psi(r) = \psi(-r)$.
  -/)]
lemma ψ_neg (r : F) : P.ψ (-r) = P.ψ r := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  · rw [ParamData.ψ_of_ne_zero P (neg_ne_zero.mpr hr0), ParamData.ψ_of_ne_zero P hr0,
      x_neg, y_neg]

end image

end Elligator.Elligator2
