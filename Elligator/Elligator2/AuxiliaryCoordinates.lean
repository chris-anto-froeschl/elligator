/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator2.CurveParameters

/-!
# The auxiliary coordinates `v` and `ε` of Elligator 2

[Bernstein2013a], Theorem 5, defines for each nonzero `r ∈ R`

```
v = -A / (1 + u r ^ 2),   ε = χ (v ^ 3 + A v ^ 2 + B v) ,
```

and the first two steps of its proof show that `v ≠ 0` and that `v ^ 3 + A v ^ 2 + B v ≠ 0`, so
that `ε ∈ {1, -1}`.

## Main results

* `v_ne_zero`: `v` is defined and nonzero ("By hypothesis `A ≠ 0` and `1 + u r ^ 2 ≠ 0`").
* `sq_mul_rhsFactor_v`: the identity `(1 + u r ^ 2) ^ 2 (v ^ 2 + A v + B)
  = B (1 + u r ^ 2) ^ 2 - A ^ 2 u r ^ 2`, which turns the defining condition of `R` into the
  statement `v ^ 2 + A v + B ≠ 0`.
* `rhsFactor_v_ne_zero`, `rhs_v_ne_zero`, `ε_ne_zero`: the paper's step
  "`v ^ 3 + A v ^ 2 + B v ≠ 0` and `ε ≠ 0`".
* `ε_eq_one_or_eq_neg_one`, `ε_sq`: `ε` is a sign.

## References

See [Bernstein2013a], Section 5.2, Theorem 5.
-/

@[expose] public section

namespace Elligator.Elligator2

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator2.CurveParameters

variable {F : Type*} [Field F]

namespace ParamData

variable (P : ParamData F)

/-- The auxiliary coordinate `v = -A / (1 + u r ^ 2)` of Theorem 5. -/
@[blueprint "def:v2"
  (title := "The auxiliary coordinate $v$")
  (statement := /--
  In the situation of Theorem 5, for each nonzero $r \in R$ define
  $$
  v = -A/(1 + u r ^ 2) .
  $$
  -/)]
def v (r : F) : F := -P.A / (1 + P.u * r ^ 2)

/-- The quadratic character `ε = χ(v ^ 3 + A v ^ 2 + B v)` of Theorem 5. -/
@[blueprint "def:eps2"
  (title := "The sign $\\varepsilon$")
  (statement := /--
  In the situation of Theorem 5, for each nonzero $r \in R$ define
  $$
  \varepsilon = \chi(v ^ 3 + A v ^ 2 + B v) .
  $$
  -/)]
def ε [Fintype F] [DecidableEq F] (r : F) : F := χ (P.rhs (P.v r))

end ParamData

namespace CurveParameters

variable (P : ParamData F) {r : F}

/-- The defining relation `v (1 + u r ^ 2) = -A` of `v`. -/
lemma v_mul_one_add (hw : 1 + P.u * r ^ 2 ≠ 0) :
    P.v r * (1 + P.u * r ^ 2) = -P.A := by
  simp only [ParamData.v]
  field_simp

/-- `v` is defined and nonzero, the first step of the proof of Theorem 5. -/
@[blueprint "lemma:v2_ne_zero"
  (title := "$v$ is defined and $v \\neq 0$")
  (statement := /--
  In the situation of Theorem 5, $v$ is defined and $v \neq 0$: by hypothesis $A \neq 0$ and
  $1 + u r ^ 2 \neq 0$.
  -/)]
lemma v_ne_zero [IsRegularABParam P.A P.B] (hw : 1 + P.u * r ^ 2 ≠ 0) : P.v r ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr (A_ne_zero P)) hw

/-- The relation `v + A = -(v u r ^ 2)`, i.e. the paper's `v + v u r ^ 2 = -A`. -/
lemma v_add_A (hw : 1 + P.u * r ^ 2 ≠ 0) :
    P.v r + P.A = -(P.v r * P.u * r ^ 2) := by
  have h := v_mul_one_add P hw
  linear_combination h

/-- The paper's computation `v ^ 2 + A v = v (v + A) = v (-v u r ^ 2)`. -/
lemma v_mul_v_add_A (hw : 1 + P.u * r ^ 2 ≠ 0) :
    P.v r * (P.v r + P.A) = -(P.v r ^ 2 * P.u * r ^ 2) := by
  rw [v_add_A P hw]
  ring

/-- Clearing denominators in `v ^ 2 + A v + B` turns the defining condition of `R` into a
statement about `v`. -/
lemma sq_mul_rhsFactor_v (hw : 1 + P.u * r ^ 2 ≠ 0) :
    (1 + P.u * r ^ 2) ^ 2 * P.rhsFactor (P.v r)
      = P.B * (1 + P.u * r ^ 2) ^ 2 - P.A ^ 2 * P.u * r ^ 2 := by
  have h := v_mul_one_add P hw
  rw [ParamData.rhsFactor_eq]
  linear_combination (P.v r * (1 + P.u * r ^ 2) - P.A + P.A * (1 + P.u * r ^ 2)) * h

/-- For `1 + u r ^ 2 ≠ 0`, admissibility of `r` is exactly the nonvanishing of `v ^ 2 + A v + B`.

This is the content of the second step of the proof of Theorem 5: "If `v ^ 2 + A v + B = 0` then
`v ^ 2 u r ^ 2 = B` so, using the definition of `v`, `A ^ 2 u r ^ 2 = B(1 + u r ^ 2) ^ 2`,
contradicting the definition of `R`". -/
lemma mem_R_iff_rhsFactor_v_ne_zero (hw : 1 + P.u * r ^ 2 ≠ 0) :
    r ∈ P.R ↔ P.rhsFactor (P.v r) ≠ 0 := by
  rw [ParamData.mem_R_iff]
  have h := sq_mul_rhsFactor_v P hw
  constructor
  · rintro ⟨-, hR⟩ hzero
    rw [hzero, mul_zero] at h
    exact hR (by linear_combination h)
  · intro hne
    refine ⟨hw, fun hR => hne ?_⟩
    have hsq : (1 + P.u * r ^ 2) ^ 2 * P.rhsFactor (P.v r) = 0 := by
      rw [h, hR]
      ring
    exact (mul_eq_zero.mp hsq).resolve_left (pow_ne_zero 2 hw)

/-- The paper's step "`v ^ 2 + A v + B ≠ 0`" for an admissible `r`. -/
@[blueprint "lemma:rhsFactor_v_ne_zero"
  (title := "$v ^ 2 + A v + B \\neq 0$")
  (statement := /--
  In the situation of Theorem 5, let $r \in R$ with $1 + u r ^ 2 \neq 0$. If
  $v ^ 2 + A v + B = 0$ then $v ^ 2 u r ^ 2 = B$, so, using the definition of $v$,
  $A ^ 2 u r ^ 2 = B(1 + u r ^ 2) ^ 2$, contradicting the definition of $R$. Hence
  $v ^ 2 + A v + B \neq 0$.
  -/)]
lemma rhsFactor_v_ne_zero (hr : r ∈ P.R) : P.rhsFactor (P.v r) ≠ 0 :=
  (mem_R_iff_rhsFactor_v_ne_zero P hr.1).mp hr

/-- The paper's step "`v ^ 3 + A v ^ 2 + B v ≠ 0`" for an admissible `r`. -/
lemma rhs_v_ne_zero [IsRegularABParam P.A P.B] (hr : r ∈ P.R) : P.rhs (P.v r) ≠ 0 := by
  rw [ParamData.rhs_eq_mul_rhsFactor]
  exact mul_ne_zero (v_ne_zero P hr.1) (rhsFactor_v_ne_zero P hr)

/-- Negating the input does not change `v`. -/
@[simp]
lemma v_neg : P.v (-r) = P.v r := by
  rw [ParamData.v, ParamData.v, neg_pow_two]

variable [Fintype F] [DecidableEq F]

/-- The paper's step "`ε ≠ 0`". -/
lemma ε_ne_zero [IsRegularABParam P.A P.B] (hr : r ∈ P.R) : P.ε r ≠ 0 :=
  χ_a_ne_zero (rhs_v_ne_zero P hr)

lemma ε_eq_one_or_eq_neg_one [IsRegularABParam P.A P.B] (hr : r ∈ P.R) :
    P.ε r = 1 ∨ P.ε r = -1 :=
  (χ_values (a := P.rhs (P.v r))).resolve_left (ε_ne_zero P hr) |>.symm

/-- A sign squares to one. -/
lemma ε_sq [IsRegularABParam P.A P.B] (hr : r ∈ P.R) : P.ε r ^ 2 = 1 := by
  rcases ε_eq_one_or_eq_neg_one P hr with h | h <;> rw [h] <;> ring

/-- Negating the input does not change `ε`. -/
@[simp]
lemma ε_neg : P.ε (-r) = P.ε r := by
  rw [ParamData.ε, ParamData.ε, v_neg]

end CurveParameters

end Elligator.Elligator2
