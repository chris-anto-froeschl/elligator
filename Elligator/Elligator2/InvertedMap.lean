/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator2.ReconstructionCoordinates

/-!
# Inverting the Elligator 2 map

This file collects the three conclusions of [Bernstein2013a], Theorem 7. It describes the
preimages and the image of `ψ`, and verifies the paper's explicit inverse formula on that image.

## Main results

* `ψ_preimage_eq`: for `r ∈ R` the set of preimages of `ψ(r)` under `ψ` is `{r, -r}`, part 1 of
  Theorem 7.
* `mem_ψOverR_iff_props`: a point of `E(F_q)` lies in `ψ(R)` if and only if it satisfies the three
  conditions `x ≠ -A`, `y = 0 → x = 0` and `-u x (x + A)` is a square, part 2 of Theorem 7.
* `rbar_mem_R_and_ψ_rbar`: for `(x, y) ∈ ψ(R)` the element `rbar` is defined, lies in `R`, and
  satisfies `ψ(rbar) = (x, y)`, part 3 of Theorem 7.

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
open Elligator.Elligator2.ReconstructionCoordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (P : ParamData F) (Q : PointData F) {r r' : F}
variable [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u] [IsSqrtFun P.sqrt]

section preimages

omit [IsSqrtFun P.sqrt] in
/-- A nonzero admissible input is not mapped to the point `(0, 0)`. -/
lemma ψ_ne_zero_of_ne_zero (hr : r ∈ P.R) (hr0 : r ≠ 0) : P.ψ r ≠ (0, 0) := by
  rw [ParamData.ψ_of_ne_zero P hr0]
  intro h
  exact x_ne_zero P hr hr0 (congrArg Prod.fst h)

/-- If `ψ(r) = ψ(r')` then `ε` agrees on `r` and `r'`, since `y` is `-ε` times a nonzero
square root determined by `x`. -/
lemma ε_eq_of_ψ_eq (hr : r ∈ P.R) (hr0 : r ≠ 0)
    (hx : P.x r' = P.x r) (hy : P.y r' = P.y r) : P.ε r' = P.ε r := by
  have hs : P.sqrt (P.rhs (P.x r)) ≠ 0 :=
    sqrt_ne_zero P.sqrt (isSquare_rhs_x P hr hr0) (rhs_x_ne_zero P hr hr0)
  rw [ParamData.y, ParamData.y, hx] at hy
  field_simp at hy
  exact neg_inj.mp hy

omit [IsNonsquareParam P.u] [IsSqrtFun P.sqrt] in
/-- If `ψ(r) = ψ(r')` then `v` agrees on `r` and `r'`. -/
lemma v_eq_of_ψ_eq (hr : r ∈ P.R) (hx : P.x r' = P.x r) (hε : P.ε r' = P.ε r) :
    P.v r' = P.v r := by
  rcases ε_eq_one_or_eq_neg_one P hr with h | h
  · rw [← x_of_ε_eq_one P h, ← x_of_ε_eq_one P (hε.trans h), hx]
  · have h' : P.v r' = -P.x r' - P.A := by
      rw [x_of_ε_eq_neg_one P (hε.trans h)]
      ring
    rw [h', hx, x_of_ε_eq_neg_one P h]
    ring

/-- The converse half of part 1 of Theorem 7: the only preimages of `ψ(r)` are `r` and `-r`. -/
@[blueprint "lemma:eq_or_eq_neg_of_psi_eq"
  (title := "$\\psi(r) = \\psi(r')$ implies $r' \\in \\{r, -r\\}$")
  (statement := /--
  Assume that $\psi(r) = \psi(r')$ with $r, r' \in R$. If $r = 0$ then $\psi(r) = (0, 0)$, and
  otherwise $\psi(r)$ has nonzero coordinates by Theorem 5; hence $r = 0$ if and only if
  $r' = 0$. In the remaining case $y = -\varepsilon\sqrt{x ^ 3 + A x ^ 2 + B x}$ and
  $y' = -\varepsilon'\sqrt{(x') ^ 3 + A (x') ^ 2 + B x'}$, so $\varepsilon' = \varepsilon$ since
  $\sqrt{\ }$ is a function. Next $x = \varepsilon v - (1 - \varepsilon)A/2$ and
  $x' = \varepsilon' v' - (1 - \varepsilon')A/2$ so $v' = v$. Finally
  $1 + u r ^ 2 = 1 + u (r') ^ 2$ so $r' \in \{r, -r\}$.
  -/)]
theorem eq_or_eq_neg_of_ψ_eq (hr : r ∈ P.R) (hr' : r' ∈ P.R) (h : P.ψ r' = P.ψ r) :
    r' = r ∨ r' = -r := by
  rcases eq_or_ne r 0 with rfl | hr0
  · left
    by_contra hr0'
    rw [ParamData.ψ_zero] at h
    exact ψ_ne_zero_of_ne_zero P hr' hr0' h
  · rcases eq_or_ne r' 0 with rfl | hr0'
    · rw [ParamData.ψ_zero] at h
      exact absurd h.symm (ψ_ne_zero_of_ne_zero P hr hr0)
    · rw [ParamData.ψ_of_ne_zero P hr0', ParamData.ψ_of_ne_zero P hr0, Prod.mk.injEq] at h
      obtain ⟨hx, hy⟩ := h
      have hε := ε_eq_of_ψ_eq P hr hr0 hx hy
      have hv := v_eq_of_ψ_eq P hr hx hε
      -- `v (1 + u r ^ 2) = -A = v (1 + u (r') ^ 2)` with `v ≠ 0` gives `u r ^ 2 = u (r') ^ 2`
      have h1 := v_mul_one_add P (r := r) hr.1
      have h2 := v_mul_one_add P (r := r') hr'.1
      rw [hv] at h2
      have hvne := v_ne_zero P hr.1
      have hsq : r' ^ 2 = r ^ 2 := by
        have hu := u_ne_zero P
        have : P.v r * (P.u * r' ^ 2) = P.v r * (P.u * r ^ 2) := by linear_combination h2 - h1
        have := mul_left_cancel₀ hvne this
        exact mul_left_cancel₀ hu this
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

/-- Part 1 of Theorem 7: the set of preimages of `ψ(r)` under `ψ` is `{r, -r}`. -/
@[blueprint "thm:thm7-1"
  (title := "Theorem 7.1: the preimages of $\\psi(r)$")
  (statement := /--
  In the situation of Definition 6, if $r \in R$ then the set of preimages of $\psi(r)$ under
  $\psi$ is $\{r, -r\}$.
  -/)]
theorem ψ_preimage_eq (hr : r ∈ P.R) :
    {r' : F | r' ∈ P.R ∧ P.ψ r' = P.ψ r} = {r, -r} := by
  ext r'
  constructor
  · rintro ⟨hr', heq⟩
    rcases eq_or_eq_neg_of_ψ_eq P hr hr' heq with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨hr, rfl⟩
    · exact ⟨neg_mem_R P hr, ψ_neg P r⟩

end preimages

section image

/-- The forward half of part 2 of Theorem 7: every point of `ψ(R)` satisfies the three
conditions. -/
lemma ψOverRProps_of_mem_R (hr : r ∈ P.R) : (P.withPoint (P.ψ r)).ψOverRProps := by
  have hA := A_ne_zero P
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [ParamData.ψ_zero]
    refine ⟨?_, fun _ => rfl, ?_⟩
    · change (0 : F) + P.A ≠ 0
      simpa using hA
    · change IsSquare (-(P.u * ((0 : F) * ((0 : F) + P.A))))
      simp
  · rw [ParamData.ψ_of_ne_zero P hr0]
    exact ⟨x_add_A_ne_zero P hr hr0, fun h => absurd h (y_ne_zero P hr hr0),
      isSquare_neg_u_mul_x_mul_x_add_A P hr⟩

omit [Fintype F] [DecidableEq F] [IsOddCard F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u]
  [IsSqrtFun P.sqrt] in
lemma withPoint_self : Q.toParamData.withPoint Q.P = Q := rfl

variable [IsRegularABParam Q.A Q.B] [IsNonsquareParam Q.u] [IsSqrtFun Q.sqrt]

/-- Part 2 of Theorem 7: `ψ(R)` is the set of points of `E(F_q)` with `x ≠ -A`, with `x = 0`
whenever `y = 0`, and with `-u x (x + A)` a square. -/
@[blueprint "thm:thm7-2"
  (title := "Theorem 7.2: the image $\\psi(R)$")
  (statement := /--
  In the situation of Definition 6, $\psi(R)$ is the set of $(x, y) \in E(\mathbb{F}_q)$ such
  that
  \begin{itemize}
  \item $x \neq -A$,
  \item if $y = 0$ then $x = 0$, and
  \item $-u x (x + A)$ is a square in $\mathbb{F}_q$.
  \end{itemize}
  -/)]
theorem mem_ψOverR_iff_props (hcurve : Q.P ∈ Q.EOverF) :
    Q.P ∈ Q.toParamData.ψOverR ↔ Q.ψOverRProps := by
  constructor
  · rintro ⟨r, hr, heq⟩
    have hQ : Q = Q.toParamData.withPoint (Q.toParamData.ψ r) := by
      rw [heq, withPoint_self]
    rw [hQ]
    exact ψOverRProps_of_mem_R Q.toParamData hr
  · intro hprops
    exact ⟨Q.rbar, rbar_mem_R Q hcurve hprops, ψ_rbar Q hcurve hprops⟩

/-- Part 3 of Theorem 7: for a point of `ψ(R)` the reconstruction `rbar` is defined, admissible,
and satisfies `ψ(rbar) = (x, y)`. -/
@[blueprint "thm:thm7-3"
  (title := "Theorem 7.3: the inverse formula")
  (statement := /--
  In the situation of Definition 6, if $(x, y) \in \psi(R)$ then the element $\bar r$ of $R$ is
  defined and $\psi(\bar r) = (x, y)$.
  -/)]
theorem rbar_mem_R_and_ψ_rbar (hQ : Q.P ∈ Q.toParamData.ψOverR) :
    Q.rbar ∈ Q.toParamData.R ∧ Q.toParamData.ψ Q.rbar = Q.P := by
  have hcurve : Q.P ∈ Q.EOverF := ψOverR_subset_EOverF Q.toParamData hQ
  have hprops : Q.ψOverRProps := (mem_ψOverR_iff_props Q hcurve).mp hQ
  exact ⟨rbar_mem_R Q hcurve hprops, ψ_rbar Q hcurve hprops⟩

end image

end Elligator.Elligator2
