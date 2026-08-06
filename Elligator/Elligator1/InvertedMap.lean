/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.phiProperties

/-!
# Inverted Map

This file collects the three conclusions of Theorem 3 in the Elligator paper. It describes the
preimage and image of `ϕ`, and verifies the paper's explicit inverse formula on that image.

## Main results

* `ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages`: the preimage of `ϕ t` consists exactly of `t` and `-t`;
  in particular, `ϕ t = ϕ (-t)` and there are no other preimages.
* `props_iff_mem_ϕOverF`: membership in the image `ϕ(F)` is equivalent to the three
  algebraic point conditions stated in part 2 of Theorem 3.
* `X2_defined`, `z_defined`, `t2_defined`: the denominators required by the inverse construction
  are nonzero on `ϕ(F)`.
* `ϕ_of_t2_eq_x_y`: applying `ϕ` to the reconstructed parameter `t2` recovers the original point.

## References

See [bernstein2013a] Section 3.3, Theorem 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

/-- The preimage of `ϕ t` consists exactly of the two field elements `t` and `-t`.

This is part 1 of Theorem 3. The left side records `ϕ t = ϕ (-t)`; the right side says that no
field element distinct from both `t` and `-t` maps to `ϕ t`. -/
@[blueprint "thm:thm3-1"
  (title := "Theorem 3.1: the fibers of $\\varphi$")
  (statement := /--
  In the situation of Definition 2: if $t \in \mathbb{F}_q$ then the set of preimages of
  $\varphi(t)$ under $\varphi$ is $\{t, -t\}$.
  Equivalently, $\varphi(t) = \varphi(-t)$ if and only if no element of $\mathbb{F}_q$ other
  than $t$ and $-t$ maps to $\varphi(t)$.
  -/)]
theorem ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  :
  let ϕ_of_t := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod).val
  let ϕ_of_neg_t := (ϕ (-t) hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod).val
  ϕ_of_t = ϕ_of_neg_t
  ↔ ¬(∃ (p : { n : F // n ≠ t ∧ n ≠ -t}),
    ϕ p.val hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod = ϕ_of_t) := by
    intro ϕ_of_t ϕ_of_neg_t
    constructor
    · intro h
      exact ϕ_preimages t hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod
    · intro h
      exact ϕ_of_t_eq_ϕ_of_neg_t t hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod

/-- Characterization of the image of `ϕ` by the three conditions in part 2 of Theorem 3.
For `P = ϕ t`, membership in `ϕ(F)` is equivalent to `ϕOverFProps s P`: `y + 1 ≠ 0`,
`(1 + ηr)² - 1` is a square, and the exceptional case `ηr = -2` has the specified `x`-coordinate.

Note: Original statement does not read like an iff. Only the proof explanation
makes this more concrete.
-/
@[blueprint "thm:thm3-2"
  (title := "Theorem 3.2: the image of $\\varphi$")
  (statement := /--
  In the situation of Definition 2: $\varphi(\mathbb{F}_q)$ is the set of
  $(x, y) \in E(\mathbb{F}_q)$ such that
  \begin{itemize}
    \item $y + 1 \neq 0$;
    \item $(1 + \eta r)^2 - 1$ is a square, where $\eta = \frac{y - 1}{2(y + 1)}$; and
    \item if $\eta r = -2$ then $x = 2s(c - 1)\chi(c)/r$.
  \end{itemize}
  -/)]
theorem props_iff_mem_ϕOverF
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  :
  let P := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod
  ϕOverFProps s P ↔ P.val ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod := by
    intro P
    constructor
    · exact P_in_ϕOverF_of_P_props hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod P
    · exact P_props_of_P_in_ϕOverF t hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod

/-- The explicit inverse formula in part 3 of Theorem 3 recovers a point in `ϕ(F)`.

Starting with `P = ϕ t`, the definitions `X2`, `z`, `u2`, and `t2` reproduce the paper's
quantities `X2`, `z`, `u2`, and `t2`; evaluating `ϕ (t2 s P q)` returns the coordinates of `P`. -/
@[blueprint "thm:thm3-3"
  (title := "Theorem 3.3: inverting $\\varphi$")
  (statement := /--
  In the situation of Definition 2: if $(x, y) \in \varphi(\mathbb{F}_q)$ then the following
  elements $\bar X, z, \bar u, \bar t$ of $\mathbb{F}_q$ are defined and
  $\varphi(\bar t) = (x, y)$:
  \begin{align*}
    \bar X &= -(1 + \eta r) + ((1 + \eta r)^2 - 1)^{(q+1)/4}, \\
    z &= \chi\bigl((c - 1)s\bar X(1 + \bar X)x(\bar X^2 + 1/c^2)\bigr), \\
    \bar u &= z\bar X, \\
    \bar t &= (1 - \bar u)/(1 + \bar u).
  \end{align*}
  -/)]
theorem ϕ_of_t2_eq_x_y
  -- Fix t ∈ F_q
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  :
  -- Define (x, y) = ϕ(t)
  let P := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod).val
  let x_of_t := P.1
  let y_of_t := P.2
  -- t2 defined (and used to build ϕ(t2))
  let t' := t2 s P q
  let ϕ_of_t' := (ϕ t' hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod).val
  ϕ_of_t' = (x_of_t, y_of_t) := by
    intro P x_of_P y_of_P t' ϕ_of_t'
    unfold x_of_P y_of_P P ϕ
    dsimp
    split
    · rename_i h
      exact ϕ_of_t2_eq_x_y_main_case ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod
    · rename_i h
      exact ϕ_of_t2_eq_x_y_base_case
        ⟨t, by grind⟩ hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod

/-- The denominator `2 * (y + 1)` in the inverse construction is nonzero on `ϕ(F)`.
This supplies the definedness of `η`, and hence of `X2`, in part 3 of Theorem 3. -/
@[blueprint "thm:X2_defined"
  (title := "$\\bar X$ is defined")
  (statement := /--
  For $(x, y) \in \varphi(\mathbb{F}_q)$ the denominator $2(y + 1)$ of $\eta$ is nonzero, so
  $\eta$ and hence $\bar X$ of Theorem 3.3 are defined.
  -/)]
theorem X2_defined
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  (P : {p : F × F // p ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod})
  :
  let y := P.val.snd
  2 * (y + 1) ≠ 0 := by
    intro y
    have h1 : y + 1 ≠ 0 := by
      unfold y
      let h1_1 := P.prop
      unfold ϕOverF at h1_1
      rcases h1_1 with ⟨t, h1_2⟩
      unfold ϕ at h1_2
      by_cases h1_3 : t ≠ 1 ∧ t ≠ -1
      · grind [y_add_one_ne_zero]
      · dsimp at h1_2
        rw [dif_neg h1_3] at h1_2
        let h1_4 := congrArg Prod.snd h1_2
        rw [← h1_4]
        ring_nf
        exact two_ne_zero hq_card hq_mod
    exact mul_ne_zero (two_ne_zero hq_card hq_mod) h1

omit [DecidableEq F] in
/-- The denominator `c²` occurring in the definition of `z` is nonzero. -/
@[blueprint "thm:z_defined"
  (title := "$z$ is defined")
  (statement := /--
  The denominator $c^2$ occurring in $z$ of Theorem 3.3 is nonzero, so $z$ is defined.
  -/)]
theorem z_defined (hs_ne_zero : s ≠ 0) (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : (c s)^2 ≠ 0 := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)

/-- The denominator `1 + u2` in the reconstructed parameter `t2` is nonzero on `ϕ(F)`. -/
@[blueprint "thm:t2_defined"
  (title := "$\\bar t$ is defined")
  (statement := /--
  For $(x, y) \in \varphi(\mathbb{F}_q)$ the denominator $1 + \bar u$ of $\bar t$ in
  Theorem 3.3 is nonzero, so $\bar t$ is defined.
  -/)]
theorem t2_defined
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  (P : {p : F × F // p ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod})
  :
  let u2_of_P := u2 s P.val q
  (1 + u2_of_P) ≠ 0 := one_add_u2_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_primePow hq_mod P

end Elligator.Elligator1
