/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator2.Context
public import Elligator.OddCharacteristic

/-!
# Curve parameters of Elligator 2

The elementary consequences of the standing hypotheses of [Bernstein2013a], Theorem 5:
`AB(A ^ 2 - 4B) ≠ 0`, `u` a non-square, and the description of the admissible set `R`.

## Main results

* `A_ne_zero`, `B_ne_zero`, `disc_ne_zero`: the three factors of `AB(A ^ 2 - 4B) ≠ 0`.
* `u_ne_zero`, `χ_u_eq_neg_one`: the non-square `u` is nonzero and has quadratic character `-1`.
* `zero_mem_R`, `neg_mem_R`: `0` is admissible, and admissibility only depends on `r ^ 2`.
* `R_eq_univ`: if `q ≡ 1 (mod 4)` and `A ^ 2 - 4B` is a non-square then `R = F_q`, the last
  assertion of Theorem 5.

## References

See [Bernstein2013a], Section 5.2, Theorem 5.
-/

@[expose] public section

namespace Elligator.Elligator2.CurveParameters

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F]
variable (P : ParamData F)

section coefficients

variable [IsRegularABParam P.A P.B]

/-- The paper assumes `A ≠ 0`: the curves of `j`-invariant `1728` are excluded. -/
lemma A_ne_zero : P.A ≠ 0 := by
  intro h
  exact AB_disc_ne_zero (A := P.A) (B := P.B) (by rw [h]; ring)

/-- The curve `y ^ 2 = x ^ 3 + A x ^ 2 + B x` is nonsingular, so `B ≠ 0`. -/
lemma B_ne_zero : P.B ≠ 0 := by
  intro h
  exact AB_disc_ne_zero (A := P.A) (B := P.B) (by rw [h]; ring)

/-- The curve `y ^ 2 = x ^ 3 + A x ^ 2 + B x` is nonsingular, so `A ^ 2 - 4B ≠ 0`. -/
lemma disc_ne_zero : P.A ^ 2 - 4 * P.B ≠ 0 := by
  intro h
  exact AB_disc_ne_zero (A := P.A) (B := P.B) (by rw [h]; ring)

/-- The Elligator 2 hypotheses make the curve model nonsingular. -/
lemma curve_isValid : P.curve.IsValid := by
  simp only [Primitives.ECC.WeierstrassABCurve.IsValid, ParamData.curve_A, ParamData.curve_B]
  exact mul_ne_zero (B_ne_zero P) (disc_ne_zero P)

end coefficients

section nonsquare

variable [IsNonsquareParam P.u]

/-- A non-square is nonzero. -/
lemma u_ne_zero : P.u ≠ 0 := by
  intro h
  exact u_nonsquare (u := P.u) (h ▸ IsSquare.zero)

variable [Fintype F] [DecidableEq F] [IsOddCard F]

/-- The quadratic character of the non-square `u` is `-1`. -/
lemma χ_u_eq_neg_one : χ P.u = -1 := χ_of_not_isSquare u_nonsquare

/-- `u r ^ 2` is a non-square for `r ≠ 0`; this is the key sign flip of Section 5. -/
lemma χ_u_mul_sq {r : F} (hr : r ≠ 0) : χ (P.u * r ^ 2) = -1 := by
  rw [χ_of_a_eq_χ_a_mul_b_pow_two hr, χ_u_eq_neg_one]

end nonsquare

section parameter_choices

variable [Fintype F]

/-- For `q ≡ 3 (mod 4)` one can take `u = -1`, as noted in [Bernstein2013a], Section 5.1. -/
instance isNonsquareParam_neg_one [IsCardThreeModFour F] : IsNonsquareParam (-1 : F) :=
  ⟨neg_one_non_square card_mod_four⟩

/-- For `q ≡ 5 (mod 8)` one can take `u = 2`, as noted in [Bernstein2013a], Section 5.1. -/
lemma isNonsquareParam_two (h : Fintype.card F % 8 = 5) : IsNonsquareParam (2 : F) :=
  ⟨not_isSquare_two_of_card_five_mod_eight h⟩

end parameter_choices

section admissible

variable [IsRegularABParam P.A P.B]

/-- `0` is always an admissible input; the paper sets `ψ(0) = (0, 0)`. -/
lemma zero_mem_R : (0 : F) ∈ P.R := by
  refine ⟨by simp, ?_⟩
  simpa using (B_ne_zero P).symm

omit [IsRegularABParam P.A P.B] in
/-- Admissibility only depends on `r ^ 2`, hence is preserved by negation. -/
lemma neg_mem_R {r : F} (hr : r ∈ P.R) : -r ∈ P.R := by
  rwa [ParamData.mem_R_iff, neg_pow_two]

variable [Fintype F] [DecidableEq F] [IsNonsquareParam P.u]

omit [DecidableEq F] in
/-- If `q ≡ 1 (mod 4)` and `A ^ 2 - 4B` is a non-square then `R = F_q`, so `ψ` is defined on all
of `F_q`.

This is the last assertion of [Bernstein2013a], Theorem 5. -/
@[blueprint "thm:thm5-R-eq-univ"
  (title := "Theorem 5: $R = \\mathbb{F}_q$")
  (statement := /--
  In the situation of Theorem 5, if $q \equiv 1 \pmod 4$ and $A ^ 2 - 4B$ is a non-square in
  $\mathbb{F}_q$ then
  $$
  R = \mathbb{F}_q .
  $$
  -/)]
theorem R_eq_univ [IsCardOneModFour F] [IsNonsquareDisc P.A P.B] : P.R = Set.univ := by
  classical
  ext r
  simp only [Set.mem_univ, iff_true]
  -- Write `s = u r ^ 2`, as in the proof of the paper.
  set s : F := P.u * r ^ 2 with hs_def
  -- `χ s ∈ {0, -1}`, while `χ (±1) = 1`, so `s ≠ ±1`; in particular `1 + s ≠ 0`.
  have hχs : χ s = 0 ∨ χ s = -1 := by
    rcases eq_or_ne r 0 with rfl | hr
    · left
      simp [hs_def]
    · right
      exact χ_u_mul_sq P hr
  have hs_ne_neg_one : s ≠ -1 := by
    intro h
    rw [h, χ_neg_one_of_card_one_mod_four] at hχs
    rcases hχs with h' | h'
    · exact one_ne_zero h'
    · exact absurd (by linear_combination h' : (2 : F) = 0) two_ne_zero_of_odd_card
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h, χ_one] at hχs
    rcases hχs with h' | h'
    · exact one_ne_zero h'
    · exact absurd (by linear_combination h' : (2 : F) = 0) two_ne_zero_of_odd_card
  have hone_add : 1 + s ≠ 0 := fun h => hs_ne_neg_one (by linear_combination h)
  have hone_sub : 1 - s ≠ 0 := fun h => hs_ne_one (by linear_combination -h)
  refine ⟨hone_add, ?_⟩
  -- Suppose `A ^ 2 s = B (1 + s) ^ 2`.
  intro hcontra
  have heq : P.A ^ 2 * s = P.B * (1 + s) ^ 2 := by rw [← hcontra]; ring
  -- `s ≠ 0`, since `A ^ 2 * 0 = B` would contradict `B ≠ 0`.
  have hs_ne_zero : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at heq
    exact B_ne_zero P (by linear_combination -heq)
  -- Subtracting `4Bs` gives `(A ^ 2 - 4B) s = B (1 - s) ^ 2`.
  have hsub : (P.A ^ 2 - 4 * P.B) * s = P.B * (1 - s) ^ 2 := by linear_combination heq
  -- Multiplying by `A ^ 2 s` gives `(A ^ 2 - 4B) A ^ 2 s ^ 2 = B ^ 2 (1 + s) ^ 2 (1 - s) ^ 2`.
  have hmul : (P.A ^ 2 - 4 * P.B) * (P.A * s) ^ 2 =
      (P.B * ((1 + s) * (1 - s))) ^ 2 := by
    linear_combination (P.A ^ 2 * s) * hsub + (P.B * (1 - s) ^ 2) * heq
  -- The left hand side has character `-1`, the right hand side character `1`.
  have hAs_ne_zero : P.A * s ≠ 0 := mul_ne_zero (A_ne_zero P) hs_ne_zero
  have hright_ne_zero : P.B * ((1 + s) * (1 - s)) ≠ 0 :=
    mul_ne_zero (B_ne_zero P) (mul_ne_zero hone_add hone_sub)
  have hleft : χ ((P.A ^ 2 - 4 * P.B) * (P.A * s) ^ 2) = -1 := by
    rw [χ_of_a_eq_χ_a_mul_b_pow_two hAs_ne_zero]
    exact χ_of_not_isSquare disc_nonsquare
  rw [hmul, χ_sq hright_ne_zero] at hleft
  exact absurd (by linear_combination hleft : (2 : F) = 0) two_ne_zero_of_odd_card

end admissible

end Elligator.Elligator2.CurveParameters
