/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Reconstruction Coordinates

The quantities `η`, `X̄` (`Xbar`), `z`, `ū` (`ubar`), `t̄` (`tbar`) reconstructed from a curve
point, mirroring the forward chain `u, v, X, Y, t` of `AuxiliaryCoordinates.lean` in reverse.
Together with the base-case (`t = ±1`) values of each and the `X ↔ X̄` relation needed to prove
`X̄` well-defined.

## Main Results

* `η`, `Xbar`, `z`, `ubar`, `tbar`: the reconstruction quantities of [bernstein2013a],
  Section 3.3, Theorem 3.
* `X_quadratic_eq_of_y`, `X_quadratic_eq_of_η`, `X_add_inv_X_eq_neg_two_mul_one_add_η_mul_r`:
  relate `η` back to the forward-map quantities `X`, `y`.
* `X_comparison_implication`, `X_comparison_implication2`: `X`'s behavior under `t ↦ -t`,
  restated in terms of `η · r`.
* `ubar_eq_u`, `ubar_eq_u'`, `tbar_eq_t`, `tbar_eq_t'`: identify the reconstructed quantities
  with the forward-map values at `t` or `-t`, the key step of Theorem 3's inversion proof.

## References

See [bernstein2013a], Section 3.3, Theorem 3.
-/

@[expose] public section

namespace Elligator.Elligator1.ReconstructionCoordinates

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates

variable {F : Type*} [Field F]
variable (I : InputData F)
variable (M : MapData F)
variable (Q : PointData F)

section η

/-- η(s, q, point) is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:η"
  (title := "The inversion quantity $\\eta$")
  (statement := /--
  For a point $(x, y)$ of $E(\mathbb{F}_q)$ with $y + 1 \neq 0$, define
  $$
  \eta = \frac{y - 1}{2(y + 1)} .
  $$
  -/)]
def η (P : F × F) : F :=
    let y := P.snd
    (y - 1) / (2 * (y + 1))

/-- PointData wrapper for η. -/
def _root_.Elligator.PointData.η : F := ReconstructionCoordinates.η Q.P

lemma _root_.Elligator.PointData.η_eq_y : Q.η = (Q.y - 1) / (2 * (Q.y + 1)) := rfl

variable [Fintype F] [DecidableEq F]

/-- MapData wrapper for η.

Due to `MapData.decoded_P_eq_point_P`, we are allowed to use `M.η` instead of `Q.η` in theorems,
which would mix both a `MapData` and a `PointData` structure.
(which would otherwise result in 2 distinct `s`)
-/
def _root_.Elligator.MapData.η
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] : F :=
    M.decoded.η

lemma _root_.Elligator.MapData.η_eq_y
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.decoded.η = (M.y - 1) / (2 * (M.y + 1)) := by
  rw [M.decoded_eq_point]
  exact M.point.η_eq_y

-- Used in Theorem 3 Proof B part as implication for P_in_ϕOverF_with_prop2_main_case argument.
lemma X_quadratic_eq_of_y
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.X ^ 2 + (2 + M.r * (M.y - 1) / (M.y + 1)) * M.X + 1 = 0 := by
  rw [← mul_left_inj' (y_add_one_ne_zero M)]
  repeat rw [add_mul]
  rw [zero_mul]
  have h_factor_X : (2 * M.X * (M.y + 1) + M.r * (M.y - 1) / (M.y + 1) * M.X * (M.y + 1))
      = (2 * (M.y + 1) + M.r * (M.y - 1)) * M.X := by
    rw [add_mul _ _ M.X, ← div_left_inj' (y_add_one_ne_zero M)]
    repeat rw [add_div, mul_div_assoc, div_self (y_add_one_ne_zero M)]
    rw [mul_comm (2 * (M.y + 1)) M.X, ← mul_assoc]
    nth_rw 2 [mul_div_assoc]
    rw [div_self (y_add_one_ne_zero M)]
    ring
  have h_expand_coefficient : (2 * (M.y + 1) + M.r * (M.y - 1))
      = (M.y * M.r - M.r + 2 * M.y + 2) := by ring
  rw [h_factor_X, h_expand_coefficient, mul_add, add_mul]
  ring_nf
  rw [← add_right_inj (M.r * M.X - 1 - 2 * M.X - M.X ^ 2)]
  ring_nf
  rw [mul_comm (M.X ^ 2) M.y, mul_comm M.X M.y, mul_assoc, mul_assoc]
  nth_rw 4 [← mul_one M.y]
  rw [add_assoc, ← mul_add M.y]
  rw [add_assoc, ← mul_add M.y, add_comm (M.X ^ 2) 1, ← add_assoc, add_comm (M.X * 2) 1]
  rw [mul_comm M.X 2]
  have h_perfect_square : 1 + 2 * M.X + M.X ^ 2 = (1 + M.X) ^ 2 := by ring
  have h_regroup : -1 + M.r * M.X - 2 * M.X - M.X ^ 2
      = M.r * M.X - (1 + 2 * M.X + M.X ^ 2) := by ring
  rw [h_regroup, h_perfect_square]
  rw [← mul_assoc, mul_comm, ← mul_add]
  rw [← div_left_inj' (y_divisor_ne_zero M)]
  rw [mul_div_assoc]
  rw [div_self (y_divisor_ne_zero M), mul_one]
  rfl

-- Implicated by X_quadratic_eq_of_y. Saved for further proof arguments in Theorem 3 Proof B
lemma X_quadratic_eq_of_η
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.X ^ 2 + 2 * (1 + M.η * M.r) * M.X + 1 = 0 := by
  calc
    M.X ^ 2 + 2 * (1 + M.η * M.r) * M.X + 1 =
        M.X ^ 2 + 2 * (1 + 1 / 2 * ((M.y - 1) / (M.y + 1)) * M.r) * M.X + 1 := by
      -- Unfold until reaching the y which is equivalent to y for comparison
      rw [MapData.η, M.η_eq_y]
      rw [one_div, inv_eq_one_div, ← mul_div_mul_comm]
      ring
    _ = M.X ^ 2 + (2 + M.r * (M.y - 1) / (M.y + 1)) * M.X + 1 := by
      rw [mul_add 2]
      rw [div_eq_mul_inv 1 2, mul_one, one_mul, mul_assoc, ← mul_assoc]
      rw [mul_inv_cancel₀ (two_ne_zero card_mod_four)]
      ring
    _ = 0 := by rw [X_quadratic_eq_of_y M]

-- Implicated by X_quadratic_eq_of_η.
lemma X_add_inv_X_eq_neg_two_mul_one_add_η_mul_r
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.X + 1 / M.X = -2 * (1 + M.η * M.r) := by
  rw [← add_right_inj (2 * (1 + M.η * M.r))]
  rw [← mul_left_inj' (X_ne_zero M)]
  have h_cancel_terms : (2 * (1 + M.η * M.r) + -2 * (1 + M.η * M.r)) * M.X = 0 := by ring
  rw [h_cancel_terms, ← X_quadratic_eq_of_η M]
  ring_nf
  rw [mul_inv_cancel₀ (X_ne_zero M)]
  ring

-- Typical classes and structures not used here since indeed a rare special case.
lemma ϕ_of_t_eq_zero_one {s : F} (t : { n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_mod : Fintype.card F % 4 = 3) :
    let ϕ := ϕ t.val hs_ne_zero sq_ne_pm_two hq_mod
    ϕ.val = (0, 1) := by
  intro ϕ
  unfold ϕ Elligator1.ϕ
  rcases t.prop with h | h <;> simp [h]

lemma η_eq_zero {s : F} (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_mod : Fintype.card F % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_mod).val
    (η P) = 0 := by
  intro P
  unfold η
  let y := P.2
  change (y - 1) / (2 * (y + 1)) = 0
  unfold y P
  rw [ϕ_of_t_eq_zero_one t hs_ne_zero sq_ne_pm_two hq_mod]
  rw [sub_self, zero_div]

lemma y_add_one_eq_two {s : F} (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_mod : Fintype.card F % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_mod).val
    let y := P.2
    y + 1 = 2 := by
  intro P y
  unfold y P
  rw [ϕ_of_t_eq_zero_one t hs_ne_zero sq_ne_pm_two hq_mod]
  ring

end η

section comparison

lemma u_comparison : M.neg.u = 1 / M.u := by
  calc
    M.neg.u = (1 -  M.neg.t) / (1 + M.neg.t) := by rfl
    _ = (1 + M.t) / (1 - M.t) := by simp [MapData.neg, InputData.neg]; ring
    _ = 1 / M.u := by simp [InputData.u, u]; rfl

lemma v_comparison : M.neg.v = 1 / M.u ^ 5 + (M.r ^ 2 - 2) * 1 / M.u ^ 3 + 1 / M.u := by
  calc
    M.neg.v = M.neg.u ^ 5 + (M.r ^ 2 - 2) * M.neg.u ^ 3 + M.neg.u := by rfl
    _ = 1 / M.u ^ 5 + (M.r ^ 2 - 2) * 1 / M.u ^ 3 + 1 / M.u := by
      rw [u_comparison M]
      ring

lemma v_comparison_implication1 : M.neg.v * M.u ^ 6 = M.v := by
  calc
    M.neg.v * M.u ^ 6 = M.u + (M.r ^ 2 - 2) * M.u ^ 3 + M.u ^ 5 := by
      rw [v_comparison M]
      grind
    _ = M.v := by
      unfold MapData.v InputData.u ParamData.r v
      ring

lemma v_comparison_implication2 :
    M.neg.v = M.v / M.u ^ 6 := by
  have hu1_pow6_ne_zero : M.u ^ 6 ≠ 0 := pow_ne_zero 6 (u_ne_zero M.toInputData)
  rw [← mul_right_inj' hu1_pow6_ne_zero]
  rw [← v_comparison_implication1 M]
  grind

variable [Fintype F] [DecidableEq F]

lemma v_comparison_implication3 : χ (I.u ^ 6) = (1 : F) := by
  have hu6_eq_u2_mul_u2_mul_u2 : I.u ^ 6 = I.u ^ 2 * I.u ^ 2 * I.u ^ 2 := by ring
  rw [hu6_eq_u2_mul_u2_mul_u2, χ_mul, χ_mul, χ_sq (u_ne_zero I)]
  rw [mul_one, mul_one]

lemma v_comparison_implication4 : χ M.neg.v = χ M.v := by
  rw [← v_comparison_implication1 M]
  rw [χ_mul, v_comparison_implication3 M.toInputData, mul_one]

lemma X_comparison : M.neg.X = 1 / M.X := by
  calc
    M.neg.X = (χ M.neg.v) * M.neg.u := by rfl
    _ = (χ M.v) / M.u := by
      rw [v_comparison_implication4 M]
      rw [u_comparison M]
      ring
    _ = 1 / ((χ M.v) * M.u) := by
      nth_rw 1 [one_div_χ_of_a_eq_χ_a]
      ring
    _ = 1 / M.X := by rfl

lemma Y_comparison [IsNonzeroParam M.s] [IsCardThreeModFour F] :
    M.neg.Y = M.Y / M.X ^ 3 := by
  have first_factor :
    ((χ M.neg.v) * M.neg.v) ^ (((Fintype.card F) + 1) / 4)
        = ((χ M.v) * M.v) ^ (((Fintype.card F) + 1) / 4) * (χ M.u) / M.u ^ 3 := by
      have h_v2_mul_v2_eq_v1_mul_v1_div_u1_pow6 : (χ M.neg.v) * M.neg.v
          = (χ M.v) * M.v / M.u ^ 6 := by
        rw [v_comparison_implication4 M, v_comparison_implication2 M]
        rw [← mul_div_assoc]
      have h_χ_u1_mul_u1_cubed_isSquare : IsSquare ((χ M.u) * M.u ^ 3) := by
        have h_χ_u1_mul_u1_cubed_ne_zero : (χ M.u) * M.u ^ 3 ≠ 0 := by
          apply mul_ne_zero
          · exact χ_a_ne_zero (u_ne_zero M.toInputData)
          · exact pow_ne_zero 3 (u_ne_zero M.toInputData)
        apply (χ_eq_one_iff_isSquare h_χ_u1_mul_u1_cubed_ne_zero card_mod_four).mp
        have h_three_eq_one_add_two : (3 : ℕ) = 1 + 2 := by norm_num
        rw [h_three_eq_one_add_two, pow_add M.u 1 2, ← mul_assoc, pow_one]
        rw [χ_mul, χ_mul, χ_χ_eq_χ card_mod_four, ← χ_mul, ← pow_two]
        have h_χ_u1_sq_eq_one : χ (M.u ^ 2) = 1 := by
          apply (χ_eq_one_iff_isSquare (pow_ne_zero 2 (u_ne_zero M.toInputData)) card_mod_four).mpr
          exact IsSquare.sq M.u
        simp [h_χ_u1_sq_eq_one]
      have h_u1_pow6_pow_eq_χ_u1_mul_u1_cubed : (M.u ^ 6) ^ (((Fintype.card F) + 1) / 4)
          = (χ M.u) * M.u ^ 3 := by
        have h_six_eq_three_mul_two : 6 = 3 * 2 := by norm_num
        rw [h_six_eq_three_mul_two, ← pow_mul, mul_assoc, mul_comm, pow_mul, mul_comm]
        rw [add_comm, one_add_q_div_four_mul_two_eq_one_add_q_div_two card_mod_four]
        rw [add_comm, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a card_mod_four]
        change ((χ M.u) * M.u) ^ 3 = (χ M.u) * M.u ^ 3
        rw [mul_pow, χ_of_a_pow_n_eq_χ_a M.u ⟨3, by trivial⟩]
      calc
        ((χ M.neg.v) * M.neg.v) ^ (((Fintype.card F) + 1) / 4)
            = ((χ M.v) * M.v / M.u ^ 6) ^ (((Fintype.card F) + 1) / 4) := by
          rw [h_v2_mul_v2_eq_v1_mul_v1_div_u1_pow6]
        _ = ((χ M.v) * M.v) ^ (((Fintype.card F) + 1) / 4) * (χ M.u) / M.u ^ 3 := by
          rw [div_pow, h_u1_pow6_pow_eq_χ_u1_mul_u1_cubed]
          nth_rw 2 [one_div_χ_of_a_eq_χ_a]
          grind
  have second_factor : (χ M.neg.v) = (χ M.v) := v_comparison_implication4 M
  have third_factor : χ (M.neg.u ^ 2 + 1 / M.c ^ 2) = χ (M.u * M.v * (M.u ^ 2 + 1 / M.c ^ 2)) := by
    calc
      χ (M.neg.u ^ 2 + 1 / M.c ^ 2)
        = χ ((M.c ^ 2 * M.u ^ 4 * (M.neg.u ^ 2 + 1 / M.c ^ 2)) * (M.u ^ 2 + 1 / M.c ^ 2) ^ 2) := by
        rw [← χ_of_a_eq_χ_a_mul_b_pow_two (c_ne_zero M.toParamData)]
        rw [mul_comm, ← χ_of_a_eq_χ_a_mul_b_pow_two (pow_ne_zero 2 (u_ne_zero M.toInputData))]
        rw [χ_of_a_eq_χ_a_mul_b_pow_two (v_factored_third_factor_ne_zero M)]
        grind
      _ = χ ((M.u ^ 2 * (M.c ^ 2 + M.u ^ 2)) * (M.u ^ 2 + 1 / M.c ^ 2) ^ 2) := by
        rw [pow_two M.neg.u]
        rw [u_comparison M]
        have h_clear_denominators :
            M.c ^ 2 * M.u ^ 4 * (1 / M.u * (1 / M.u) + 1 / M.c ^ 2)
              = M.u ^ 2 * (M.c ^ 2 + M.u ^ 2) := by
          have hc_sq_ne_zero : M.c ^ 2 ≠ 0 := pow_ne_zero 2 (c_ne_zero M.toParamData)
          grind
        rw [h_clear_denominators]
      _ = χ (M.u * M.v * (M.u ^ 2 + 1 / M.c ^ 2)) := by grind [v_factored]
  calc
    M.neg.Y = M.Y * (χ M.u) * χ (M.u * M.v) / M.u ^ 3 := by
      change ((χ M.neg.v) * M.neg.v) ^ (((Fintype.card F) + 1) / 4)
        * (χ M.neg.v) * χ (M.neg.u ^ 2 + 1 / M.c ^ 2)
        = M.Y * (χ M.u) * χ (M.u * M.v) / M.u ^ 3
      rw [first_factor, second_factor, third_factor, χ_mul]
      have h_rearrange :
        ((χ M.v) * M.v) ^ (((Fintype.card F) + 1) / 4) * (χ M.u) / M.u ^ 3 * (χ M.v)
        * (χ (M.u * M.v) * (χ (M.u ^ 2 + 1 / M.c ^ 2)))
        = ((χ M.v) * M.v) ^ (((Fintype.card F) + 1) / 4) * (χ M.v) * (χ (M.u ^ 2 + 1 / M.c ^ 2))
          * (χ M.u) * χ (M.u * M.v) / M.u ^ 3 := by ring
      rw [h_rearrange]
      rfl
    _ = M.Y / ((χ M.v) * M.u) ^ 3 := by
      calc
      M.Y * (χ M.u) * χ (M.u * M.v) / M.u ^ 3 = M.Y * (χ M.v) / M.u ^ 3 := by
        rw [χ_mul, ← mul_assoc, mul_assoc M.Y, ← χ_mul, ← pow_two]
        rw [χ_sq (u_ne_zero M.toInputData), mul_one]
      _ = M.Y / ((χ M.v) * M.u) ^ (2 + 1) := by
        nth_rw 1 [one_div_χ_of_a_eq_χ_a]
        rw [mul_div_assoc, div_div]
        nth_rw 1 [← χ_of_a_pow_n_eq_χ_a M.v ⟨3, by trivial⟩, ← mul_pow]
        ring_nf
    _ = M.Y / M.X ^ 3 := by rfl

lemma X_comparison_implication
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.X + M.neg.X = -2 * (1 + M.η * M.r) := by
  rw [X_comparison M]
  exact X_add_inv_X_eq_neg_two_mul_one_add_η_mul_r M

lemma X_comparison_implication2
    [IsNonzeroParam M.s] [IsCardThreeModFour F] :
    M.neg.X * M.X = 1 := by
  rw [X_comparison M]
  rw [← inv_eq_one_div, inv_mul_cancel₀ (X_ne_zero M)]

lemma x_comparison [IsNonzeroParam M.s] [IsCardThreeModFour F] : M.neg.x = M.x := by
  have hX1_pow3_ne_zero : M.X ^ 3 ≠ 0 := pow_ne_zero 3 (X_ne_zero M)
  calc
    M.neg.x = (M.c - 1) * M.s * M.neg.X * (1 + M.neg.X) / M.neg.Y := by rfl
    _ = (M.c - 1) * M.s * 1 / M.X * (1 + 1 / M.X) / (M.Y / M.X ^ 3) := by
      grind [X_comparison, Y_comparison]
    _ = (M.c - 1) * M.s * M.X * (1 + M.X) / M.Y := by simp_all; grind
    _ = M.x := by rfl

lemma y_comparison : M.neg.y = M.y := by
  calc
    M.neg.y = (M.r * M.neg.X - (1 + M.neg.X) ^ 2) / (M.r * M.neg.X + (1 + M.neg.X) ^ 2) := by rfl
    _ = (M.r * (1 / M.X) - (1 + (1 / M.X)) ^ 2) / (M.r * (1 / M.X) + (1 + (1 / M.X)) ^ 2) := by
      rw [X_comparison M]
    _ = (M.r * M.X - (M.X + 1) ^ 2) / (M.r * M.X + (M.X + 1) ^ 2) := by grind
    _ = M.y := by
      rw [add_comm]
      rfl

lemma P_comparison [IsNonzeroParam M.s] [IsCardThreeModFour F] :
    (M.x, M.y) = (M.neg.x, M.neg.y) := by
  rw [x_comparison M, y_comparison M]

end comparison

variable [Fintype F] [DecidableEq F]

section Xbar

/-- Xbar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:Xbar"
  (title := "The reconstructed coordinate $\\bar X$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\eta$ as above, define
  $$
  \bar X = -(1 + \eta r) + ((1 + \eta r) ^ 2 - 1)^{(q+1)/4} .
  $$
  -/)]
def Xbar (s : F) (P : F × F) (q : ℕ) : F :=
    let η := η P
    let r := r s
    (-(1 + η * r) + ((1 + η * r) ^ 2 - 1) ^ ((q + 1) / 4))

/-- PointData wrapper for η. -/
def _root_.Elligator.PointData.Xbar : F := ReconstructionCoordinates.Xbar Q.s Q.P (Fintype.card F)

def _root_.Elligator.MapData.Xbar
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] : F :=
    M.decoded.Xbar

lemma Xbar_eq_neg_one
    (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let Xbar := Xbar s P.1 q
    Xbar = -1 := by
  intro P Xbar
  unfold Xbar ReconstructionCoordinates.Xbar
  let η := η P.1
  change -(1 + η * (r s)) + ((1 + η * (r s)) ^ 2 - 1) ^ ((q + 1) / 4) = -1
  unfold η
  rw [η_eq_zero t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  ring_nf
  rw [zero_pow, add_zero]
  omega

end Xbar

section z

/-- z is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:z"
  (title := "The inversion sign $z$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\bar X$ as above, define
  $$
  z = \chi\bigl((c - 1)s\bar X(1 + \bar X)x(\bar X ^ 2 + 1/c ^ 2)\bigr) .
  $$
  -/)]
def z (s : F) (P : F × F) (q : ℕ) : F :=
    let x := P.fst
    let c := c s
    let Xbar := Xbar s P q
    χ ((c - 1) * s * Xbar * (1 + Xbar) * x * (Xbar ^ 2 + 1 / c ^ 2))

lemma z_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let z := z s P q
    z = 0 := by
  intro P z
  unfold z ReconstructionCoordinates.z
  repeat rw [Xbar_eq_neg_one t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  simp_all

omit [DecidableEq F] in
lemma Xbar_pow_two_add_one_div_c_pow_two_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s}) :
    let X := Xbar s P q
    let c := c s
    X ^ 2 + 1 / c ^ 2 ≠ 0 := by
  intro X c h_sum_eq_zero
  rw [← mul_left_inj' (c_ne_zero hs_ne_zero hq_card hq_mod)] at h_sum_eq_zero
  rw [← mul_left_inj' (c_ne_zero hs_ne_zero hq_card hq_mod)] at h_sum_eq_zero
  ring_nf at h_sum_eq_zero
  change X ^ 2 * c ^ 2 + c⁻¹ ^ 2 * c ^ 2 = 0 at h_sum_eq_zero
  rw [inv_pow c 2,
    inv_mul_cancel₀ (pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod))] at h_sum_eq_zero
  rw [← add_left_inj (-1 : F), ← mul_pow] at h_sum_eq_zero
  simp only [add_neg_cancel_right, zero_add] at h_sum_eq_zero
  have h_neg_one_non_square := neg_one_non_square hq_card hq_mod
  have h_isSquare_neg_one : IsSquare (-1 : F) := by
    rw [← h_sum_eq_zero, pow_two]
    apply IsSquare.mul_self
  contradiction

end z

section ubar

/-- ubar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:ubar"
  (title := "The reconstructed quantity $\\bar u$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $z$ and $\bar X$ as above, define
  $$
  \bar u = z\bar X .
  $$
  -/)]
def ubar (s : F) (P : F × F) (q : ℕ) : F :=
    let Xbar := Xbar s P q
    let z := z s P q
    z * Xbar

lemma ubar_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let ubar := ubar s P q
    ubar = 0 := by
  grind [z_eq_zero, ubar]

-- TODO find proper place
lemma χ_IsSquare_h1 [DecidableEq F]
    (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let v := v t s
    IsSquare (((χ v) * v) ^ ((q + 1) / 4)) := by
  intro v
  have hv_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
  have hχ_a_mul_a_IsSquare := χ_a_mul_a_IsSquare hv_ne_zero hq_card hq_mod
  unfold IsSquare at hχ_a_mul_a_IsSquare
  rcases hχ_a_mul_a_IsSquare with ⟨r, hr⟩
  rw [hr, ← pow_two, ← pow_mul, mul_comm, pow_mul]
  exact IsSquare.sq _

lemma ubar_eq_u (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      let X := X t s
      let Xbar := Xbar s P q
      Xbar = X) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let u := u t
    let ubar := ubar s P q
    ubar = u := by
  intro P u ubar
  let X := X t s
  let Xbar := Xbar s P q
  let c := c s
  let x := x t s q
  let Y := Y t s q
  let z := z s P q
  let v := v t s;
  unfold ubar ReconstructionCoordinates.ubar
  rw [hXXbar]
  change z * X = u
  have hXbar_expand_eq_x_mul_Y : (c - 1) * s * Xbar * (1 + Xbar) = x * Y := by
    unfold Xbar
    rw [hXXbar]
    rw [← div_left_inj' (Y_ne_zero hs_ne_zero hq_card hq_mod t)]
    change x = x * Y / Y
    rw [mul_div_assoc, div_self (Y_ne_zero hs_ne_zero hq_card hq_mod t)]
    ring_nf
  have hz_eq_χY_mul_χ_sum : z = (χ Y) * χ (X ^ 2 + 1 / c ^ 2) := by
    calc
      z = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2)) := by
        unfold z ReconstructionCoordinates.z
        change χ ((c - 1) * s * Xbar * (1 + Xbar) * P.1 * (Xbar ^ 2 + 1 / c ^ 2))
          = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2))
        unfold P ϕ
        simp only [hXbar_expand_eq_x_mul_Y]
        rw [dite_eq_left t.prop]
        change χ (x * Y * x * (Xbar ^ 2 + 1 / c ^ 2)) = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2))
        unfold Xbar X
        rw [hXXbar]
        ring_nf
      _ = (χ Y) * χ (X ^ 2 + 1 / c ^ 2) := by
        rw [χ_mul, χ_mul]
        rw [χ_a_eq_one (pow_ne_zero 2
          (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t))
          (IsSquare.sq x)]
        ring
  have hχu_sum_eq_χX_sum : χ (u ^ 2 + 1 / c ^ 2) = χ (X ^ 2 + 1 / c ^ 2) := by
    unfold X AuxiliaryCoordinates.X
    rw [mul_pow]
    nth_rw 3 [pow_two]
    rw [← χ_mul]
    rw [← pow_two, χ_a_eq_one
      (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod t)) (IsSquare.sq v)]
    unfold u
    simp_all
  have hχY_eq_χv_mul_χ_sum : χ Y = (χ v) * χ (X ^ 2 + 1 / c ^ 2) := by
    rw [← hχu_sum_eq_χX_sum]
    unfold Y AuxiliaryCoordinates.Y
    change χ (((χ v) * v) ^ ((q + 1) / 4) * (χ v) * χ (u ^ 2 + 1 / c ^ 2))
      = (χ v) * χ (u ^ 2 + 1 / c ^ 2)
    rw [mul_assoc, χ_mul]
    rw [χ_a_eq_one
      (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero t hs_ne_zero hq_card hq_mod)
      (χ_IsSquare_h1 t hs_ne_zero hq_card hq_mod)]
    rw [χ_mul]
    rw [χ_χ_eq_χ hq_card hq_mod]
    rw [χ_χ_eq_χ hq_card hq_mod]
    simp_all
  have hz_eq_χv : z = χ v := by
    rw [hz_eq_χY_mul_χ_sum, hχY_eq_χv_mul_χ_sum, mul_assoc, ← χ_mul, ← pow_two]
    rw [χ_a_eq_one
      (pow_ne_zero 2 (X_pow_two_add_one_div_c_pow_two_ne_zero hs_ne_zero hq_card hq_mod t))
      (IsSquare.sq (X ^ 2 + 1 / c ^ 2))]
    simp
  rw [hz_eq_χv]
  unfold X AuxiliaryCoordinates.X
  change (χ v) * ((χ v) * u) = u
  rw [← mul_assoc, ← χ_mul, ← pow_two]
  have hv_sq_isSquare : IsSquare (v ^ 2) := IsSquare.sq v
  rw [χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod t)) hv_sq_isSquare]
  simp

lemma ubar_eq_u' (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
      let Xbar := Xbar s P q
      Xbar = X') :
    let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let u' := u ⟨-t.val, t_h⟩
    let ubar := ubar s P q
    ubar = u' := by
  intro t_h P u' ubar
  let X' := X ⟨-t.val, t_h⟩ s
  let X := X t s
  let Xbar := Xbar s P q
  let c := c s
  let x' := x ⟨-t.val, t_h⟩ s q
  let x := x t s q
  let Y' := Y ⟨-t.val, t_h⟩ s q
  let Y := Y t s q
  let z := z s P q
  let v' := v ⟨-t.val, t_h⟩ s
  let v := v t s;
  unfold ubar ReconstructionCoordinates.ubar
  rw [hXXbar]
  change z * X' = u'
  have hXbar_expand_eq_x'_mul_Y' : (c - 1) * s * Xbar * (1 + Xbar) = x' * Y' := by
    unfold Xbar
    rw [hXXbar]
    rw [← div_left_inj' (Y_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩)]
    change x' = x' * Y' / Y'
    rw [mul_div_assoc, div_self (Y_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩)]
    ring_nf
  have hz_eq_χY'_mul_χ_sum : z = (χ Y') * (χ (X'^2 + 1 / c ^ 2)) := by
    calc
      z = (χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))) := by
        unfold z ReconstructionCoordinates.z
        change χ ((c - 1) * s * Xbar * (1 + Xbar) * P.1 * (Xbar ^ 2 + 1 / c ^ 2))
          = χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))
        unfold P ϕ
        simp only [hXbar_expand_eq_x'_mul_Y']
        rw [dite_eq_left t.prop]
        change χ (x' * Y' * x * (Xbar ^ 2 + 1 / c ^ 2)) = χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))
        unfold Xbar X' x' x
        rw [x_comparison t hs_ne_zero hq_card hq_mod]
        rw [hXXbar]
        ring_nf
      _ = (χ Y') * χ (X'^2 + 1 / c ^ 2) := by
        rw [χ_mul]
        rw [χ_mul]
        rw [χ_a_eq_one (pow_ne_zero 2
          (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod ⟨-t, t_h⟩))
          (IsSquare.sq x')]
        ring_nf
  have hχu'_sum_eq_χX'_sum : (χ (u'^2 + 1 / c ^ 2)) = (χ (X'^2 + 1 / c ^ 2)) := by
    unfold X' AuxiliaryCoordinates.X
    rw [mul_pow]
    nth_rw 3 [pow_two]
    rw [← χ_mul]
    rw [← pow_two, χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod ⟨-t, t_h⟩))
      (IsSquare.sq v')]
    unfold u'
    simp_all
  have hχY'_eq_χv'_mul_χ_sum : (χ Y') = (χ v') * (χ (X'^2 + 1 / c ^ 2)) := by
    rw [← hχu'_sum_eq_χX'_sum]
    unfold Y' AuxiliaryCoordinates.Y
    let χ_sum := χ (u'^2 + 1 / c ^ 2);
    change (χ (((χ v') * v') ^ ((q + 1) / 4) * (χ v') * χ_sum)) = (χ v') * χ_sum
    rw [mul_assoc, χ_mul]
    rw [χ_a_eq_one
      (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero ⟨-t.val, t_h⟩ hs_ne_zero hq_card hq_mod)
      (χ_IsSquare_h1 ⟨-t.val, t_h⟩ hs_ne_zero hq_card hq_mod)]
    rw [χ_mul, χ_χ_eq_χ hq_card hq_mod]
    rw [χ_χ_eq_χ hq_card hq_mod]
    unfold χ_sum
    simp_all
  have hz_eq_χv' : z = (χ v') := by
    rw [hz_eq_χY'_mul_χ_sum, hχY'_eq_χv'_mul_χ_sum, mul_assoc]
    rw [← χ_mul, ← pow_two]
    rw [χ_a_eq_one (pow_ne_zero 2
        (X_pow_two_add_one_div_c_pow_two_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩))
      (IsSquare.sq (X'^2 + 1 / c ^ 2))]
    simp
  rw [hz_eq_χv']
  unfold X' AuxiliaryCoordinates.X
  change (χ v') * ((χ v') * u') = u'
  rw [← mul_assoc, ← χ_mul, ← pow_two]
  have hv'_sq_isSquare : IsSquare (v'^2) := IsSquare.sq v'
  rw [χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩))
    hv'_sq_isSquare]
  simp

lemma one_add_ubar_ne_zero_base_case (t : {n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    let ubar := ubar s P q
    1 + ubar ≠ 0 := by
  intro P ubar
  unfold ubar
  rw [ubar_eq_zero, add_zero]
  exact one_ne_zero' F

end ubar

section tbar

/-- tbar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:tbar"
  (title := "The reconstructed preimage $\\bar t$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\bar u$ as above, define
  $$
  \bar t = (1 - \bar u)/(1 + \bar u) .
  $$
  -/)]
def tbar (s : F) (P : F × F) (q : ℕ) : F :=
    let ubar := ubar s P q
    (1 - ubar) / (1 + ubar)

lemma tbar_eq_one (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let tbar := tbar s P q
    tbar = 1 := by
  intro P tbar_of_P
  unfold tbar_of_P tbar
  let ubar_of_P := ubar s P q
  change (1 - ubar_of_P) / (1 + ubar_of_P) = 1
  unfold ubar_of_P
  rw [ubar_eq_zero t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  simp

lemma tbar_eq_t (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let X := X t s
      let Xbar := Xbar s P q
      Xbar = X) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let tbar_of_P := tbar s P q
    tbar_of_P = t := by
  intro P tbar_of_P
  let u := u t
  let ubar := ubar s P q
  have hubar_eq_u : ubar = u := ubar_eq_u t hs_ne_zero sq_ne_pm_two hq_card hq_mod hXXbar
  unfold u AuxiliaryCoordinates.u at hubar_eq_u
  unfold tbar_of_P tbar
  change (1 - ubar) / (1 + ubar) = t.val
  change ubar = (1 - t.val) / (1 + t.val) at hubar_eq_u
  rw [hubar_eq_u, sub_div' (one_add_t_ne_zero t)]
  rw [add_div' (1 - t.val) 1 (1 + t.val) (one_add_t_ne_zero t)]
  rw [div_div_div_eq]
  have h_denom_ne_zero : (1 + t.val) * 2 ≠ 0 :=
    mul_ne_zero (one_add_t_ne_zero t) (two_ne_zero hq_card hq_mod)
  grind

lemma tbar_eq_t' (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
      let Xbar := Xbar s P q
      Xbar = X')
    :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let tbar_of_P := tbar s P q
    let t' := -t.val
    tbar_of_P = t' := by
  intro P tbar_of_P t'
  have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let u' := u ⟨t', t_h⟩
  let ubar := ubar s P q
  have hubar_eq_u' : ubar = u' := ubar_eq_u' t hs_ne_zero sq_ne_pm_two hq_card hq_mod hXXbar
  unfold u' u at hubar_eq_u'
  unfold tbar_of_P tbar
  change (1 - ubar) / (1 + ubar) = t'
  change ubar = (1 - t') / (1 + t') at hubar_eq_u'
  rw [hubar_eq_u', sub_div' (one_add_t_ne_zero ⟨t', t_h⟩)]
  rw [add_div' (1 - t') 1 (1 + t') (one_add_t_ne_zero ⟨t', t_h⟩), div_div_div_eq]
  have h_denom_ne_zero : ((1 + t') * 2) ≠ 0 :=
    mul_ne_zero (one_add_t_ne_zero ⟨t', t_h⟩) (two_ne_zero hq_card hq_mod)
  grind

end tbar

end Elligator.Elligator1.ReconstructionCoordinates
