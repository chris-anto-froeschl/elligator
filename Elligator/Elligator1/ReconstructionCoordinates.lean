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
variable (D : ParamData F)
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

/-- The two exceptional inputs `t = ± 1` are both decoded to the neutral point `(0, 1)`.

The input is the bare subtype `{n : F // n = 1 ∨ n = -1}` rather than an `InputData`, since these
are precisely the two inputs an `InputData` excludes. -/
lemma ϕ_of_t_eq_zero_one [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]
    (t : { n : F // n = 1 ∨ n = -1}) :
    (D.ϕ t.val).val = (0, 1) := by
  unfold ParamData.ϕ Elligator1.ϕ
  rcases t.prop with h | h <;> simp [h]

lemma η_eq_zero [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]
    (t : { n : F // n = 1 ∨ n = -1}) :
    (D.decoded t.val).η = 0 := by
  have hP : (D.decoded t.val).P = ((0 : F), (1 : F)) := ϕ_of_t_eq_zero_one D t
  unfold PointData.η η
  rw [hP]
  norm_num

lemma y_add_one_eq_two [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]
    (t : { n : F // n = 1 ∨ n = -1}) :
    (D.decoded t.val).y + 1 = 2 := by
  have hP : (D.decoded t.val).P = ((0 : F), (1 : F)) := ϕ_of_t_eq_zero_one D t
  unfold PointData.y
  rw [hP]
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

/-- MapData wrapper for Xbar, evaluated at the point decoded from the input `t`. -/
def _root_.Elligator.MapData.Xbar
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] : F :=
    M.decoded.Xbar

/-- The decoded point does not change when the input `t` is replaced by `-t`. -/
lemma _root_.Elligator.MapData.neg_decoded_P
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.neg.decoded.P = M.decoded.P := by
  rw [M.neg.decoded_P_eq_point_P, M.decoded_P_eq_point_P]
  change (M.neg.x, M.neg.y) = (M.x, M.y)
  rw [x_comparison M, y_comparison M]

/-- Hence the reconstructed coordinate `X̄` does not change either. -/
lemma _root_.Elligator.MapData.neg_Xbar
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.neg.Xbar = M.Xbar := by
  change ReconstructionCoordinates.Xbar M.neg.s M.neg.decoded.P (Fintype.card F)
    = ReconstructionCoordinates.Xbar M.s M.decoded.P (Fintype.card F)
  rw [M.neg_decoded_P, MapData.neg_s]

lemma Xbar_eq_neg_one [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]
    (t : { n : F // n = 1 ∨ n = -1}) :
    (D.decoded t.val).Xbar = -1 := by
  have hη : η (D.decoded t.val).P = 0 := η_eq_zero D t
  have hcard := card_mod_four (F := F)
  unfold PointData.Xbar ReconstructionCoordinates.Xbar
  rw [hη]
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

/-- PointData wrapper for z. -/
def _root_.Elligator.PointData.z : F := ReconstructionCoordinates.z Q.s Q.P (Fintype.card F)

/-- MapData wrapper for z. -/
def _root_.Elligator.MapData.z
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] : F :=
    M.decoded.z

lemma z_eq_zero [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]
    (t : { n : F // n = 1 ∨ n = -1}) :
    (D.decoded t.val).z = 0 := by
  have hXbar :
      ReconstructionCoordinates.Xbar (D.decoded t.val).s (D.decoded t.val).P (Fintype.card F)
        = -1 :=
    Xbar_eq_neg_one D t
  unfold PointData.z ReconstructionCoordinates.z
  rw [hXbar]
  simp

omit [DecidableEq F] in
lemma Xbar_pow_two_add_one_div_c_pow_two_ne_zero
    [IsNonzeroParam Q.s] [IsCardThreeModFour F] :
    Q.Xbar ^ 2 + 1 / Q.c ^ 2 ≠ 0 := by
  intro h_sum_eq_zero
  have hc_ne_zero : Q.c ≠ 0 := c_ne_zero Q.toParamData
  have h_sq : (Q.Xbar * Q.c) ^ 2 = -1 := by
    field_simp at h_sum_eq_zero
    linear_combination h_sum_eq_zero
  exact false_of_isSquare_neg_one card_mod_four ⟨Q.Xbar * Q.c, by rw [← h_sq]; ring⟩

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

/-- PointData wrapper for ubar. -/
def _root_.Elligator.PointData.ubar : F := ReconstructionCoordinates.ubar Q.s Q.P (Fintype.card F)

/-- MapData wrapper for ubar. -/
def _root_.Elligator.MapData.ubar
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] : F :=
    M.decoded.ubar

lemma ubar_eq_zero [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]
    (t : { n : F // n = 1 ∨ n = -1}) :
    (D.decoded t.val).ubar = 0 := by
  have hz : ReconstructionCoordinates.z (D.decoded t.val).s (D.decoded t.val).P (Fintype.card F)
      = 0 :=
    z_eq_zero D t
  unfold PointData.ubar ReconstructionCoordinates.ubar
  rw [hz, zero_mul]

lemma χ_IsSquare_h1 [IsNonzeroParam M.s] [IsCardThreeModFour F] :
    IsSquare ((χ M.v * M.v) ^ ((Fintype.card F + 1) / 4)) := by
  obtain ⟨w, hw⟩ := χ_a_mul_a_IsSquare (v_ne_zero M) card_mod_four
  rw [hw, ← pow_two, ← pow_mul, mul_comm, pow_mul]
  exact IsSquare.sq _

/-- `X` and `u` differ by the sign `χ(v)`, hence have the same square. -/
lemma X_sq_eq_u_sq [IsNonzeroParam M.s] [IsCardThreeModFour F] : M.X ^ 2 = M.u ^ 2 := by
  change (χ M.v * M.u) ^ 2 = M.u ^ 2
  rw [mul_pow, pow_two, χ_mul_self_eq_one (v_ne_zero M), one_mul]

lemma χ_Y_eq_χ_v_mul_χ_sum [IsNonzeroParam M.s] [IsCardThreeModFour F] :
    χ M.Y = χ M.v * χ (M.u ^ 2 + 1 / M.c ^ 2) := by
  change χ ((χ M.v * M.v) ^ ((Fintype.card F + 1) / 4) * χ M.v * χ (M.u ^ 2 + 1 / M.c ^ 2)) = _
  rw [χ_mul, χ_mul,
    χ_a_eq_one (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero M) (χ_IsSquare_h1 M),
    one_mul, χ_χ_eq_χ card_mod_four, χ_χ_eq_χ card_mod_four]

lemma z_eq_χ_v [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F]
    (hXXbar : M.Xbar = M.X) :
    M.z = χ M.v := by
  have hY_ne_zero : M.Y ≠ 0 := Y_ne_zero M
  have hx_eq : M.x * M.Y = (M.c - 1) * M.s * M.X * (1 + M.X) := by
    change (M.c - 1) * M.s * M.X * (1 + M.X) / M.Y * M.Y = _
    rw [div_mul_cancel₀ _ hY_ne_zero]
  have hz : M.z = χ ((M.c - 1) * M.s * M.Xbar * (1 + M.Xbar) * M.decoded.P.1
      * (M.Xbar ^ 2 + 1 / M.c ^ 2)) := rfl
  rw [hz, hXXbar, M.decoded_P_eq_point_P]
  change χ ((M.c - 1) * M.s * M.X * (1 + M.X) * M.x * (M.X ^ 2 + 1 / M.c ^ 2)) = χ M.v
  rw [← hx_eq]
  have hrearrange : M.x * M.Y * M.x * (M.X ^ 2 + 1 / M.c ^ 2)
      = M.x ^ 2 * (M.Y * (M.X ^ 2 + 1 / M.c ^ 2)) := by ring
  rw [hrearrange, χ_mul, χ_sq (x_ne_zero M), one_mul, χ_mul, χ_Y_eq_χ_v_mul_χ_sum M,
    X_sq_eq_u_sq M, mul_assoc, χ_mul_self_eq_one (v_factored_third_factor_ne_zero M), mul_one]

lemma ubar_eq_u [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F]
    (hXXbar : M.Xbar = M.X) :
    M.ubar = M.u := by
  have hubar : M.ubar = M.z * M.Xbar := rfl
  rw [hubar, hXXbar, z_eq_χ_v M hXXbar]
  change χ M.v * (χ M.v * M.u) = M.u
  rw [← mul_assoc, χ_mul_self_eq_one (v_ne_zero M), one_mul]

/-- `ū` does not change when the input `t` is replaced by `-t`. -/
lemma _root_.Elligator.MapData.neg_ubar
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.neg.ubar = M.ubar := by
  change ReconstructionCoordinates.ubar M.neg.s M.neg.decoded.P (Fintype.card F)
    = ReconstructionCoordinates.ubar M.s M.decoded.P (Fintype.card F)
  rw [M.neg_decoded_P, MapData.neg_s]

lemma ubar_eq_u' [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F]
    (hXXbar : M.Xbar = M.neg.X) :
    M.ubar = M.neg.u := by
  rw [← M.neg_ubar]
  exact ubar_eq_u M.neg (by rw [M.neg_Xbar]; exact hXXbar)

lemma one_add_ubar_ne_zero_base_case [IsNonzeroParam D.s] [IsRegularParam D.s]
    [IsCardThreeModFour F] (t : {n : F // n = 1 ∨ n = -1}) :
    1 + (D.decoded t.val).ubar ≠ 0 := by
  rw [ubar_eq_zero D t, add_zero]
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

/-- PointData wrapper for tbar. -/
def _root_.Elligator.PointData.tbar : F := ReconstructionCoordinates.tbar Q.s Q.P (Fintype.card F)

/-- MapData wrapper for tbar. -/
def _root_.Elligator.MapData.tbar
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] : F :=
    M.decoded.tbar

lemma tbar_eq_one [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]
    (t : { n : F // n = 1 ∨ n = -1}) :
    (D.decoded t.val).tbar = 1 := by
  have hubar :
      ReconstructionCoordinates.ubar (D.decoded t.val).s (D.decoded t.val).P (Fintype.card F)
        = 0 :=
    ubar_eq_zero D t
  unfold PointData.tbar ReconstructionCoordinates.tbar
  rw [hubar]
  simp

lemma tbar_eq_t [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F]
    (hXXbar : M.Xbar = M.X) :
    M.tbar = M.t := by
  have htbar : M.tbar = (1 - M.ubar) / (1 + M.ubar) := rfl
  have hu : M.u = (1 - M.t) / (1 + M.t) := rfl
  have h_one_add_t_ne_zero : (1 : F) + M.t ≠ 0 := one_add_t_ne_zero M.tSub
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  rw [htbar, ubar_eq_u M hXXbar, hu]
  field_simp
  have hnum : 1 + M.t - (1 - M.t) = 2 * M.t := by ring
  have hden : 1 + M.t + (1 - M.t) = 2 := by ring
  rw [hnum, hden, mul_comm, mul_div_assoc, div_self h_two_ne_zero, mul_one]

/-- `t̄` does not change when the input `t` is replaced by `-t`. -/
lemma _root_.Elligator.MapData.neg_tbar
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.neg.tbar = M.tbar := by
  change ReconstructionCoordinates.tbar M.neg.s M.neg.decoded.P (Fintype.card F)
    = ReconstructionCoordinates.tbar M.s M.decoded.P (Fintype.card F)
  rw [M.neg_decoded_P, MapData.neg_s]

lemma tbar_eq_t' [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F]
    (hXXbar : M.Xbar = M.neg.X) :
    M.tbar = -M.t := by
  rw [← M.neg_tbar, ← MapData.neg_t]
  exact tbar_eq_t M.neg (by rw [M.neg_Xbar]; exact hXXbar)

end tbar

end Elligator.Elligator1.ReconstructionCoordinates
