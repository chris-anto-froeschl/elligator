/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.XbarConsequences
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Reverse Proof Vehicle

The primed quantities `Y'`, `z'`, `u'`, `v'`, `t'`, `x'`, `y'` reconstructed from a point of
`E(F)` satisfying the image conditions of Theorem 3. They mirror the forward quantities of
Theorem 1 and are shown to coincide with them for the input `t'`, which is the heart of the
reverse direction of Theorem 3.

## Main Results

* `Y'`, `z'`, `u'`, `v'`, `t'`, `x'`, `y'`: the reconstructed quantities.
* `u'_eq_u`, `v'_eq_v`, `X'_eq_X`, `Y'_eq_Y`, `x'_eq_x`, `y'_eq_y`: they agree with the
  forward quantities computed from the input `t'`.
* `x_y_of_P_eq_x_y`: the forward map applied to `t'` returns the original point.

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.ReverseProofVehicle

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates
open Elligator.Elligator1.ReconstructionCoordinates
open Elligator.Elligator1.PhiOverFCharacterization
open Elligator.Elligator1.XbarConsequences

variable (Q : PointData F)

section Y'

/-- `Y'` is the `Y` equivalent used in the proof reverse argumentation of Theorem 3 part C.

This is just `def x` with the denominator `Y` replaced by the `x`-coordinate of the point. -/
def Y' : F := (Q.c - 1) * Q.s * Q.Xbar * (1 + Q.Xbar) / Q.x

omit [DecidableEq F] in
lemma c_sub_one_pow_two_mul_s_pow_two [IsNonzeroParam Q.s] [IsCardThreeModFour F] :
    (Q.c - 1) ^ 2 * Q.s ^ 2 = 2 * (Q.r - 2) := by
  have hs_ne_zero : Q.s ≠ 0 := s_ne_zero
  have hc_ne_zero : Q.c ≠ 0 := c_ne_zero Q.toParamData
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  have hc : Q.c = 2 / Q.s ^ 2 := rfl
  have hr : Q.r = Q.c + 1 / Q.c := rfl
  rw [hr, hc]
  field_simp
  ring

lemma one_add_Xbar_ne_zero [IsNonzeroParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hy_ne_one : Q.y ≠ 1) :
    1 + Q.Xbar ≠ 0 :=
  fun h => Xbar_ne_neg_one Q hP hy_ne_one (by linear_combination h)

lemma Y'_pow_two_eq_of_Xbar_ne_one
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → Y' Q ^ 2 = Q.Xbar ^ 5 + (Q.r ^ 2 - 2) * Q.Xbar ^ 3 + Q.Xbar := by
  intro hX1
  have hx2 := x_pow_two_of_Xbar_ne_one_eq2_of_Xbar_ne_one Q hcurve hP hX1
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  have hA : 2 * (Q.r - 2) * Q.Xbar ^ 2 * (1 + Q.Xbar) ^ 2 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero h_two_ne_zero (r_sub_two_ne_zero Q.toParamData))
        (pow_ne_zero 2 (Xbar_ne_zero Q hP)))
      (pow_ne_zero 2 (one_add_Xbar_ne_zero Q hP hy_ne_one))
  have hY2 : Y' Q ^ 2 = (2 * (Q.r - 2) * Q.Xbar ^ 2 * (1 + Q.Xbar) ^ 2) / Q.x ^ 2 := by
    change ((Q.c - 1) * Q.s * Q.Xbar * (1 + Q.Xbar) / Q.x) ^ 2 = _
    rw [div_pow]
    congr 1
    linear_combination (Q.Xbar ^ 2 * (1 + Q.Xbar) ^ 2) * c_sub_one_pow_two_mul_s_pow_two Q
  rw [hY2, hx2, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hA, mul_one]

lemma Y'_ne_zero [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Y' Q ≠ 0 := by
  apply div_ne_zero _ hx_ne_zero
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (c_sub_one_ne_zero Q.toParamData) s_ne_zero) (Xbar_ne_zero Q hP))
    (one_add_Xbar_ne_zero Q hP hy_ne_one)

end Y'

section z'

/-- `z'` is the `z` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def z' : F := χ (Y' Q * (Q.Xbar ^ 2 + 1 / Q.c ^ 2))

lemma z'_argument_ne_zero [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Y' Q * (Q.Xbar ^ 2 + 1 / Q.c ^ 2) ≠ 0 :=
  mul_ne_zero (Y'_ne_zero Q hP hx_ne_zero hy_ne_one)
    (Xbar_pow_two_add_one_div_c_pow_two_ne_zero Q)

lemma z'_ne_zero [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    z' Q ≠ 0 :=
  χ_a_ne_zero (z'_argument_ne_zero Q hP hx_ne_zero hy_ne_one)

lemma z'_eq_one_or_z'_eq_neg_one [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    z' Q = 1 ∨ z' Q = -1 := by
  have hne := z'_ne_zero Q hP hx_ne_zero hy_ne_one
  rcases χ_values (a := Y' Q * (Q.Xbar ^ 2 + 1 / Q.c ^ 2)) with h | h | h
  · exact absurd h hne
  · exact Or.inr h
  · exact Or.inl h

end z'

section u'

/-- `u'` is the `u` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def u' : F := z' Q * Q.Xbar

lemma u'_pow_two_eq_X_pow_two [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    u' Q ^ 2 = Q.Xbar ^ 2 := by
  change (z' Q * Q.Xbar) ^ 2 = _
  rcases z'_eq_one_or_z'_eq_neg_one Q hP hx_ne_zero hy_ne_one with h | h <;> rw [h] <;> ring

lemma u'_eq_Xbar_or_u'_eq_neg_Xbar
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    u' Q = Q.Xbar ∨ u' Q = -Q.Xbar := by
  rcases z'_eq_one_or_z'_eq_neg_one Q hP hx_ne_zero hy_ne_one with h | h
  · left
    change z' Q * Q.Xbar = Q.Xbar
    rw [h, one_mul]
  · right
    change z' Q * Q.Xbar = -Q.Xbar
    rw [h]
    ring

lemma u'_ne_neg_one [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → u' Q ≠ -1 := by
  intro hX1 hcontra
  rcases u'_eq_Xbar_or_u'_eq_neg_Xbar Q hP hx_ne_zero hy_ne_one with h | h
  · exact Xbar_ne_neg_one Q hP hy_ne_one (by rw [← h, hcontra])
  · exact hX1 (by linear_combination h - hcontra)

lemma one_add_u'_ne_zero [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → 1 + u' Q ≠ 0 := by
  intro hX1 hcontra
  exact u'_ne_neg_one Q hP hx_ne_zero hy_ne_one hX1 (by linear_combination hcontra)

lemma u'_ne_zero [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    u' Q ≠ 0 :=
  mul_ne_zero (z'_ne_zero Q hP hx_ne_zero hy_ne_one) (Xbar_ne_zero Q hP)

end u'

section v'

/-- `v'` is the `v` equivalent used in the proof reverse argumentation of Theorem 3 part C.

Note: this is just the definition of `v` as in Theorem 1. -/
def v' : F := u' Q ^ 5 + (Q.r ^ 2 - 2) * u' Q ^ 3 + u' Q

lemma z'_pow_three_eq_z' : z' Q ^ 3 = z' Q :=
  χ_of_a_pow_n_eq_χ_a (Y' Q * (Q.Xbar ^ 2 + 1 / Q.c ^ 2)) ⟨3, by decide⟩

lemma z'_pow_five_eq_z' : z' Q ^ 5 = z' Q :=
  χ_of_a_pow_n_eq_χ_a (Y' Q * (Q.Xbar ^ 2 + 1 / Q.c ^ 2)) ⟨5, by decide⟩

lemma v'_eq_z'_mul_Y'_pow_two [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → v' Q = z' Q * Y' Q ^ 2 := by
  intro hX1
  have hY2 := Y'_pow_two_eq_of_Xbar_ne_one Q hcurve hP hy_ne_one hX1
  have hv : v' Q = (z' Q * Q.Xbar) ^ 5 + (Q.r ^ 2 - 2) * (z' Q * Q.Xbar) ^ 3
      + (z' Q * Q.Xbar) := rfl
  rw [hv, hY2, mul_pow, mul_pow, z'_pow_three_eq_z' Q, z'_pow_five_eq_z' Q]
  ring

lemma v'_ne_zero [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → v' Q ≠ 0 := by
  intro hX1
  rw [v'_eq_z'_mul_Y'_pow_two Q hcurve hP hy_ne_one hX1]
  exact mul_ne_zero (z'_ne_zero Q hP hx_ne_zero hy_ne_one)
    (pow_ne_zero 2 (Y'_ne_zero Q hP hx_ne_zero hy_ne_one))

end v'

lemma χ_of_v'_eq_χ_of_z' [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → χ (v' Q) = χ (z' Q) := by
  intro hX1
  rw [v'_eq_z'_mul_Y'_pow_two Q hcurve hP hy_ne_one hX1,
    χ_of_a_eq_χ_a_mul_b_pow_two (Y'_ne_zero Q hP hx_ne_zero hy_ne_one)]

lemma χ_of_z'_eq_z' [IsCardThreeModFour F] : χ (z' Q) = z' Q := by
  change χ (χ (Y' Q * (Q.Xbar ^ 2 + 1 / Q.c ^ 2))) = χ (Y' Q * (Q.Xbar ^ 2 + 1 / Q.c ^ 2))
  exact χ_χ_eq_χ card_mod_four

lemma χ_of_v'_eq_z' [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → χ (v' Q) = z' Q := by
  intro hX1
  rw [χ_of_v'_eq_χ_of_z' Q hcurve hP hx_ne_zero hy_ne_one hX1, χ_of_z'_eq_z' Q]

lemma X'_eq_χ_of_v'_mul_u' [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → Q.Xbar = χ (v' Q) * u' Q := by
  intro hX1
  rw [χ_of_v'_eq_z' Q hcurve hP hx_ne_zero hy_ne_one hX1]
  change Q.Xbar = z' Q * (z' Q * Q.Xbar)
  rcases z'_eq_one_or_z'_eq_neg_one Q hP hx_ne_zero hy_ne_one with h | h <;> rw [h] <;> ring

lemma Y'_pow_two_eq_χ_of_v'_mul_v'
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → Y' Q ^ 2 = χ (v' Q) * v' Q := by
  intro hX1
  rw [χ_of_v'_eq_z' Q hcurve hP hx_ne_zero hy_ne_one hX1,
    v'_eq_z'_mul_Y'_pow_two Q hcurve hP hy_ne_one hX1]
  rcases z'_eq_one_or_z'_eq_neg_one Q hP hx_ne_zero hy_ne_one with h | h <;> rw [h] <;> ring

lemma χ_of_v'_eq_z'_unfold_of_X'_ne_one
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → χ (v' Q) = χ (Y' Q * (Q.Xbar ^ 2 + 1 / Q.c ^ 2)) := by
  intro hX1
  rw [χ_of_v'_eq_z' Q hcurve hP hx_ne_zero hy_ne_one hX1]
  rfl

lemma χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_div_c_pow_two
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → χ (v' Q) = χ (Y' Q * (u' Q ^ 2 + 1 / Q.c ^ 2)) := by
  intro hX1
  rw [u'_pow_two_eq_X_pow_two Q hP hx_ne_zero hy_ne_one]
  exact χ_of_v'_eq_z'_unfold_of_X'_ne_one Q hcurve hP hx_ne_zero hy_ne_one hX1

lemma u'_pow_two_add_one_div_c_pow_two_ne_zero [IsNonzeroParam Q.s] [IsCardThreeModFour F] :
    u' Q ^ 2 + 1 / Q.c ^ 2 ≠ 0 := by
  intro h
  have hc_ne_zero : Q.c ≠ 0 := c_ne_zero Q.toParamData
  have hsq : (u' Q * Q.c) ^ 2 = -1 := by
    field_simp at h
    linear_combination h
  exact false_of_isSquare_neg_one card_mod_four ⟨u' Q * Q.c, by rw [← hsq]; ring⟩

lemma Y'_observation1 [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → χ (Y' Q) = χ (v' Q) * χ (u' Q ^ 2 + 1 / Q.c ^ 2) := by
  intro hX1
  rw [χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_div_c_pow_two Q hcurve hP hx_ne_zero hy_ne_one hX1,
    χ_mul, mul_assoc, χ_mul_self_eq_one (u'_pow_two_add_one_div_c_pow_two_ne_zero Q), mul_one]

lemma Y'_observation2 [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → Y' Q = (χ (v' Q) * v' Q) ^ ((Fintype.card F + 1) / 4) * χ (v' Q)
      * χ (u' Q ^ 2 + 1 / Q.c ^ 2) := by
  intro hX1
  have hY_ne_zero := Y'_ne_zero Q hP hx_ne_zero hy_ne_one
  have hY2 := Y'_pow_two_eq_χ_of_v'_mul_v' Q hcurve hP hx_ne_zero hy_ne_one hX1
  have hobs1 := Y'_observation1 Q hcurve hP hx_ne_zero hy_ne_one hX1
  have hexp : 2 * ((Fintype.card F + 1) / 4) = (Fintype.card F + 1) / 2 := by
    have := card_mod_four (F := F)
    omega
  rw [← hY2, ← pow_mul, hexp, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a card_mod_four]
  rw [mul_assoc, ← hobs1]
  have hregroup : χ (Y' Q) * Y' Q * χ (Y' Q) = Y' Q * (χ (Y' Q) * χ (Y' Q)) := by ring
  rw [hregroup, χ_mul_self_eq_one hY_ne_zero, mul_one]

section t'

/-- `t'` is the `t` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def t' : F := (1 - u' Q) / (1 + u' Q)

lemma t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → t' Q ≠ 1 ∧ t' Q ≠ -1 := by
  intro hX1
  have h1u : 1 + u' Q ≠ 0 := one_add_u'_ne_zero Q hP hx_ne_zero hy_ne_one hX1
  have hu0 : u' Q ≠ 0 := u'_ne_zero Q hP hx_ne_zero hy_ne_one
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  constructor
  · intro h
    have h' : 1 - u' Q = 1 * (1 + u' Q) := (div_eq_iff h1u).mp h
    exact hu0 (mul_left_cancel₀ h_two_ne_zero (by linear_combination -h' : (2 : F) * u' Q = 2 * 0))
  · intro h
    have h' : 1 - u' Q = -1 * (1 + u' Q) := (div_eq_iff h1u).mp h
    exact h_two_ne_zero (by linear_combination h')

lemma one_add_t'_ne_zero [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → t' Q + 1 ≠ 0 := by
  intro hX1 h
  exact (t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one Q hP hx_ne_zero hy_ne_one hX1).2
    (by linear_combination h)

/-- The `MapData` of Theorem 1 attached to the reconstructed input `t'`. -/
@[reducible]
def mapDataOfPoint (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) : MapData F :=
  Q.toParamData.withInput (t' Q) ht.1 ht.2

lemma u'_eq_one_sub_t'_div_one_add_t'
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → u' Q = (1 - t' Q) / (1 + t' Q) := by
  intro hX1
  have h1u : 1 + u' Q ≠ 0 := one_add_u'_ne_zero Q hP hx_ne_zero hy_ne_one hX1
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  have ht' : t' Q = (1 - u' Q) / (1 + u' Q) := rfl
  have hd : (1 : F) + (1 - u' Q) / (1 + u' Q) = 2 / (1 + u' Q) := by
    field_simp
    ring
  have hdne : (1 : F) + (1 - u' Q) / (1 + u' Q) ≠ 0 := by
    rw [hd]
    exact div_ne_zero h_two_ne_zero h1u
  rw [ht', eq_div_iff hdne]
  field_simp
  ring

lemma u'_eq_u [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1)
    (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    u' Q = (mapDataOfPoint Q ht).u :=
  u'_eq_one_sub_t'_div_one_add_t' Q hP hx_ne_zero hy_ne_one hX1

lemma v'_eq_v [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1)
    (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    v' Q = (mapDataOfPoint Q ht).v := by
  have hu := u'_eq_u Q hP hx_ne_zero hy_ne_one hX1 ht
  change u' Q ^ 5 + (Q.r ^ 2 - 2) * u' Q ^ 3 + u' Q = _
  rw [hu]
  rfl

lemma X'_eq_X [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    Q.Xbar = (mapDataOfPoint Q ht).X := by
  have hu := u'_eq_u Q hP hx_ne_zero hy_ne_one hX1 ht
  have hv := v'_eq_v Q hP hx_ne_zero hy_ne_one hX1 ht
  change Q.Xbar = χ (mapDataOfPoint Q ht).v * (mapDataOfPoint Q ht).u
  rw [← hu, ← hv]
  exact X'_eq_χ_of_v'_mul_u' Q hcurve hP hx_ne_zero hy_ne_one hX1

lemma Y'_eq_Y [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    Y' Q = (mapDataOfPoint Q ht).Y := by
  have hu := u'_eq_u Q hP hx_ne_zero hy_ne_one hX1 ht
  have hv := v'_eq_v Q hP hx_ne_zero hy_ne_one hX1 ht
  change _ = (χ (mapDataOfPoint Q ht).v * (mapDataOfPoint Q ht).v) ^ ((Fintype.card F + 1) / 4)
    * χ (mapDataOfPoint Q ht).v * χ ((mapDataOfPoint Q ht).u ^ 2 + 1 / Q.c ^ 2)
  rw [← hu, ← hv]
  exact Y'_observation2 Q hcurve hP hx_ne_zero hy_ne_one hX1

end t'

section x'

/-- `x'` is the `x` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def x' : F := (Q.c - 1) * Q.s * Q.Xbar * (1 + Q.Xbar) / Y' Q

/-- `y'` is the `y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def y' : F := (Q.r * Q.Xbar - (1 + Q.Xbar) ^ 2) / (Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2)

lemma x'_eq_x [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    x' Q = (mapDataOfPoint Q ht).x := by
  have hX := X'_eq_X Q hcurve hP hx_ne_zero hy_ne_one hX1 ht
  have hY := Y'_eq_Y Q hcurve hP hx_ne_zero hy_ne_one hX1 ht
  change (Q.c - 1) * Q.s * Q.Xbar * (1 + Q.Xbar) / Y' Q = _
  rw [hX, hY]
  rfl

lemma y'_eq_y [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    y' Q = (mapDataOfPoint Q ht).y := by
  have hX := X'_eq_X Q hcurve hP hx_ne_zero hy_ne_one hX1 ht
  change (Q.r * Q.Xbar - (1 + Q.Xbar) ^ 2) / (Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2) = _
  rw [hX]
  rfl

theorem x'_and_y'_fulfill_curve_equation
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    Q.curve.Equation (x' Q) (y' Q) := by
  rw [x'_eq_x Q hcurve hP hx_ne_zero hy_ne_one hX1 ht,
    y'_eq_y Q hcurve hP hx_ne_zero hy_ne_one hX1 ht]
  exact map_fulfills_curve_equation (mapDataOfPoint Q ht)

lemma y_eq_y_of_P [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    (mapDataOfPoint Q ht).y = Q.y := by
  rw [← y'_eq_y Q hcurve hP hx_ne_zero hy_ne_one hX1 ht]
  exact (y_with_Xbar Q hP).symm

lemma x_eq_x_of_P [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    (mapDataOfPoint Q ht).x = Q.x := by
  have hN : (Q.c - 1) * Q.s * Q.Xbar * (1 + Q.Xbar) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (c_sub_one_ne_zero Q.toParamData) s_ne_zero) (Xbar_ne_zero Q hP))
      (one_add_Xbar_ne_zero Q hP hy_ne_one)
  have hx' : x' Q = Q.x := by
    change (Q.c - 1) * Q.s * Q.Xbar * (1 + Q.Xbar) / Y' Q = Q.x
    rw [show Y' Q = (Q.c - 1) * Q.s * Q.Xbar * (1 + Q.Xbar) / Q.x from rfl,
      div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hN, mul_one]
  rw [← x'_eq_x Q hcurve hP hx_ne_zero hy_ne_one hX1 ht, hx']

lemma x_y_of_P_eq_x_y [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0)
    (hy_ne_one : Q.y ≠ 1) (hX1 : Q.Xbar ≠ 1) (ht : t' Q ≠ 1 ∧ t' Q ≠ -1) :
    ((mapDataOfPoint Q ht).x, (mapDataOfPoint Q ht).y) = Q.P := by
  rw [x_eq_x_of_P Q hcurve hP hx_ne_zero hy_ne_one hX1 ht,
    y_eq_y_of_P Q hcurve hP hx_ne_zero hy_ne_one hX1 ht]
  rfl

end x'

end Elligator.Elligator1.ReverseProofVehicle
