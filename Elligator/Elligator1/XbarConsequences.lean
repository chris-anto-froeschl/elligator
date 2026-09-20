/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Elligator.Elligator1.ReconstructionCoordinates
public import Elligator.Elligator1.PhiOverFCharacterization
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Xbar Consequences

Consequences of the image conditions of Theorem 3 for the reconstructed coordinate `X̄`: the
quadratic equation it satisfies, its nonvanishing, and the resulting expression of `y` and `x`
in terms of `X̄`.

## Main Results

* `Xbar_quadratic_eq_of_η`: `X̄ ² + 2(1 + ηr)X̄ + 1 = 0`.
* `Xbar_eq_X_or_eq_X'`: for a point of the image, `X̄` is `X(t)` or `X(-t)`.
* `y_with_Xbar`, `x_pow_two_of_Xbar_ne_one_eq2_of_Xbar_ne_one`: the coordinates in terms of `X̄`.
* `tbar_in_t_or_neg_t`: the reconstructed preimage is `t` or `-t`.

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.XbarConsequences

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates
open Elligator.Elligator1.ReconstructionCoordinates
open Elligator.Elligator1.PhiOverFCharacterization

variable (D : ParamData F)
variable (M : MapData F)
variable (Q : PointData F)

section point

lemma Xbar_sqrt_property [IsCardThreeModFour F] (hP : Q.ϕOverFProps) :
    (1 + Q.η * Q.r + Q.Xbar) ^ 2 = (1 + Q.η * Q.r) ^ 2 - 1 := by
  have hsq : IsSquare ((1 + Q.η * Q.r) ^ 2 - 1) := hP.2.1
  have hXbar : Q.Xbar
      = -(1 + Q.η * Q.r) + ((1 + Q.η * Q.r) ^ 2 - 1) ^ ((Fintype.card F + 1) / 4) := rfl
  rw [hXbar]
  have hcollapse : 1 + Q.η * Q.r + (-(1 + Q.η * Q.r)
      + ((1 + Q.η * Q.r) ^ 2 - 1) ^ ((Fintype.card F + 1) / 4))
      = ((1 + Q.η * Q.r) ^ 2 - 1) ^ ((Fintype.card F + 1) / 4) := by ring
  have hexp : (Fintype.card F + 1) / 4 * 2 = (Fintype.card F + 1) / 2 := by
    have := card_mod_four (F := F)
    omega
  rw [hcollapse, ← pow_mul, hexp]
  exact a_pow_q_add_one_div_two_eq_a hsq card_mod_four

lemma Xbar_quadratic_eq_of_η [IsCardThreeModFour F] (hP : Q.ϕOverFProps) :
    Q.Xbar ^ 2 + 2 * (1 + Q.η * Q.r) * Q.Xbar + 1 = 0 := by
  linear_combination Xbar_sqrt_property Q hP

lemma Xbar_ne_zero [IsCardThreeModFour F] (hP : Q.ϕOverFProps) : Q.Xbar ≠ 0 := by
  intro h
  have hquad := Xbar_quadratic_eq_of_η Q hP
  rw [h] at hquad
  simp at hquad

lemma y_divisor_ne_zero_with_Xbar_for_X [IsNonzeroParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) :
    Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2 ≠ 0 := by
  intro h1
  have hquad := Xbar_quadratic_eq_of_η Q hP
  have hr_ne_zero : Q.r ≠ 0 := r_ne_zero Q.toParamData
  have hXbar_ne_zero : Q.Xbar ≠ 0 := Xbar_ne_zero Q hP
  have hy_add_one_ne_zero : Q.y + 1 ≠ 0 := hP.1
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  have h2 : Q.r * Q.Xbar * (1 - 2 * Q.η) = 0 := by linear_combination h1 - hquad
  have h3 : 2 * Q.η = 1 := by
    rcases mul_eq_zero.mp h2 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hr_ne_zero
      · exact absurd h' hXbar_ne_zero
    · linear_combination -h
  rw [Q.η_eq_y] at h3
  have hdenom : 2 * (Q.y + 1) ≠ 0 := mul_ne_zero h_two_ne_zero hy_add_one_ne_zero
  have h4 : 2 * ((Q.y - 1) / (2 * (Q.y + 1))) * (2 * (Q.y + 1)) = 2 * (Q.y + 1) := by
    rw [h3, one_mul]
  rw [mul_assoc, div_mul_cancel₀ _ hdenom] at h4
  exact four_ne_zero (F := F) card_mod_four (by linear_combination -h4)

lemma Xbar_ne_neg_one [IsNonzeroParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (y_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ -1 := by
  intro h1
  have hquad := Xbar_quadratic_eq_of_η Q hP
  rw [h1] at hquad
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  have hηr : Q.η * Q.r = 0 :=
    mul_left_cancel₀ h_two_ne_zero (by linear_combination -hquad : (2 : F) * (Q.η * Q.r) = 2 * 0)
  rcases mul_eq_zero.mp hηr with h | h
  · have hy_add_one_ne_zero : Q.y + 1 ≠ 0 := hP.1
    have hdenom : 2 * (Q.y + 1) ≠ 0 :=
      mul_ne_zero (two_ne_zero card_mod_four) hy_add_one_ne_zero
    have h0 : (Q.y - 1) / (2 * (Q.y + 1)) = 0 := by rw [← Q.η_eq_y, h]
    rcases div_eq_zero_iff.mp h0 with h' | h'
    · exact y_ne_one (by linear_combination h')
    · exact hdenom h'
  · exact r_ne_zero Q.toParamData h

lemma Xbar_add_one_ne_zero [IsNonzeroParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (y_ne_one : Q.y ≠ 1) :
    Q.Xbar + 1 ≠ 0 :=
  fun h => Xbar_ne_neg_one Q hP y_ne_one (by linear_combination h)

lemma y_with_Xbar [IsNonzeroParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) :
    Q.y = (Q.r * Q.Xbar - (1 + Q.Xbar) ^ 2) / (Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2) := by
  have hquad := Xbar_quadratic_eq_of_η Q hP
  have hy_add_one_ne_zero : Q.y + 1 ≠ 0 := hP.1
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  have hden : Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2 ≠ 0 := y_divisor_ne_zero_with_Xbar_for_X Q hP
  have hdenom : 2 * (Q.y + 1) ≠ 0 := mul_ne_zero h_two_ne_zero hy_add_one_ne_zero
  have hηeq : 2 * Q.η * (Q.y + 1) = Q.y - 1 := by
    rw [Q.η_eq_y]
    linear_combination div_mul_cancel₀ (Q.y - 1) hdenom
  have h2ηr : 2 * Q.η * (Q.r * Q.Xbar) + (1 + Q.Xbar) ^ 2 = 0 := by linear_combination hquad
  rw [eq_div_iff hden]
  linear_combination (Q.y + 1) * h2ηr - (Q.r * Q.Xbar) * hηeq

lemma y_with_Xbar_of_Xbar_eq_one [IsNonzeroParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) :
    Q.Xbar = 1 → Q.y = (Q.r - 4) / (Q.r + 4) := by
  intro h
  rw [y_with_Xbar Q hP, h]
  norm_num

lemma η_mul_r_eq_neg_two_of_Xbar_eq_one [IsCardThreeModFour F] (hP : Q.ϕOverFProps) :
    Q.Xbar = 1 → Q.η * Q.r = -2 := by
  intro h
  have hquad := Xbar_quadratic_eq_of_η Q hP
  rw [h] at hquad
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  exact mul_left_cancel₀ h_two_ne_zero (by linear_combination hquad : (2 : F) * (Q.η * Q.r)
    = 2 * (-2))

lemma Xbar_observation1_of_Xbar_ne_one [IsNonzeroParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) :
    Q.Xbar ≠ 1 →
      (Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2) ^ 2 * (1 - Q.y ^ 2)
        = 4 * Q.r * Q.Xbar * (1 + Q.Xbar) ^ 2 := by
  intro _
  have hden : Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2 ≠ 0 := y_divisor_ne_zero_with_Xbar_for_X Q hP
  rw [y_with_Xbar Q hP]
  field_simp
  ring

lemma Xbar_observation2_of_Xbar_ne_one
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) :
    Q.Xbar ≠ 1 →
      (Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2) ^ 2 * (1 - Q.d * Q.y ^ 2)
        = ((2 * Q.r) / (Q.r - 2)) * (Q.Xbar ^ 4 + (Q.r ^ 2 - 2) * Q.Xbar ^ 2 + 1) := by
  intro _
  have hden : Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2 ≠ 0 := y_divisor_ne_zero_with_Xbar_for_X Q hP
  have hr_sub_two : Q.r - 2 ≠ 0 := r_sub_two_ne_zero Q.toParamData
  have hd : Q.d = -((Q.r + 2) / (Q.r - 2)) := by
    linear_combination -neg_d_eq_r_add_two_div_r_sub_two Q.toParamData
  rw [y_with_Xbar Q hP, hd]
  field_simp
  ring

omit [DecidableEq F] in
lemma one_sub_d_mul_y_pow_two_ne_zero [IsRegularParam Q.s] [IsCardThreeModFour F] :
    1 - Q.d * Q.y ^ 2 ≠ 0 := by
  intro h
  have hd_ne_zero : Q.d ≠ 0 := d_ne_zero Q.toParamData
  apply one_div_d_nonsquare Q.toParamData
  refine ⟨Q.y, ?_⟩
  rw [div_eq_iff hd_ne_zero]
  linear_combination h

omit [DecidableEq F] in
lemma x_pow_two_of_Xbar_ne_one_eq1 [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) :
    Q.x ^ 2 = (1 - Q.y ^ 2) / (1 - Q.d * Q.y ^ 2) := by
  have hcurve' : Q.x ^ 2 + Q.y ^ 2 = 1 + Q.d * Q.x ^ 2 * Q.y ^ 2 :=
    (mem_EOverF_iff Q.toParamData Q.P).mp hcurve
  rw [eq_div_iff (one_sub_d_mul_y_pow_two_ne_zero Q)]
  linear_combination hcurve'

lemma Xbar_poly_ne_zero
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (hX1 : Q.Xbar ≠ 1) :
    Q.Xbar ^ 5 + (Q.r ^ 2 - 2) * Q.Xbar ^ 3 + Q.Xbar ≠ 0 := by
  have hr_sub_two : Q.r - 2 ≠ 0 := r_sub_two_ne_zero Q.toParamData
  have hXbar_ne_zero : Q.Xbar ≠ 0 := Xbar_ne_zero Q hP
  have hden : Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2 ≠ 0 := y_divisor_ne_zero_with_Xbar_for_X Q hP
  have hne : 1 - Q.d * Q.y ^ 2 ≠ 0 := one_sub_d_mul_y_pow_two_ne_zero Q
  have h4' : (Q.r - 2) * ((Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2) ^ 2 * (1 - Q.d * Q.y ^ 2))
      = 2 * Q.r * (Q.Xbar ^ 4 + (Q.r ^ 2 - 2) * Q.Xbar ^ 2 + 1) := by
    rw [Xbar_observation2_of_Xbar_ne_one Q hP hX1]
    field_simp
  have hS : Q.Xbar ^ 4 + (Q.r ^ 2 - 2) * Q.Xbar ^ 2 + 1 ≠ 0 := by
    intro hS0
    rw [hS0, mul_zero] at h4'
    exact (mul_ne_zero hr_sub_two (mul_ne_zero (pow_ne_zero 2 hden) hne)) h4'
  intro hp
  apply hS
  have hfactor : Q.Xbar * (Q.Xbar ^ 4 + (Q.r ^ 2 - 2) * Q.Xbar ^ 2 + 1) = 0 := by
    linear_combination hp
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd h hXbar_ne_zero
  · exact h

lemma x_pow_two_of_Xbar_ne_one_eq2_of_Xbar_ne_one
    [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) :
    Q.Xbar ≠ 1 →
      Q.x ^ 2 = (2 * (Q.r - 2) * Q.Xbar ^ 2 * (1 + Q.Xbar) ^ 2)
        / (Q.Xbar ^ 5 + (Q.r ^ 2 - 2) * Q.Xbar ^ 3 + Q.Xbar) := by
  intro hX1
  have hr_ne_zero : Q.r ≠ 0 := r_ne_zero Q.toParamData
  have hr_sub_two : Q.r - 2 ≠ 0 := r_sub_two_ne_zero Q.toParamData
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  have hden : Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2 ≠ 0 := y_divisor_ne_zero_with_Xbar_for_X Q hP
  have hne : 1 - Q.d * Q.y ^ 2 ≠ 0 := one_sub_d_mul_y_pow_two_ne_zero Q
  have h1 := x_pow_two_of_Xbar_ne_one_eq1 Q hcurve
  have h3 := Xbar_observation1_of_Xbar_ne_one Q hP hX1
  have e1 : Q.x ^ 2 * (1 - Q.d * Q.y ^ 2) = 1 - Q.y ^ 2 := by
    rw [h1, div_mul_cancel₀ _ hne]
  have h4' : (Q.r - 2) * ((Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2) ^ 2 * (1 - Q.d * Q.y ^ 2))
      = 2 * Q.r * (Q.Xbar ^ 4 + (Q.r ^ 2 - 2) * Q.Xbar ^ 2 + 1) := by
    rw [Xbar_observation2_of_Xbar_ne_one Q hP hX1]
    field_simp
  rw [eq_div_iff (Xbar_poly_ne_zero Q hP hX1)]
  refine mul_left_cancel₀ (mul_ne_zero h_two_ne_zero hr_ne_zero) ?_
  linear_combination (-(Q.Xbar * Q.x ^ 2)) * h4'
    + (Q.Xbar * (Q.r - 2) * (Q.r * Q.Xbar + (1 + Q.Xbar) ^ 2) ^ 2) * e1
    + (Q.Xbar * (Q.r - 2)) * h3

lemma Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    [IsNonzeroParam Q.s] [IsCardThreeModFour F]
    (hP : Q.ϕOverFProps) (y_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → Q.Xbar ≠ 1 ∧ Q.Xbar ≠ -1 :=
  fun h => ⟨h, Xbar_ne_neg_one Q hP y_ne_one⟩

end point

section map

variable [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F]

/-- The point decoded from a nonexceptional input satisfies the image conditions. -/
lemma decoded_ϕOverFProps : M.decoded.ϕOverFProps :=
  P_of_ϕ_fulfills_ϕOverFProps M.toParamData M.t

lemma Xbar_eq_X_or_X'_factored : (M.Xbar - M.X) * (M.Xbar - M.neg.X) = 0 := by
  have hquad : M.Xbar ^ 2 + 2 * (1 + M.η * M.r) * M.Xbar + 1 = 0 :=
    Xbar_quadratic_eq_of_η M.decoded (decoded_ϕOverFProps M)
  have hsum : M.X + M.neg.X = -2 * (1 + M.η * M.r) := X_comparison_implication M
  have hprod : M.neg.X * M.X = 1 := X_comparison_implication2 M
  linear_combination hquad - M.Xbar * hsum + hprod

lemma Xbar_eq_X_or_eq_X' : M.Xbar = M.X ∨ M.Xbar = M.neg.X := by
  rcases mul_eq_zero.mp (Xbar_eq_X_or_X'_factored M) with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

lemma ubar_eq_u_or_eq_u' : M.ubar = M.u ∨ M.ubar = M.neg.u := by
  rcases Xbar_eq_X_or_eq_X' M with h | h
  · exact Or.inl (ubar_eq_u M h)
  · exact Or.inr (ubar_eq_u' M h)

/-- The key step: rewriting `1 + ubar(ϕ(t))` in the main case (t ≠ ±1) to show it is ne_zero,
    using `ubar_eq_u_or_eq_u'` which gives `ubar = u(t)` or `ubar = u(-t)`. -/
lemma one_add_ubar_ne_zero_main_case : 1 + M.ubar ≠ 0 := by
  rcases ubar_eq_u_or_eq_u' M with h | h
  · rw [h]
    exact one_add_u_ne_zero M.toInputData
  · rw [h]
    exact one_add_u_ne_zero M.neg.toInputData

end map

section image

variable [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]

lemma one_add_ubar_ne_zero (t : F) : 1 + (D.decoded t).ubar ≠ 0 := by
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · exact one_add_ubar_ne_zero_main_case (D.withInput t h.1 h.2)
  · have h' : t = 1 ∨ t = -1 := by
      rw [ne_eq, ne_eq, ← not_or, not_not] at h
      exact h
    exact one_add_ubar_ne_zero_base_case D ⟨t, h'⟩

@[blueprint "lemma:tbar_in_t_or_neg_t"
  (title := "$\\bar t = \\pm t$")
  (statement := /--
  For $t \in \mathbb{F}_q$, the parameter $\bar t$ reconstructed from $\varphi(t)$ in
  Theorem 3.3 satisfies $\bar t = t$ or $\bar t = -t$. This is the key step showing that
  $\varphi(t)$ has no preimages besides $t$ and $-t$.
  -/)]
lemma tbar_in_t_or_neg_t (t : F) : (D.decoded t).tbar = t ∨ (D.decoded t).tbar = -t := by
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · rcases Xbar_eq_X_or_eq_X' (D.withInput t h.1 h.2) with h1 | h1
    · exact Or.inl (tbar_eq_t (D.withInput t h.1 h.2) h1)
    · exact Or.inr (tbar_eq_t' (D.withInput t h.1 h.2) h1)
  · have h' : t = 1 ∨ t = -1 := by
      rw [ne_eq, ne_eq, ← not_or, not_not] at h
      exact h
    rcases h' with h' | h'
    · exact Or.inl ((tbar_eq_one D ⟨t, Or.inl h'⟩).trans h'.symm)
    · exact Or.inr ((tbar_eq_one D ⟨t, Or.inr h'⟩).trans (by rw [h']; ring))

end image

end Elligator.Elligator1.XbarConsequences
