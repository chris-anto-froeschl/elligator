/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Elligator.Elligator1.ReverseProofVehicle

/-!
# Inverted Map

This file collects the three conclusions of Theorem 3 in the Elligator paper. It describes the
preimage and image of `ϕ`, and verifies the paper's explicit inverse formula on that image.

## Main results

* `ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages`: the preimage of `ϕ t` consists exactly of `t` and `-t`;
  in particular, `ϕ t = ϕ (-t)` and there are no other preimages.
* `props_iff_mem_ϕOverF`: membership in the image `ϕ(F)` is equivalent to the three
  algebraic point conditions stated in part 2 of Theorem 3.
* `Xbar_defined`, `z_defined`, `tbar_defined`: the denominators required by the inverse construction
  are nonzero on `ϕ(F)`.
* `ϕ_of_tbar_eq_x_y`: applying `ϕ` to the reconstructed parameter `tbar` recovers
  the original point.

## References

See [Bernstein2013a] Section 3.3, Theorem 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Primitives.ECC
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates
open Elligator.Elligator1.ReconstructionCoordinates
open Elligator.Elligator1.ReverseProofVehicle
open Elligator.Elligator1.XbarConsequences
open Elligator.Elligator1.PhiOverFCharacterization

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (D : ParamData F)
variable (M : MapData F)
variable (Q : PointData F)

section point_on_curve

omit [Fintype F] [DecidableEq F] in
lemma x_y_eq_zero_sign_one (hcurve : Q.P ∈ Q.EOverF) (hx_eq_zero : Q.x = 0) :
    Q.P = ((0 : F), (1 : F)) ∨ Q.P = ((0 : F), (-1 : F)) := by
  have hcurve' : Q.x ^ 2 + Q.y ^ 2 = 1 + Q.d * Q.x ^ 2 * Q.y ^ 2 :=
    (mem_EOverF_iff Q.toParamData Q.P).mp hcurve
  have hP : Q.P = (Q.x, Q.y) := rfl
  have hy_sq_eq_one : Q.y ^ 2 = 1 := by
    rw [hx_eq_zero] at hcurve'
    linear_combination hcurve'
  have hfactor : (Q.y - 1) * (Q.y + 1) = 0 := by linear_combination hy_sq_eq_one
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    rw [hP, hx_eq_zero, show Q.y = 1 by linear_combination h]
  · right
    rw [hP, hx_eq_zero, show Q.y = -1 by linear_combination h]

lemma x_y_eq_zero_one (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_eq_zero : Q.x = 0) :
    Q.P = ((0 : F), (1 : F)) := by
  have hy_add_one_ne_zero : Q.y + 1 ≠ 0 := hP.1
  rcases x_y_eq_zero_sign_one Q hcurve hx_eq_zero with h | h
  · exact h
  · exfalso
    apply hy_add_one_ne_zero
    have : Q.y = -1 := congrArg Prod.snd h
    rw [this]
    ring

omit [DecidableEq F] in
lemma y_ne_one [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hx_ne_zero : Q.x ≠ 0) :
    Q.y ≠ 1 := by
  intro hy
  have hcurve' : Q.x ^ 2 + Q.y ^ 2 = 1 + Q.d * Q.x ^ 2 * Q.y ^ 2 :=
    (mem_EOverF_iff Q.toParamData Q.P).mp hcurve
  rw [hy] at hcurve'
  have hfactor : Q.x ^ 2 * (1 - Q.d) = 0 := by linear_combination hcurve'
  rcases mul_eq_zero.mp hfactor with h | h
  · exact hx_ne_zero ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h)
  · exact d_ne_one Q.toParamData (by linear_combination -h)

lemma η_ne_zero [IsRegularParam Q.s] [IsCardThreeModFour F]
    (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps) (hx_ne_zero : Q.x ≠ 0) :
    Q.η ≠ 0 := by
  rw [Q.η_eq_y]
  apply div_ne_zero
  · intro h
    exact y_ne_one Q hcurve hx_ne_zero (by linear_combination h)
  · exact mul_ne_zero (two_ne_zero card_mod_four) hP.1

end point_on_curve

section fibers

variable [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]

lemma ϕ_of_t_eq_ϕ_of_neg_t_base_case (t : { t : F // t = 1 ∨ t = -1}) :
    (D.ϕ t.val).val = (D.ϕ (-t.val)).val := by
  have hneg : (-t.val = 1 ∨ -t.val = -1) := by
    rcases t.prop with h | h
    · right; rw [h]
    · left; rw [h]; ring
  have h1 : (D.ϕ t.val).val = ((0 : F), (1 : F)) := ϕ_of_t_eq_zero_one D t
  have h2 : (D.ϕ (-t.val)).val = ((0 : F), (1 : F)) := ϕ_of_t_eq_zero_one D ⟨-t.val, hneg⟩
  rw [h1, h2]

lemma ϕ_of_t_eq_ϕ_of_neg_t_main_case (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    (D.ϕ t.val).val = (D.ϕ (-t.val)).val := by
  have h1 : (D.ϕ t.val).val = (D.withInput t.val t.prop.1 t.prop.2).point.P :=
    (D.withInput t.val t.prop.1 t.prop.2).decoded_P_eq_point_P
  have h2 : (D.ϕ (-t.val)).val = (D.withInput t.val t.prop.1 t.prop.2).neg.point.P :=
    (D.withInput t.val t.prop.1 t.prop.2).neg.decoded_P_eq_point_P
  rw [h1, h2]
  exact P_comparison (D.withInput t.val t.prop.1 t.prop.2)

-- Original: Theorem 3.1 forward statement, Proof A
@[blueprint "lemma:ϕ_of_t_eq_ϕ_of_neg_t"
  (title := "$\\varphi(t) = \\varphi(-t)$")
  (statement := /--
  The forward part of statement 1 of Theorem 3: for every $t \in \mathbb{F}_q$,
  $$
  \varphi(t) = \varphi(-t) .
  $$
  -/)]
lemma ϕ_of_t_eq_ϕ_of_neg_t (t : F) : (D.ϕ t).val = (D.ϕ (-t)).val := by
  by_cases h : t = 1 ∨ t = -1
  · exact ϕ_of_t_eq_ϕ_of_neg_t_base_case D ⟨t, h⟩
  · exact ϕ_of_t_eq_ϕ_of_neg_t_main_case D ⟨t, by
      rw [not_or] at h
      exact h⟩

-- Original: Theorem 3.1 backward statement (Original: Proof B as the very last argument)
@[blueprint "thm:ϕ_preimages"
  (title := "$\\varphi$ has no preimages besides $t$ and $-t$")
  (statement := /--
  The reverse part of statement 1 of Theorem 3: for $t \in \mathbb{F}_q$, no element of
  $\mathbb{F}_q$ other than $t$ and $-t$ is a preimage of $\varphi(t)$ under $\varphi$.
  -/)]
theorem ϕ_preimages (t : F) :
    ¬(∃ (p : { n : F // n ≠ t ∧ n ≠ -t}), (D.ϕ p.val).val = (D.ϕ t).val) := by
  rintro ⟨p, hp⟩
  have htbar_p := tbar_in_t_or_neg_t D p.val
  have htbar_t := tbar_in_t_or_neg_t D t
  have hdec : D.decoded p.val = D.decoded t := by
    unfold ParamData.decoded
    rw [hp]
  rw [hdec] at htbar_p
  have hpt : p.val = t ∨ p.val = -t := by
    rcases htbar_p with h | h <;> rcases htbar_t with h' | h'
    · left; rw [← h, h']
    · right; rw [← h, h']
    · right
      have : -p.val = t := by rw [← h, h']
      linear_combination -this
    · left
      have : -p.val = -t := by rw [← h, h']
      linear_combination -this
  rcases hpt with h | h
  · exact p.prop.1 h
  · exact p.prop.2 h

/-- Equality of images under `ϕ` forces the inputs to agree up to sign.
This is the preimage conclusion of Theorem 3, restated in the form needed for the injectivity
argument in Theorem 4. -/
lemma eq_or_eq_neg_of_ϕ_eq (t t' : F) (h : D.ϕ t = D.ϕ t') : t = t' ∨ t = -t' := by
  by_contra hne
  rw [not_or] at hne
  apply ϕ_preimages D t'
  exact ⟨⟨t, hne.1, hne.2⟩, congrArg Subtype.val h⟩

end fibers

section zero_input

/-- The `MapData` of the input `t = 0`. -/
@[reducible]
def _root_.Elligator.ParamData.zeroInput : MapData F :=
  D.withInput 0 (by norm_num) (by norm_num)

omit [Fintype F] [DecidableEq F] in
lemma u_of_zero : D.zeroInput.u = 1 := by
  change (1 - (0 : F)) / (1 + 0) = 1
  norm_num

omit [Fintype F] [DecidableEq F] in
lemma v_of_zero : D.zeroInput.v = D.r ^ 2 := by
  change D.zeroInput.u ^ 5 + (D.r ^ 2 - 2) * D.zeroInput.u ^ 3 + D.zeroInput.u = _
  rw [u_of_zero]
  ring

lemma X_of_zero [IsNonzeroParam D.s] [IsCardThreeModFour F] : D.zeroInput.X = 1 := by
  change χ D.zeroInput.v * D.zeroInput.u = 1
  rw [u_of_zero, v_of_zero, mul_one, χ_sq (r_ne_zero D)]

lemma y_of_zero [IsNonzeroParam D.s] [IsCardThreeModFour F] :
    D.zeroInput.y = (D.r - 4) / (D.r + 4) := by
  change (D.r * D.zeroInput.X - (1 + D.zeroInput.X) ^ 2)
    / (D.r * D.zeroInput.X + (1 + D.zeroInput.X) ^ 2) = _
  rw [X_of_zero D]
  norm_num

-- Implicated by main case of Theorem 3 Proof part B
lemma ϕ_of_zero [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F] :
    (D.ϕ (0 : F)).val = (2 * (D.c - 1) * D.s * (χ D.c) / D.r, (D.r - 4) / (D.r + 4)) := by
  have hr_ne_zero : D.r ≠ 0 := r_ne_zero D
  have hr_add_four : D.r + 4 ≠ 0 := by
    intro h
    exact four_add_r_ne_zero D (by linear_combination h)
  have hy := y_of_zero D
  have hη : D.zeroInput.η * D.r = -2 := by
    have hηy : D.zeroInput.η = (D.zeroInput.y - 1) / (2 * (D.zeroInput.y + 1)) :=
      D.zeroInput.η_eq_y
    rw [hηy, hy]
    rw [div_mul_eq_mul_div, div_eq_iff]
    · field_simp
      ring
    · intro h
      apply hr_ne_zero
      have h' : (2 : F) * ((D.r - 4) / (D.r + 4) + 1) = 0 := h
      rw [show (D.r - 4) / (D.r + 4) + 1 = (2 * D.r) / (D.r + 4) by field_simp; ring] at h'
      rcases mul_eq_zero.mp h' with h2 | h2
      · exact absurd h2 (two_ne_zero card_mod_four)
      · rcases div_eq_zero_iff.mp h2 with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact absurd h4 (two_ne_zero card_mod_four)
          · exact h4
        · exact absurd h3 hr_add_four
  have hprop3 := P_in_ϕOverF_with_prop3 D (0 : F)
  have hP : (D.ϕ (0 : F)).val = D.zeroInput.point.P := D.zeroInput.decoded_P_eq_point_P
  have hx : (D.ϕ (0 : F)).val.1 = 2 * D.s * (D.c - 1) * (χ D.c) / D.r := by
    apply hprop3
    change ReconstructionCoordinates.η (D.ϕ (0 : F)).val * D.r = -2
    rw [hP, show ReconstructionCoordinates.η D.zeroInput.point.P = D.zeroInput.η from
      point_η_eq_η D.zeroInput]
    exact hη
  have hy' : (D.ϕ (0 : F)).val.2 = (D.r - 4) / (D.r + 4) := by
    rw [hP]
    exact hy
  have hpair : (D.ϕ (0 : F)).val = ((D.ϕ (0 : F)).val.1, (D.ϕ (0 : F)).val.2) := rfl
  rw [hpair, hx, hy']
  congr 1
  ring

end zero_input

section image

variable [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]

-- Used in theorem 3 proof part C
lemma x_y_eq_ϕ_of_zero_of_Xbar_eq_one (hP : Q.ϕOverFProps) :
    Q.Xbar = 1 → (Q.ϕ (0 : F)).val = Q.P := by
  intro hX1
  have h1 := η_mul_r_eq_neg_two_of_Xbar_eq_one Q hP hX1
  have h2 : Q.x = 2 * Q.s * (Q.c - 1) * (χ Q.c) / Q.r := hP.2.2 h1
  have h3 : Q.y = (Q.r - 4) / (Q.r + 4) := y_with_Xbar_of_Xbar_eq_one Q hP hX1
  have hpair : Q.P = (Q.x, Q.y) := rfl
  rw [ϕ_of_zero Q.toParamData, hpair, h2, h3]
  congr 1
  ring

-- Used in theorem 3 proof part C
lemma x_y_eq_ϕ_of_t_of_Xbar_ne_one (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps)
    (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Q.Xbar ≠ 1 → (Q.ϕ (t' Q)).val = Q.P := by
  intro hX1
  have ht := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one Q hP hx_ne_zero hy_ne_one hX1
  have hP' : (Q.ϕ (t' Q)).val = (mapDataOfPoint Q ht).point.P :=
    (mapDataOfPoint Q ht).decoded_P_eq_point_P
  rw [hP']
  exact x_y_of_P_eq_x_y Q hcurve hP hx_ne_zero hy_ne_one hX1 ht

end image

section inverse

variable [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]

lemma ϕ_of_one_eq_zero_one : (D.ϕ (1 : F)).val = ((0 : F), (1 : F)) :=
  ϕ_of_t_eq_zero_one D ⟨1, Or.inl rfl⟩

lemma ϕ_of_neg_one_eq_zero_one : (D.ϕ (-1 : F)).val = ((0 : F), (1 : F)) :=
  ϕ_of_t_eq_zero_one D ⟨-1, Or.inr rfl⟩

lemma ϕ_of_one_in_ϕ_of_F : (D.ϕ (1 : F)).val ∈ D.ϕOverF := ⟨1, rfl⟩

lemma ϕ_of_tbar_eq_x_y_base_case (t : { n : F // n = 1 ∨ n = -1}) :
    (D.ϕ (D.decoded t.val).tbar).val = ((0 : F), (1 : F)) := by
  rw [tbar_eq_one D t]
  exact ϕ_of_one_eq_zero_one D

lemma ϕ_of_tbar_eq_x_y_main_case (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    (D.ϕ (D.decoded t.val).tbar).val = (D.ϕ t.val).val := by
  rcases tbar_in_t_or_neg_t D t.val with h | h
  · rw [h]
  · rw [h, ← ϕ_of_t_eq_ϕ_of_neg_t D t.val]

end inverse

section characterization

variable [IsNonzeroParam Q.s] [IsRegularParam Q.s] [IsCardThreeModFour F]

lemma P_in_ϕOverF_base_case (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps)
    (hx_eq_zero : Q.x = 0) :
    Q.P ∈ Q.ϕOverF := by
  have h1 : Q.P = ((0 : F), (1 : F)) := x_y_eq_zero_one Q hcurve hP hx_eq_zero
  have h2 : (Q.toParamData.ϕ (1 : F)).val = ((0 : F), (1 : F)) :=
    ϕ_of_one_eq_zero_one Q.toParamData
  rw [h1, ← h2]
  exact ϕ_of_one_in_ϕ_of_F Q.toParamData

lemma P_in_ϕOverF_main_case_with_y_eq_one (hcurve : Q.P ∈ Q.EOverF)
    (hx_ne_zero : Q.x ≠ 0) (hy_eq_one : Q.y = 1) :
    Q.P ∈ Q.ϕOverF :=
  absurd hy_eq_one (y_ne_one Q hcurve hx_ne_zero)

lemma P_in_ϕOverF_main_case_with_y_ne_one (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps)
    (hx_ne_zero : Q.x ≠ 0) (hy_ne_one : Q.y ≠ 1) :
    Q.P ∈ Q.ϕOverF := by
  by_cases hX1 : Q.Xbar = 1
  · exact ⟨0, x_y_eq_ϕ_of_zero_of_Xbar_eq_one Q hP hX1⟩
  · exact ⟨t' Q, x_y_eq_ϕ_of_t_of_Xbar_ne_one Q hcurve hP hx_ne_zero hy_ne_one hX1⟩

lemma P_in_ϕOverF_main_case (hcurve : Q.P ∈ Q.EOverF) (hP : Q.ϕOverFProps)
    (hx_ne_zero : Q.x ≠ 0) :
    Q.P ∈ Q.ϕOverF :=
  P_in_ϕOverF_main_case_with_y_ne_one Q hcurve hP hx_ne_zero (y_ne_one Q hcurve hx_ne_zero)

-- Original: Theorem 3.2 Proof C (3.2 reverse statement)
@[blueprint "thm:P_in_ϕOverF_of_P_props"
  (title := "The image conditions characterize $\\varphi(\\mathbb{F}_q)$")
  (statement := /--
  The reverse part of statement 2 of Theorem 3: every $(x, y) \in E(\mathbb{F}_q)$ such that
  $y + 1 \neq 0$; $(1 + \eta r) ^ 2 - 1$ is a square, where $\eta = (y - 1)/(2(y + 1))$; and
  $x = 2s(c - 1)\chi(c)/r$ whenever $\eta r = -2$, lies in $\varphi(\mathbb{F}_q)$.
  -/)]
theorem P_in_ϕOverF_of_P_props (hcurve : Q.P ∈ Q.EOverF) :
    Q.ϕOverFProps → Q.P ∈ Q.ϕOverF := by
  intro hP
  by_cases hx : Q.x = 0
  · exact P_in_ϕOverF_base_case Q hcurve hP hx
  · exact P_in_ϕOverF_main_case Q hcurve hP hx

end characterization

section theorem3

variable [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]

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
theorem ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages (t : F) :
    (D.ϕ t).val = (D.ϕ (-t)).val
      ↔ ¬(∃ (p : { n : F // n ≠ t ∧ n ≠ -t}), (D.ϕ p.val).val = (D.ϕ t).val) := by
  constructor
  · intro _
    exact ϕ_preimages D t
  · intro _
    exact ϕ_of_t_eq_ϕ_of_neg_t D t

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
    \item $(1 + \eta r) ^ 2 - 1$ is a square, where $\eta = \frac{y - 1}{2(y + 1)}$; and
    \item if $\eta r = -2$ then $x = 2s(c - 1)\chi(c)/r$.
  \end{itemize}
  -/)]
theorem props_iff_mem_ϕOverF [IsNonzeroParam Q.s] [IsRegularParam Q.s] (hcurve : Q.P ∈ Q.EOverF) :
    Q.ϕOverFProps ↔ Q.P ∈ Q.ϕOverF := by
  constructor
  · exact P_in_ϕOverF_of_P_props Q hcurve
  · exact props_of_mem_ϕOverF Q

/-- The explicit inverse formula in part 3 of Theorem 3 recovers a point in `ϕ(F)`.

Starting with `P = ϕ t`, the definitions `Xbar`, `z`, `ubar`, and `tbar` reproduce the paper's
quantities `Xbar`, `z`, `ubar`, and `tbar`; evaluating `ϕ (tbar s P q)` returns the coordinates
of `P`.
-/
@[blueprint "thm:thm3-3"
  (title := "Theorem 3.3: inverting $\\varphi$")
  (statement := /--
  In the situation of Definition 2: if $(x, y) \in \varphi(\mathbb{F}_q)$ then the following
  elements $\bar X, z, \bar u, \bar t$ of $\mathbb{F}_q$ are defined and
  $\varphi(\bar t) = (x, y)$:
  \begin{align*}
    \bar X &= -(1 + \eta r) + ((1 + \eta r) ^ 2 - 1)^{(q+1)/4}, \\
    z &= \chi\bigl((c - 1)s\bar X(1 + \bar X)x(\bar X ^ 2 + 1/c ^ 2)\bigr), \\
    \bar u &= z\bar X, \\
    \bar t &= (1 - \bar u)/(1 + \bar u).
  \end{align*}
  -/)]
theorem ϕ_of_tbar_eq_x_y (t : F) : (D.ϕ (D.decoded t).tbar).val = (D.ϕ t).val := by
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · exact ϕ_of_tbar_eq_x_y_main_case D ⟨t, h⟩
  · have h' : t = 1 ∨ t = -1 := by
      rw [ne_eq, ne_eq, ← not_or, not_not] at h
      exact h
    have hbase : (D.ϕ t).val = ((0 : F), (1 : F)) := ϕ_of_t_eq_zero_one D ⟨t, h'⟩
    rw [ϕ_of_tbar_eq_x_y_base_case D ⟨t, h'⟩, hbase]

/-- The denominator `2 * (y + 1)` in the inverse construction is nonzero on `ϕ(F)`.
This supplies the definedness of `η`, and hence of `Xbar`, in part 3 of Theorem 3. -/
@[blueprint "thm:Xbar_defined"
  (title := "$\\bar X$ is defined")
  (statement := /--
  For $(x, y) \in \varphi(\mathbb{F}_q)$ the denominator $2(y + 1)$ of $\eta$ is nonzero, so
  $\eta$ and hence $\bar X$ of Theorem 3.3 are defined.
  -/)]
theorem Xbar_defined [IsNonzeroParam Q.s] [IsRegularParam Q.s] (hQ : Q.P ∈ Q.ϕOverF) :
    2 * (Q.y + 1) ≠ 0 :=
  mul_ne_zero (two_ne_zero card_mod_four) (props_of_mem_ϕOverF Q hQ).1

omit [DecidableEq F] [IsRegularParam D.s] in
/-- The denominator `c²` occurring in the definition of `z` is nonzero. -/
@[blueprint "thm:z_defined"
  (title := "$z$ is defined")
  (statement := /--
  The denominator $c ^ 2$ occurring in $z$ of Theorem 3.3 is nonzero, so $z$ is defined.
  -/)]
theorem z_defined : D.c ^ 2 ≠ 0 :=
  pow_ne_zero 2 (c_ne_zero D)

/-- The denominator `1 + ubar` in the reconstructed parameter `tbar` is nonzero on `ϕ(F)`. -/
@[blueprint "thm:tbar_defined"
  (title := "$\\bar t$ is defined")
  (statement := /--
  For $(x, y) \in \varphi(\mathbb{F}_q)$ the denominator $1 + \bar u$ of $\bar t$ in
  Theorem 3.3 is nonzero, so $\bar t$ is defined.
  -/)]
theorem tbar_defined [IsNonzeroParam Q.s] [IsRegularParam Q.s] (hQ : Q.P ∈ Q.ϕOverF) :
    1 + Q.ubar ≠ 0 := by
  obtain ⟨t, ht⟩ := hQ
  change 1 + ReconstructionCoordinates.ubar Q.s Q.P (Fintype.card F) ≠ 0
  rw [← ht]
  exact one_add_ubar_ne_zero Q.toParamData t

end theorem3

end Elligator.Elligator1
