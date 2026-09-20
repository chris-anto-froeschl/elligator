/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Elligator.Elligator1.ReconstructionCoordinates
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# ϕ_over_F Characterization

The three conditions of Theorem 3 characterizing the image `ϕ(F)` inside `E(F)`, and the proof
that every point of the image satisfies them.

## Main Results

* `ϕOverFProp1`, `ϕOverFProp2`, `ϕOverFProp3`, `ϕOverFProps`: the image conditions.
* `ϕOverF`: the image of the decoding map `ϕ`.
* `P_props_of_P_in_ϕOverF`: every point of the image satisfies the three conditions.

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.PhiOverFCharacterization

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates
open Elligator.Elligator1.ReconstructionCoordinates

variable (D : ParamData F)
variable (M : MapData F)
variable (Q : PointData F)

/-- `ϕOverFProp1` is the first property fulfilled by Ps in `EOverF s`.
This property does not have to consider a dedicated field `F` with `q`.
This restriction is defined during the context evolution.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp1"
  (title := "Image condition 1: $y + 1 \\neq 0$")
  (statement := /--
  The first of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies
  $$
  y + 1 \neq 0 .
  $$
  -/)]
def ϕOverFProp1 (P : F × F) : Prop :=
    let y := P.snd
    y + 1 ≠ 0

/-- PointData wrapper for `ϕOverFProp1`. -/
def _root_.Elligator.PointData.ϕOverFProp1 : Prop :=
    PhiOverFCharacterization.ϕOverFProp1 Q.P

/-- `ϕOverFProp2` is the second property fulfilled by Ps in `EOverF s`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp2"
  (title := "Image condition 2: $(1 + \\eta r) ^ 2 - 1$ is a square")
  (statement := /--
  The second of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies that
  $$
  (1 + \eta r) ^ 2 - 1
  $$
  is a square, where $\eta = (y - 1)/(2(y + 1))$.
  -/)]
def ϕOverFProp2 (s : F) (P : F × F) : Prop :=
    let r := r s
    let η := η P
    IsSquare ((1 + η * r) ^ 2 - 1)

/-- PointData wrapper for `ϕOverFProp2`. -/
def _root_.Elligator.PointData.ϕOverFProp2 : Prop :=
    PhiOverFCharacterization.ϕOverFProp2 Q.s Q.P

/-- `ϕOverFProp3` is the third property fulfilled by Ps in `EOverF s`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp3"
  (title := "Image condition 3: the exceptional case $\\eta r = -2$")
  (statement := /--
  The third of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies that if $\eta r = -2$ then
  $$
  x = 2s(c - 1)\chi(c)/r .
  $$
  -/)]
def ϕOverFProp3 (s : F) (P : F × F) : Prop :=
    let x := P.fst
    let c := c s
    let r := r s
    let η := η P
    η * r = -2 → x = 2 * s * (c - 1) * (χ c) / r

/-- PointData wrapper for `ϕOverFProp3`. -/
def _root_.Elligator.PointData.ϕOverFProp3 : Prop :=
    PhiOverFCharacterization.ϕOverFProp3 Q.s Q.P

/-- `ϕOverFProps` combines the previously defined properties which are fulfilled by Ps
in `EOverF s`, i.e. `ϕOverFProp1`, `ϕOverFProp2` and `ϕOverFProp3`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProps"
  (title := "The image conditions of Theorem 3")
  (statement := /--
  The conjunction of the three conditions of Theorem 3 for a point $(x, y) \in E(\mathbb{F}_q)$:
  $y + 1 \neq 0$; $(1 + \eta r) ^ 2 - 1$ is a square, where $\eta = (y - 1)/(2(y + 1))$; and if
  $\eta r = -2$ then $x = 2s(c - 1)\chi(c)/r$.
  -/)]
def ϕOverFProps (s : F) (P : F × F) : Prop := ϕOverFProp1 P ∧ ϕOverFProp2 s P ∧ ϕOverFProp3 s P

/-- PointData wrapper for `ϕOverFProps`. -/
def _root_.Elligator.PointData.ϕOverFProps : Prop :=
    PhiOverFCharacterization.ϕOverFProps Q.s Q.P

/-- `ϕOverF` is the set of Ps produced by `ϕ`.

Original: Section "3.2 The map", Definition 2
-/
@[blueprint "def:ϕOverF"
  (title := "The image $\\varphi(\\mathbb{F}_q)$")
  (statement := /--
  The image of the decoding function of Definition 2,
  $$
  \varphi(\mathbb{F}_q) = \{\varphi(t) : t \in \mathbb{F}_q\} \subseteq E(\mathbb{F}_q) .
  $$
  -/)]
def ϕOverF {s : F} (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_mod : Fintype.card F % 4 = 3) : Set (F × F) :=
    Set.range (fun t : F => ϕ t hs_ne_zero sq_ne_pm_two hq_mod)

/-- ParamData wrapper for `ϕOverF`. -/
def _root_.Elligator.ParamData.ϕOverF
    [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F] : Set (F × F) :=
    PhiOverFCharacterization.ϕOverF (s_ne_zero (s := D.s)) s_sq_ne_pm_two card_mod_four

section base_case

variable (t : {n : F // n = 1 ∨ n = -1})

lemma P_in_ϕOverF_with_prop1_base_case
    [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F] :
    (D.decoded t.val).ϕOverFProp1 := by
  have hP : (D.decoded t.val).P = ((0 : F), (1 : F)) := ϕ_of_t_eq_zero_one D t
  change (D.decoded t.val).P.2 + 1 ≠ 0
  rw [hP]
  intro h_contra
  exact two_ne_zero (F := F) card_mod_four (by linear_combination h_contra)

lemma P_in_ϕOverF_with_prop2_base_case
    [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F] :
    (D.decoded t.val).ϕOverFProp2 := by
  change IsSquare ((1 + η (D.decoded t.val).P * r (D.decoded t.val).s) ^ 2 - 1)
  rw [show η (D.decoded t.val).P = 0 from η_eq_zero D t]
  simp

lemma P_in_ϕOverF_with_prop3_base_case
    [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F] :
    (D.decoded t.val).ϕOverFProp3 := by
  intro h_contra
  exfalso
  rw [show η (D.decoded t.val).P = 0 from η_eq_zero D t, zero_mul] at h_contra
  exact two_ne_zero (F := F) card_mod_four (by linear_combination h_contra)

end base_case

section main_case

variable [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F]

/-- The value of `η` at the point constructed from a nonexceptional input. -/
lemma point_η_eq_η : M.point.η = M.η := by
  rw [MapData.η, M.decoded_eq_point]

omit [IsRegularParam M.s] in
lemma P_in_ϕOverF_with_prop1_main_case : M.point.ϕOverFProp1 :=
  y_add_one_ne_zero M

lemma P_in_ϕOverF_with_prop2_main_case : M.point.ϕOverFProp2 := by
  change IsSquare ((1 + M.point.η * M.r) ^ 2 - 1)
  rw [point_η_eq_η M]
  have h1 : M.X ^ 2 + 2 * (1 + M.η * M.r) * M.X + 1 = 0 := X_quadratic_eq_of_η M
  have h2 : NeZero (2 : F) := ⟨two_ne_zero card_mod_four⟩
  rw [pow_two] at h1
  nth_rw 1 [← one_mul M.X, mul_assoc] at h1
  rw [@quadratic_eq_zero_iff_discrim_eq_sq
    F _ 1 (2 * (1 + M.η * M.r)) 1 h2 _ (one_ne_zero' F) M.X] at h1
  unfold discrim at h1
  rw [mul_pow 2 _ 2] at h1
  have h3 : 2 ^ 2 = (4 : F) := by norm_num
  rw [mul_one, h3, ← mul_sub, mul_comm] at h1
  rw [← div_left_inj' (four_ne_zero (F := F) card_mod_four)] at h1
  rw [mul_div_assoc, div_self (four_ne_zero (F := F) card_mod_four)] at h1
  rw [mul_one, ← h3, ← div_pow _ _ 2] at h1
  rw [h1]
  apply IsSquare.sq

section exceptional

variable (hηr : M.η * M.r = -2)

include hηr

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h1 : (M.X - 1) ^ 2 = 0 := by
  have h : M.X + 1 / M.X = -2 * (1 + M.η * M.r) :=
    X_add_inv_X_eq_neg_two_mul_one_add_η_mul_r M
  rw [hηr] at h
  have hX_ne_zero : M.X ≠ 0 := X_ne_zero M
  field_simp at h
  linear_combination h

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h2 : M.X = 1 := by
  have hXpow : (M.X - 1) ^ 2 = 0 := X_η_h1 M hηr
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hXpow
  linear_combination this

-- Used in the main case of Theorem 3 Proof part B
lemma u_η_h1 : M.u = 1 := by
  have hv_ne_zero : M.v ≠ 0 := v_ne_zero M
  have h1 : M.X = χ M.v * M.u := rfl
  rw [X_η_h2 M hηr] at h1
  rcases χ_values (a := M.v) with h2 | h2 | h2
  · exact absurd (a_eq_zero_of_χ_of_a_eq_zero h2) hv_ne_zero
  · rw [h2] at h1
    exfalso
    have h_one_add_t_ne_zero : (1 : F) + M.t ≠ 0 := one_add_t_ne_zero M.tSub
    have hu : M.u = -1 := by linear_combination h1
    have hu' : (1 : F) - M.t = M.u * (1 + M.t) := by
      change (1 : F) - M.t = (1 - M.t) / (1 + M.t) * (1 + M.t)
      rw [div_mul_cancel₀ _ h_one_add_t_ne_zero]
    rw [hu] at hu'
    exact two_ne_zero (F := F) card_mod_four (by linear_combination hu')
  · rw [h2, one_mul] at h1
    exact h1.symm

-- Used in the main case of Theorem 3 Proof part B
lemma t_η_h1 : M.t = 0 := by
  have h1 : M.u = 1 := u_η_h1 M hηr
  have h_one_add_t_ne_zero : (1 : F) + M.t ≠ 0 := one_add_t_ne_zero M.tSub
  have h_two_ne_zero : (2 : F) ≠ 0 := two_ne_zero card_mod_four
  have hu' : (1 : F) - M.t = M.u * (1 + M.t) := by
    change (1 : F) - M.t = (1 - M.t) / (1 + M.t) * (1 + M.t)
    rw [div_mul_cancel₀ _ h_one_add_t_ne_zero]
  rw [h1, one_mul] at hu'
  have h2t : (2 : F) * M.t = 0 := by linear_combination -hu'
  rcases mul_eq_zero.mp h2t with h | h
  · exact absurd h h_two_ne_zero
  · exact h

-- Used in the main case of Theorem 3 Proof part B
lemma v_η_h1 : M.v = M.r ^ 2 := by
  change M.u ^ 5 + (M.r ^ 2 - 2) * M.u ^ 3 + M.u = M.r ^ 2
  rw [u_η_h1 M hηr]
  ring

-- Used in the main case of Theorem 3 Proof part B
lemma Y_η_h1 : M.Y = M.r * (χ M.c) := by
  have hc_ne_zero : M.c ≠ 0 := c_ne_zero M.toParamData
  have hr_ne_zero : M.r ≠ 0 := r_ne_zero M.toParamData
  have hstep1 : M.Y = (M.r ^ 2) ^ ((Fintype.card F + 1) / 4) * χ (1 + 1 / M.c ^ 2) := by
    change (χ M.v * M.v) ^ ((Fintype.card F + 1) / 4) * χ M.v * χ (M.u ^ 2 + 1 / M.c ^ 2) = _
    rw [v_η_h1 M hηr, u_η_h1 M hηr,
      χ_a_eq_one (pow_ne_zero 2 hr_ne_zero) (IsSquare.sq M.r)]
    simp only [one_mul, mul_one, one_pow]
  have hsum : (1 : F) + 1 / M.c ^ 2 = M.r / M.c := by
    have hr : M.r = M.c + 1 / M.c := rfl
    rw [hr]
    field_simp
  rw [hstep1, hsum, b_pow_q_add_one_div_four_eq_χ_of_a_mul_a card_mod_four]
  rw [show M.r / M.c = M.r * (1 / M.c) by ring, χ_mul, ← χ_inv]
  have hregroup : χ M.r * M.r * (χ M.r * χ M.c) = (χ M.r * χ M.r) * (M.r * χ M.c) := by ring
  rw [hregroup, χ_mul_self_eq_one hr_ne_zero, one_mul]

-- Implicated by main case of Theorem 3 proof part B.
lemma y_η_h1 : M.y = (M.r - 4) / (M.r + 4) := by
  change (M.r * M.X - (1 + M.X) ^ 2) / (M.r * M.X + (1 + M.X) ^ 2) = _
  rw [X_η_h2 M hηr]
  norm_num

end exceptional

lemma P_in_ϕOverF_with_prop3_main_case : M.point.ϕOverFProp3 := by
  change M.point.η * M.r = -2 → M.x = 2 * M.s * (M.c - 1) * (χ M.c) / M.r
  rw [point_η_eq_η M]
  intro hηr
  have hr_ne_zero : M.r ≠ 0 := r_ne_zero M.toParamData
  have hχc_ne_zero : χ M.c ≠ 0 := χ_a_ne_zero (c_ne_zero M.toParamData)
  change (M.c - 1) * M.s * M.X * (1 + M.X) / M.Y = _
  rw [X_η_h2 M hηr, Y_η_h1 M hηr]
  rw [div_eq_div_iff (mul_ne_zero hr_ne_zero hχc_ne_zero) hr_ne_zero]
  have hχc : χ M.c * χ M.c = 1 := χ_mul_self_eq_one (c_ne_zero M.toParamData)
  calc
    (M.c - 1) * M.s * 1 * (1 + 1) * M.r
        = 2 * M.s * (M.c - 1) * (χ M.c * χ M.c) * M.r := by rw [hχc]; ring
    _ = 2 * M.s * (M.c - 1) * χ M.c * (M.r * χ M.c) := by ring

end main_case

section image

variable [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]

-- Original: Theorem 3.2 Proof B prop 1 argumentation
lemma P_in_ϕOverF_with_prop1 (t : F) : (D.decoded t).ϕOverFProp1 := by
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · have hP : (D.decoded t).P = (D.withInput t h.1 h.2).point.P :=
      (D.withInput t h.1 h.2).decoded_P_eq_point_P
    change ϕOverFProp1 (D.decoded t).P
    rw [hP]
    exact P_in_ϕOverF_with_prop1_main_case (D.withInput t h.1 h.2)
  · have h' : t = 1 ∨ t = -1 := by
      rw [ne_eq, ne_eq, ← not_or, not_not] at h
      exact h
    exact P_in_ϕOverF_with_prop1_base_case D ⟨t, h'⟩

-- Original: Theorem 3.2 Proof B prop 2 argumentation
lemma P_in_ϕOverF_with_prop2 (t : F) : (D.decoded t).ϕOverFProp2 := by
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · have hP : (D.decoded t).P = (D.withInput t h.1 h.2).point.P :=
      (D.withInput t h.1 h.2).decoded_P_eq_point_P
    change ϕOverFProp2 (D.decoded t).s (D.decoded t).P
    rw [hP]
    exact P_in_ϕOverF_with_prop2_main_case (D.withInput t h.1 h.2)
  · have h' : t = 1 ∨ t = -1 := by
      rw [ne_eq, ne_eq, ← not_or, not_not] at h
      exact h
    exact P_in_ϕOverF_with_prop2_base_case D ⟨t, h'⟩

-- Original: Theorem 3.2 Proof B prop 3 argumentation
lemma P_in_ϕOverF_with_prop3 (t : F) : (D.decoded t).ϕOverFProp3 := by
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · have hP : (D.decoded t).P = (D.withInput t h.1 h.2).point.P :=
      (D.withInput t h.1 h.2).decoded_P_eq_point_P
    change ϕOverFProp3 (D.decoded t).s (D.decoded t).P
    rw [hP]
    exact P_in_ϕOverF_with_prop3_main_case (D.withInput t h.1 h.2)
  · have h' : t = 1 ∨ t = -1 := by
      rw [ne_eq, ne_eq, ← not_or, not_not] at h
      exact h
    exact P_in_ϕOverF_with_prop3_base_case D ⟨t, h'⟩

-- Original: Theorem 3.2 Proof B (3.2 forward statement)
@[blueprint "thm:P_props_of_P_in_ϕOverF"
  (title := "Points of $\\varphi(\\mathbb{F}_q)$ satisfy the image conditions")
  (statement := /--
  The forward part of statement 2 of Theorem 3: every $(x, y) \in \varphi(\mathbb{F}_q)$
  satisfies $y + 1 \neq 0$; $(1 + \eta r) ^ 2 - 1$ is a square, where
  $\eta = (y - 1)/(2(y + 1))$; and if $\eta r = -2$ then $x = 2s(c - 1)\chi(c)/r$.
  -/)]
theorem P_props_of_P_in_ϕOverF (t : F) : (D.decoded t).ϕOverFProps :=
  ⟨P_in_ϕOverF_with_prop1 D t, P_in_ϕOverF_with_prop2 D t, P_in_ϕOverF_with_prop3 D t⟩

lemma P_of_ϕ_in_ϕOverF (t : F) : (D.ϕ t).val ∈ D.ϕOverF := ⟨t, rfl⟩

lemma P_of_ϕ_fulfills_ϕOverFProps (t : F) : (D.decoded t).ϕOverFProps :=
  P_props_of_P_in_ϕOverF D t

/-- Every point of the image `ϕ(F)` satisfies the three conditions of Theorem 3. -/
theorem props_of_mem_ϕOverF [IsNonzeroParam Q.s] [IsRegularParam Q.s] (hQ : Q.P ∈ Q.ϕOverF) :
    Q.ϕOverFProps := by
  obtain ⟨t, ht⟩ := hQ
  change ϕOverFProps Q.s Q.P
  rw [← ht]
  exact P_props_of_P_in_ϕOverF Q.toParamData t

end image

end Elligator.Elligator1.PhiOverFCharacterization
