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
variable {s : F}
variable {q : ℕ}

----------------------------------
-- TODO move
omit [Fintype F] [DecidableEq F] in
lemma x_y_eq_zero_sign_one (P : {P : F × F // P ∈ EOverF s})
    (hx_eq_zero : P.val.1 = 0) :
    P.val = ((0 : F), (1 : F)) ∨ P.val = ((0 : F), (-1 : F)) := by
  let d := d s
  let x := P.val.1
  let y := P.val.2
  change (x, y) = (0, 1) ∨ (x, y) = (0, -1)
  change x = 0 at hx_eq_zero
  rw [← hx_eq_zero]
  have h_curve_eq : x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2 := by
    have hP := P.prop
    rw [mem_EOverF_iff] at hP
    exact hP
  -- with x = 0, the curve equation reduces to y² = 1, i.e. (y-1)(y+1) = 0.
  have hy_sq_eq_one : y ^ 2 = 1 := by
    rw [hx_eq_zero, zero_pow two_ne_zero, zero_add, mul_zero, zero_mul, add_zero] at h_curve_eq
    exact h_curve_eq
  have hy_eq_pm_one : y = 1 ∨ y = -1 := sq_eq_one_iff.mp hy_sq_eq_one
  rcases hy_eq_pm_one with h | h
  · rw [← h]; left; rfl
  · rw [← h]; right; rfl


lemma x_y_eq_zero_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s}) (P_props : ϕOverFProps s P)
    (x_eq_zero : P.val.1 = 0) :
    P.val = ((0 : F), (1 : F)) := by
  let x := P.val.1
  let y := P.val.2
  have h : y + 1 ≠ 0 := P_props.1
  let h' := x_y_eq_zero_sign_one P x_eq_zero
  change (x, y) = (0, 1)
  rcases h' with h'' | h''
  · exact h''
  · change (x, y) = (0, -1) at h''
    have h''' : y + 1 = 0 := by grind
    contradiction

omit [DecidableEq F] in
lemma y_ne_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s})
    (x_ne_zero : P.val.1 ≠ 0) :
    let y := P.val.2
    y ≠ 1 := by
  intro y h
  let x := P.val.1
  let d := d s
  have h' : x = 0 := by
    have h'' : x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2 := by
      have hP := P.prop
      rw [mem_EOverF_iff] at hP
      exact hP
    have t_h : IsSquare d := by grind
    let t_h' := d_nonsquare sq_ne_pm_two hq_card hq_mod
    contradiction
  contradiction

lemma η_ne_zero (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) :
    (η P.val) ≠ 0 := by
  let x := P.val.1
  let y := P.val.2
  unfold η
  change (y - 1) / (2 * (y + 1)) ≠ 0
  apply div_ne_zero
  · intro h
    have h' := y_ne_one sq_ne_pm_two hq_card hq_mod P x_ne_zero
    have h'': y = 1 := by grind
    contradiction
  · exact mul_ne_zero (two_ne_zero hq_card hq_mod) P_props.1

lemma ϕ_of_t_eq_ϕ_of_neg_t_base_case (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_t := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let ϕ_of_neg_t := (ϕ (-t.val) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_t = ϕ_of_neg_t := by
  rcases t.prop with h2_1 | h2_1
  · change (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      = (ϕ (-t.val) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    rw [h2_1]
    unfold ϕ
    simp
  · change (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      = (ϕ (-t.val) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    rw [h2_1]
    unfold ϕ
    simp

lemma ϕ_of_t_eq_ϕ_of_neg_t_main_case (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_t := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let ϕ_of_neg_t := (ϕ (-t.val) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_t = ϕ_of_neg_t := by
  let t1 := t.val
  let t2 := -t.val
  have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let x1 := x t s q
  let x2 := x ⟨t2, t_h⟩ s q
  let y1 := y t s
  let y2 := y ⟨t2, t_h⟩ s
  have h : y2 = y1 := y_comparison t
  have h' : x2 = x1 := x_comparison t hs_ne_zero hq_card hq_mod
  change (ϕ t1 hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    = (ϕ t2 hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
  grind [ϕ]

-- Original: Theorem 3.1 forward statement, Proof A
@[blueprint "lemma:ϕ_of_t_eq_ϕ_of_neg_t"
  (title := "$\\varphi(t) = \\varphi(-t)$")
  (statement := /--
  The forward part of statement 1 of Theorem 3: for every $t \in \mathbb{F}_q$,
  $$
  \varphi(t) = \varphi(-t) .
  $$
  -/)]
lemma ϕ_of_t_eq_ϕ_of_neg_t (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_t := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let ϕ_of_neg_t := (ϕ (-t) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_t = ϕ_of_neg_t := by
  intro ϕ_of_t ϕ_of_neg_t
  by_cases h : t = 1 ∨ t = -1
  · exact ϕ_of_t_eq_ϕ_of_neg_t_base_case
      ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · exact ϕ_of_t_eq_ϕ_of_neg_t_main_case
      ⟨t, by simp_all⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod

-- Original: Theorem 3.1 backward statement (Original: Proof B as the very last argument)
@[blueprint "thm:ϕ_preimages"
  (title := "$\\varphi$ has no preimages besides $t$ and $-t$")
  (statement := /--
  The reverse part of statement 1 of Theorem 3: for $t \in \mathbb{F}_q$, no element of
  $\mathbb{F}_q$ other than $t$ and $-t$ is a preimage of $\varphi(t)$ under $\varphi$.
  -/)]
theorem ϕ_preimages (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_t := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ¬(∃ (p : { n : F // n ≠ t ∧ n ≠ -t}),
        (ϕ p.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val = ϕ_of_t) := by
  intro ϕ_of_t h
  rcases h with ⟨p, hp⟩
  have h' : p.val = t ∨ p.val = -t := by
    let p_P := ϕ p.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let t_P := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let tbar_of_p := tbar s p_P q
    let tbar_of_t := tbar s t_P q
    have tbar_h : tbar_of_p = p ∨ tbar_of_p = -p :=
      tbar_in_t_or_neg_t p.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    have tbar_h' : tbar_of_t = t ∨ tbar_of_t = -t :=
      tbar_in_t_or_neg_t t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    unfold tbar_of_p p_P at tbar_h
    rw [hp] at tbar_h
    change tbar_of_t = p ∨ tbar_of_t = -p at tbar_h
    rcases tbar_h with h | h <;> grind
  have h'' := p.prop.left
  have h''' := p.prop.right
  rcases h' <;> contradiction

/-- Equality of images under `ϕ` forces the inputs to agree up to sign.
This is the preimage conclusion of Theorem 3, restated in the form needed for the injectivity
argument in Theorem 4. -/
lemma eq_or_eq_neg_of_ϕ_eq (t t' : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (h : ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod = ϕ t' hs_ne_zero sq_ne_pm_two hq_card hq_mod) :
    t = t' ∨ t = -t' := by
  by_contra hne
  push Not at hne
  apply ϕ_preimages t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  use ⟨t', by grind⟩
  simp_all

-- TODO order properly with main result for ϕ below
-- Perhaps move back to var specific sections tho...
-----------------------
omit [Fintype F] [DecidableEq F] in
lemma u_of_zero :
    let u := u ⟨(0 : F), by simp⟩
    u = 1 := by
  simp [u]

omit [Fintype F] [DecidableEq F] in
lemma v_of_zero :
    let v := v ⟨(0 : F), by simp⟩ s
    v = (r s) ^ 2 := by
  intro v_of_t
  unfold v_of_t v
  rw [u_of_zero]
  ring

lemma X_of_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let X := X ⟨(0 : F), by simp⟩ s
    X = 1 := by
  intro X
  unfold X AuxiliaryCoordinates.X
  let χ_of_v := χ (v ⟨(0 : F), by simp⟩ s)
  rw [u_of_zero]
  change χ_of_v * 1 = 1
  unfold χ_of_v
  rw [v_of_zero]
  rw [χ_sq (r_ne_zero hs_ne_zero hq_card hq_mod), mul_one]

lemma y_of_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let y := y ⟨(0 : F), by simp⟩ s
    let r := r s
    y = (r - 4) / (r + 4) := by
  intro y r
  unfold y OutputCoordinates.y
  rw [X_of_zero hs_ne_zero hq_card hq_mod]
  change (r * 1 - (1 + 1) ^ 2) / (r * 1 + (1 + 1) ^ 2) = (r - 4) / (r + 4)
  ring
-----------------------

-- Implicated by main case of Theorem 3 Proof part B
lemma ϕ_of_zero (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_zero := (ϕ (0 : F) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let c := c s
    let r := r s
    ϕ_of_zero  = (2 * (c - 1) * s * (χ c) / r, (r - 4) / (r + 4)) := by
  intro ϕ_of_zero c r
  unfold ϕ_of_zero ϕ
  let h : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 :=
    ⟨(one_ne_zero' F).symm, (neg_ne_zero.mpr one_ne_zero).symm⟩
  let η_of_P := η ϕ_of_zero
  have h' : η_of_P * r = -2 := by
    unfold η_of_P η ϕ_of_zero ϕ
    dsimp
    rw [dite_eq_left h]
    let y := y ⟨(0 : F), h⟩ s
    let X := X ⟨(0 : F), h⟩ s
    change (y - 1) / (2 * (y + 1)) * r = -2
    -- This has to be proven again here as in y_η_h1 and X_η_h1 since
    -- the lemmas itself do not help with concret t values
    unfold y
    rw [y_of_zero hs_ne_zero hq_card hq_mod]
    change ((r - 4) / (r + 4) - 1) / (2 * ((r - 4) / (r + 4) + 1)) * r = -2
    have t_h : 1 = (r + 4) / (r + 4) := by
      rw [add_comm, div_self (four_add_r_ne_zero hs_ne_zero hq_card hq_mod)]
    rw [t_h, ← sub_div, ← add_div, ← sub_sub, ← add_assoc]
    ring_nf
    rw [inv_inv, mul_comm r, mul_assoc _ r, mul_inv_cancel₀ (r_ne_zero hs_ne_zero hq_card hq_mod)]
    rw [mul_one, inv_mul_cancel₀ (four_add_r_ne_zero hs_ne_zero hq_card hq_mod)]
    rw [one_mul, ← mul_neg_one, ← mul_right_inj' (four_ne_zero hq_card hq_mod)]
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (four_ne_zero hq_card hq_mod)]
    ring
  let x_of_t := ϕ_of_zero.1
  have h3 : x_of_t = 2 * s * (c - 1) * (χ c) / r := by
    apply P_in_ϕOverF_with_prop3 (0 : F) hs_ne_zero sq_ne_pm_two hq_card hq_mod
    exact h'
  simp only [ne_eq, not_false_eq_true, and_self, reduceDIte, h]
  rw [y_η_h1 ⟨0, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod h']
  unfold x_of_t ϕ_of_zero ϕ at h3
  grind

-- Used in theorem 3 proof part C
lemma x_y_eq_ϕ_of_zero_of_Xbar_eq_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P}) (y_eq_one : P.val.2 ≠ 1) :
    let x := P.val.1
    let y := P.val.2
    let Xbar_of_P := Xbar s P.val q
    let ϕ_of_zero := ϕ 0 hs_ne_zero sq_ne_pm_two hq_card hq_mod
    Xbar_of_P = 1 → ϕ_of_zero = (x, y) := by
  intro x y Xbar_of_P ϕ_of_zero' Xbar_h
  let r := r s
  let c := c s
  have h1 := η_mul_r_eq_neg_two_of_Xbar_eq_one hq_card hq_mod P Xbar_h
  have h2 : x = 2 * s * (c - 1) * (χ c) / r := P.prop.2.2 h1
  have h3 : y = (r - 4) / (r + 4) :=
    y_with_Xbar_of_Xbar_eq_one hs_ne_zero hq_card hq_mod P y_eq_one Xbar_h
  rw [h2, h3]
  let ϕ_of_zero'' := ϕ_of_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod
  grind

-- Used in theorem 3 proof part C
lemma x_y_eq_ϕ_of_t_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let x := P.val.1
    let y := P.val.2
    let X := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let ϕ_of_t := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    X ≠ 1 → ϕ_of_t = (x, y) := by
  intro x y X t ϕ_of_t h
  unfold ϕ_of_t ϕ
  let h' := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h
  dsimp
  rw [dite_eq_left h']
  let x_of_t := OutputCoordinates.x ⟨t, h'⟩ s q
  let y_of_t := OutputCoordinates.y ⟨t, h'⟩ s
  change (x_of_t, y_of_t) = (x, y)
  let h'' := x_y_of_P_eq_x_y
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h
  grind

lemma ϕ_of_tbar_eq_x_y_base_case (t : { n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let t' := tbar s P q
    let ϕ_of_t' := (ϕ t' hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_t' = (0, 1) := by
  intro P t' ϕ_of_t'
  unfold ϕ_of_t' ϕ
  have h1 : ¬(t' ≠ 1 ∧ t' ≠ -1) := by grind [tbar_eq_one]
  dsimp
  rw [dite_eq_right h1]

lemma ϕ_of_tbar_eq_x_y_main_case (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let t' := tbar s P q
    let ϕ_of_t' := ϕ t' hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let x_of_t := x t s q
    let y_of_t := y t s
    ϕ_of_t' = (x_of_t, y_of_t) := by
  intro P t' ϕ_of_t' x_of_t y_of_t
  have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  unfold ϕ_of_t' ϕ
  rcases (tbar_in_t_or_neg_t t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod) with h | h
  · change t' = t at h
    rw [h]
    dsimp
    rw [dite_eq_left t.prop]
  · change t' = -t at h
    rw [h]
    dsimp
    rw [dite_eq_left t_h]
    unfold x_of_t y_of_t
    symm
    exact P_comparison t hs_ne_zero hq_card hq_mod

lemma ϕ_of_one_eq_zero_one (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_one := (ϕ (1 : F) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_one = (0, 1) := by
  simp [ϕ]

lemma ϕ_of_neg_one_eq_zero_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_neg_one := (ϕ (-1 : F) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_neg_one = (0, 1) := by
  simp [ϕ]

lemma ϕ_of_one_in_ϕ_of_F
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_one := (ϕ (1 : F) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_one ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod := by
  intro ϕ_of_one
  use (1 : F)

lemma P_in_ϕOverF_base_case
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s}) (P_props : ϕOverFProps s P)
    (x_eq_zero : P.val.1 = 0) :
    let ϕOverF := ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod
    P.val ∈ ϕOverF := by
  rw [x_y_eq_zero_one sq_ne_pm_two hq_card hq_mod P P_props x_eq_zero]
  rw [← ϕ_of_one_eq_zero_one hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  exact ϕ_of_one_in_ϕ_of_F hs_ne_zero sq_ne_pm_two hq_card hq_mod

lemma P_in_ϕOverF_main_case_with_y_eq_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s})
    (x_ne_zero : P.val.1 ≠ 0) (y_eq_one : P.val.2 = 1) :
    let ϕOverF := ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod
    P.val ∈ ϕOverF := by
  intro ϕOverF
  let x := P.val.1
  let y := P.val.2
  -- Note: this differs from original proof, which claims that this implies x = 0, contra
  -- I was not able to see that, thus I found an alternative way by contradiction
  have h := P.prop;
  rw [mem_EOverF_iff] at h
  let d := d s;
  rw [y_eq_one] at h
  change x ^ 2 + 1 ^ 2 = 1 + d * x ^ 2 * 1 ^ 2  at h
  rw [← add_right_inj (-1)] at h
  rw [← div_left_inj' x_ne_zero, ← div_left_inj' x_ne_zero] at h
  ring_nf at h
  have h' : x ^ 2 ≠ 0 := by grind
  rw [inv_pow, mul_inv_cancel₀ h', one_mul] at h
  let h'' := d_ne_one sq_ne_pm_two hq_card hq_mod
  symm at h
  contradiction

lemma P_in_ϕOverF_main_case_with_y_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let ϕOverF := ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod
    P.val ∈ ϕOverF := by
  intro ϕOverF
  unfold ϕOverF PhiOverFCharacterization.ϕOverF
  rw [Set.mem_range]
  let Xbar_of_P := Xbar s P q
  let t := t' sq_ne_pm_two hq_card hq_mod P
  by_cases Xbar_h : Xbar_of_P = (1 : F)
  · use 0
    exact x_y_eq_ϕ_of_zero_of_Xbar_eq_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one Xbar_h
  · use t
    exact x_y_eq_ϕ_of_t_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one Xbar_h

lemma P_in_ϕOverF_main_case
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) :
    let ϕOverF := ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod
    P.val ∈ ϕOverF := by
  intro ϕOverF
  let y := P.val.2
  by_cases y_h : y = 1
  · exact P_in_ϕOverF_main_case_with_y_eq_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P x_ne_zero y_h
  · exact P_in_ϕOverF_main_case_with_y_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_h

-- Original: Theorem 3.2 Proof C (3.2 reverse statement)
@[blueprint "thm:P_in_ϕOverF_of_P_props"
  (title := "The image conditions characterize $\\varphi(\\mathbb{F}_q)$")
  (statement := /--
  The reverse part of statement 2 of Theorem 3: every $(x, y) \in E(\mathbb{F}_q)$ such that
  $y + 1 \neq 0$; $(1 + \eta r) ^ 2 - 1$ is a square, where $\eta = (y - 1)/(2(y + 1))$; and
  $x = 2s(c - 1)\chi(c)/r$ whenever $\eta r = -2$, lies in $\varphi(\mathbb{F}_q)$.
  -/)]
theorem P_in_ϕOverF_of_P_props
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF s})
    : ϕOverFProps s P → P.val ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod := by
  intro h1
  let x := P.val.1
  by_cases h2 : x = 0
  · exact P_in_ϕOverF_base_case hs_ne_zero sq_ne_pm_two hq_card hq_mod P h1 h2
  · rw [← not_ne_iff, not_not] at h2
    exact P_in_ϕOverF_main_case hs_ne_zero sq_ne_pm_two hq_card hq_mod P h1 h2


------------------------------

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
theorem ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ_of_t := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let ϕ_of_neg_t := (ϕ (-t) hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_t = ϕ_of_neg_t
    ↔ ¬(∃ (p : { n : F // n ≠ t ∧ n ≠ -t}),
        ϕ p.val hs_ne_zero sq_ne_pm_two hq_card hq_mod = ϕ_of_t) := by
  intro ϕ_of_t ϕ_of_neg_t
  constructor
  · intro _
    exact ϕ_preimages t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · intro _
    exact ϕ_of_t_eq_ϕ_of_neg_t t hs_ne_zero sq_ne_pm_two hq_card hq_mod

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
theorem props_iff_mem_ϕOverF (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    ϕOverFProps s P ↔ P.val ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod := by
  intro P
  constructor
  · exact P_in_ϕOverF_of_P_props hs_ne_zero sq_ne_pm_two hq_card hq_mod P
  · exact P_props_of_P_in_ϕOverF t hs_ne_zero sq_ne_pm_two hq_card hq_mod

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
theorem ϕ_of_tbar_eq_x_y (t : F) -- Fix t ∈ F_q
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    -- Define (x, y) = ϕ(t)
    let P := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let x_of_t := P.1
    let y_of_t := P.2
    -- tbar defined (and used to build ϕ(tbar))
    let t' := tbar s P q
    let ϕ_of_t' := (ϕ t' hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕ_of_t' = (x_of_t, y_of_t) := by
  intro P x_of_P y_of_P t' ϕ_of_t'
  unfold x_of_P y_of_P P ϕ
  dsimp
  split
  · rename_i h
    exact ϕ_of_tbar_eq_x_y_main_case ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · rename_i h
    exact ϕ_of_tbar_eq_x_y_base_case
      ⟨t, by grind⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod

/-- The denominator `2 * (y + 1)` in the inverse construction is nonzero on `ϕ(F)`.
This supplies the definedness of `η`, and hence of `Xbar`, in part 3 of Theorem 3. -/
@[blueprint "thm:Xbar_defined"
  (title := "$\\bar X$ is defined")
  (statement := /--
  For $(x, y) \in \varphi(\mathbb{F}_q)$ the denominator $2(y + 1)$ of $\eta$ is nonzero, so
  $\eta$ and hence $\bar X$ of Theorem 3.3 are defined.
  -/)]
theorem Xbar_defined (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod}) :
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
      rw [dite_eq_right h1_3] at h1_2
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
  The denominator $c ^ 2$ occurring in $z$ of Theorem 3.3 is nonzero, so $z$ is defined.
  -/)]
theorem z_defined (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (c s) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)

/-- The denominator `1 + ubar` in the reconstructed parameter `tbar` is nonzero on `ϕ(F)`. -/
@[blueprint "thm:tbar_defined"
  (title := "$\\bar t$ is defined")
  (statement := /--
  For $(x, y) \in \varphi(\mathbb{F}_q)$ the denominator $1 + \bar u$ of $\bar t$ in
  Theorem 3.3 is nonzero, so $\bar t$ is defined.
  -/)]
theorem tbar_defined (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod}) :
    let ubar_of_P := ubar s P.val q
    (1 + ubar_of_P) ≠ 0 :=
  one_add_ubar_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P

end Elligator.Elligator1
