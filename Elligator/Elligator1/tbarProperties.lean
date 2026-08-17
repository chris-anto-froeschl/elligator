/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.ubarProperties

/-!
# tbar Variable Properties

In this file we introduce some generally helpful lemmas for `tbar` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [Bernstein2013a], Section 3.3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.Primitives.ECC

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

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
  have h : ubar = u := ubar_eq_u t hs_ne_zero sq_ne_pm_two hq_card hq_mod hXXbar
  unfold u Elligator1.u at h
  unfold tbar_of_P tbar
  change (1 - ubar) / (1 + ubar) = t.val
  change ubar = (1 - t.val) / (1 + t.val) at h
  rw [h, sub_div' (one_add_t_ne_zero t)]
  rw [add_div' (1 - t.val) 1 (1 + t.val) (one_add_t_ne_zero t)]
  rw [div_div_div_eq]
  have h' : (1 + t.val) * 2 ≠ 0 := mul_ne_zero (one_add_t_ne_zero t) (two_ne_zero hq_card hq_mod)
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
  let h : ubar = u' := ubar_eq_u' t hs_ne_zero sq_ne_pm_two hq_card hq_mod hXXbar
  unfold u' u at h
  unfold tbar_of_P tbar
  change (1 - ubar) / (1 + ubar) = t'
  change ubar = (1 - t') / (1 + t') at h
  rw [h, sub_div' (one_add_t_ne_zero ⟨t', t_h⟩)]
  rw [add_div' (1 - t') 1 (1 + t') (one_add_t_ne_zero ⟨t', t_h⟩), div_div_div_eq]
  have h' : ((1 + t') * 2) ≠ 0 :=
    mul_ne_zero (one_add_t_ne_zero ⟨t', t_h⟩) (two_ne_zero hq_card hq_mod)
  grind

@[blueprint "lemma:tbar_in_t_or_neg_t"
  (title := "$\\bar t = \\pm t$")
  (statement := /--
  For $t \in \mathbb{F}_q$, the parameter $\bar t$ reconstructed from $\varphi(t)$ in
  Theorem 3.3 satisfies $\bar t = t$ or $\bar t = -t$. This is the key step showing that
  $\varphi(t)$ has no preimages besides $t$ and $-t$.
  -/)]
lemma tbar_in_t_or_neg_t (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let t' := -t
    let tbar_of_P := tbar s P q
    tbar_of_P = t ∨ tbar_of_P = t' := by
  intro P t' tbar_of_P
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · rcases (Xbar_h4 ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod) with h1 | h1
    · left
      exact tbar_eq_t ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod h1
    · right
      exact tbar_eq_t' ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod h1
  · have h' : t = 1 ∨ t = -1 := by
      rw [← not_ne_iff, ← not_ne_iff, ← Lean.Grind.not_and]
      exact h
    unfold tbar_of_P t'
    rw [tbar_eq_one ⟨t, h'⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod]
    grind

/-- `t'` is the `t` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def t' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let u := u' sq_ne_pm_two hq_card hq_mod P
  (1 - u) / (1 + u)

lemma t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → t ≠ 1 ∧ t ≠ -1 := by
  intro X t h1
  unfold t t'
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let u'_eq_Xbar_or_u'_eq_neg_Xbar := u'_eq_Xbar_or_u'_eq_neg_Xbar
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  change u = X ∨ u = -X at u'_eq_Xbar_or_u'_eq_neg_Xbar
  change (1 - u) / (1 + u) ≠ 1 ∧ (1 - u) / (1 + u) ≠ -1
  let one_add_u'_ne_zero := one_add_u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let u'_ne_zero := u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let two_ne_zero := two_ne_zero hq_card hq_mod
  and_intros
  · intro h2
    have h3 : 2 = 0 := by grind
    contradiction
  · intro h2
    have h3 : 2 = 0 := by grind
    contradiction

lemma one_add_t'_ne_zero (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → t + 1 ≠ 0 := by
  grind [t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one]

lemma u'_eq_one_sub_t'_div_one_add_t'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P.val q
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → u = (1 - t) / (1 + t) := by
  intro X u t h1
  unfold t t'
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let one_add_u'_ne_zero := one_add_u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let two_ne_zero := two_ne_zero hq_card hq_mod
  grind

lemma u'_eq_u (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q
      X ≠ 1) :
    let u' := u' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let u := u ⟨t, t_h⟩
    u' = u := by
  grind [u', u, u'_eq_one_sub_t'_div_one_add_t']

lemma v'_eq_v (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P.val q;
      X ≠ 1) :
    let v' := v' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let v := v ⟨t, t_h⟩ s
    v' = v := by
  grind [v', v, u'_eq_one_sub_t'_div_one_add_t', u'_eq_u]

lemma X'_eq_X (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q;
      X ≠ 1) :
    let X' := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let X := X ⟨t, t_h⟩ s
    X' = X := by
  intro X' t t_h X
  let h1 := u'_eq_u hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h2 := v'_eq_v hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h3 := X'_eq_χ_of_v'_mul_u'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold X'
  rw [h3, h1, h2]
  rfl

lemma Y'_eq_Y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q;
      X ≠ 1) :
    let Y' := Y' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let Y := Y ⟨t, t_h⟩ s q
    Y' = Y := by
  intro Y' t t_h Y
  let h1 := u'_eq_u hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h2 := v'_eq_v hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h3 := Y'_observation2
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold Y'
  rw [h3, h1, h2]
  rfl

/-- `x'` is the `x` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def x' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let c := c s
  let X' := Xbar s P q
  let Y' := Y' sq_ne_pm_two hq_card hq_mod P
  (c - 1) * s * X' * (1 + X') / Y'

lemma x'_eq_x (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let x := x ⟨t, t_h⟩ s q
    let x' := x' sq_ne_pm_two hq_card hq_mod P
    x' = x := by
  intro t t_h x x'
  unfold x' Elligator1.x' x Elligator1.x
  let hY'_eq_Y := Y'_eq_Y hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let hX'_eq_X := X'_eq_X hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

/-- `y'` is the `y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def y' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q)
    (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let X' := Xbar s P q
  let r := r s
  (r * X' - (1 + X') ^ 2) / (r * X' + (1 + X') ^ 2)

lemma y'_eq_y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y' := y' sq_ne_pm_two hq_card hq_mod P
    y' = y := by
  intro t t_h y y'
  unfold y' Elligator1.y' y Elligator1.y
  let hX'_eq_X := X'_eq_X
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

theorem x'_and_y'_fulfill_curve_equation
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let x' := x' sq_ne_pm_two hq_card hq_mod P
    let y' := y' sq_ne_pm_two hq_card hq_mod P
    let d := d s
    have d_h : d ≠ 0 ∧ d ≠ 1 := d_ne_zero_and_d_ne_one sq_ne_pm_two hq_card hq_mod
    edwardsCurveEquation x' y' ⟨d, d_h⟩ := by
  intro x' y' d
  let t := t' sq_ne_pm_two hq_card hq_mod P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let x := x ⟨t, t_h⟩ s q
  let y := y ⟨t, t_h⟩ s
  let x'_eq_x := x'_eq_x hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let y'_eq_y := y'_eq_y hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h := curve_equation ⟨t, t_h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
  simp only [edwardsCurveEquation_iff]
  grind [x'_eq_x, y'_eq_y]

lemma y_eq_y_of_P (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y_of_P := P.val.2
    y = y_of_P := by
  intro t t_h y y_of_P
  let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold y_of_P
  rw [y_with_Xbar]
  unfold y Elligator1.y
  let h := X'_eq_X hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

lemma x_eq_x_of_P (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let x := x ⟨t, t_h⟩ s q
    let x_of_P := P.val.1
    x = x_of_P := by
  intro t t_h x x_of_P
  let Y' := Y' sq_ne_pm_two hq_card hq_mod P
  let c := c s
  let X := Xbar s P q
  let Y'_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  change x_of_P ≠ 0 at x_ne_zero
  have h1 : Y' = (c - 1) * s * X * (1 + X) / x_of_P := by grind [Y', Elligator1.Y']
  have h2 : x_of_P = (c - 1) * s * X * (1 + X) / Y' := by
    unfold Y' Elligator1.Y'
    rw [← div_left_inj' x_ne_zero, ← mul_left_inj' Y'_ne_zero]
    change x_of_P / x_of_P * Y' = (c - 1) * s * X * (1 + X) / Y' / x_of_P * Y'
    grind
  rw [h2]
  let h3 := Y'_eq_Y
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h4 := X'_eq_X
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold Y' X
  rw [h3, h4]
  rfl

lemma x_y_of_P_eq_x_y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y_of_P := P.val.2
    let x := x ⟨t, t_h⟩ s q
    let x_of_P := P.val.1
    (x, y) = (x_of_P, y_of_P) := by
  grind [x_eq_x_of_P, y_eq_y_of_P]

end Elligator.Elligator1
