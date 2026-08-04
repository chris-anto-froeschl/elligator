/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.u2Properties

/-!
# t2 Variable Properties

In this file we introduce some generally helpful lemmas for `t2` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma t2_eq_one
  (t : { t : F // t = 1 ∨ t = -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3
  let t2_of_P := t2 s P q
  t2_of_P = 1 := by
    intro P t2_of_P
    unfold t2_of_P t2
    let u2_of_P := u2 s P q
    change (1 - u2_of_P) / (1 + u2_of_P) = 1
    unfold u2_of_P
    rw [u2_eq_zero t s_h1 s_h2 q_h1 q_h2 q_h3]
    simp

lemma t2_eq_t
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (X_h :
    let P := ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3
    let X := X t s
    let X2 := X2 s P q
    X2 = X)
  :
  let P := ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3
  let t2_of_P := t2 s P q
  t2_of_P = t := by
    intro P t2_of_P
    let u := u t
    let u2 := u2 s P q
    have h : u2 = u := by exact u2_eq_u t s_h1 s_h2 q_h1 q_h2 q_h3 X_h
    unfold u Elligator1.u at h
    unfold t2_of_P t2
    change (1 - u2) / (1 + u2) = t.val
    change u2 = (1 - t.val) / (1 + t.val) at h
    rw [h, sub_div' (one_add_t_ne_zero t)]
    rw [add_div' (1 - t.val) 1 (1 + t.val) (one_add_t_ne_zero t)]
    rw [div_div_div_eq]
    have h' : (1 + t.val) * 2 ≠ 0 := mul_ne_zero (one_add_t_ne_zero t) (two_ne_zero q_h1 q_h2 q_h3)
    grind

lemma t2_eq_t'
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (X_h :
    let P := ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3
    let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let X2 := X2 s P q
    X2 = X')
  :
  let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).val
  let t2_of_P := t2 s P q
  let t' := -t.val
  t2_of_P = t' := by
    intro P t2_of_P t'
    have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let u' := u ⟨t', t_h⟩
    let u2 := u2 s P q
    let h : u2 = u' := u2_eq_u' t s_h1 s_h2 q_h1 q_h2 q_h3 X_h
    unfold u' u at h
    unfold t2_of_P t2
    change (1 - u2) / (1 + u2) = t'
    change u2 = (1 - t') / (1 + t') at h
    rw [h, sub_div' (one_add_t_ne_zero ⟨t', t_h⟩)]
    rw [add_div' (1 - t') 1 (1 + t') (one_add_t_ne_zero ⟨t', t_h⟩), div_div_div_eq]
    have h' : ((1 + t') * 2) ≠ 0 :=
      mul_ne_zero (one_add_t_ne_zero ⟨t', t_h⟩) (two_ne_zero q_h1 q_h2 q_h3)
    grind

@[blueprint "lemma:t2_in_t_or_neg_t"
  (title := "$\\bar t = \\pm t$")
  (statement := /--
  For $t \in \mathbb{F}_q$, the parameter $\bar t$ reconstructed from $\varphi(t)$ in
  Theorem 3.3 satisfies $\bar t = t$ or $\bar t = -t$. This is the key step showing that
  $\varphi(t)$ has no preimages besides $t$ and $-t$.
  -/)]
lemma t2_in_t_or_neg_t
  (t : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := ϕ t s_h1 s_h2 q_h1 q_h2 q_h3
  let t' := -t
  let t2_of_P := t2 s P q
  t2_of_P = t ∨ t2_of_P = t' := by
    intro P t' t2_of_P
    by_cases h : t ≠ 1 ∧ t ≠ -1
    · rcases (X2_h4 ⟨t, h⟩ s_h1 s_h2 q_h1 q_h2 q_h3) with h1 | h1
      · left
        exact t2_eq_t ⟨t, h⟩ s_h1 s_h2 q_h1 q_h2 q_h3 h1
      · right
        exact t2_eq_t' ⟨t, h⟩ s_h1 s_h2 q_h1 q_h2 q_h3 h1
    · have h' : t = 1 ∨ t = -1 := by
        rw [← not_ne_iff, ← not_ne_iff, ← Lean.Grind.not_and]
        exact h
      unfold t2_of_P t'
      rw [t2_eq_one ⟨t, h'⟩ s_h1 s_h2 q_h1 q_h2 q_h3]
      grind

/-- `t'` is the `t` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def t'
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  : F :=
  let u := u' s_h2 q_h1 q_h3 P
  (1 - u) / (1 + u)

lemma t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  :
  let X := X2 s P q
  let t := t' s_h2 q_h1 q_h3 P
  X ≠ 1 → t ≠ 1 ∧ t ≠ -1 := by
    intro X t h1
    unfold t t'
    let u := u' s_h2 q_h1 q_h3 P
    let u'_eq_X2_or_u'_eq_neg_X2 :=
      u'_eq_X2_or_u'_eq_neg_X2 s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    change u = X ∨ u = -X at u'_eq_X2_or_u'_eq_neg_X2
    change (1 - u) / (1 + u) ≠ 1 ∧ (1 - u) / (1 + u) ≠ -1
    let one_add_u'_ne_zero :=
      one_add_u'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one h1
    let u'_ne_zero := u'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one h1
    let two_ne_zero := two_ne_zero q_h1 q_h2 q_h3
    and_intros
    · intro h2
      have h3 : 2 = 0 := by grind
      contradiction
    · intro h2
      have h3 : 2 = 0 := by grind
      contradiction

lemma one_add_t'_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  :
  let X := X2 s P q
  let t := t' s_h2 q_h1 q_h3 P
  X ≠ 1 → t + 1 ≠ 0 := by grind [t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one]

lemma u'_eq_one_sub_t'_over_one_add_t'
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  :
  let X := X2 s P.val q
  let u := u' s_h2 q_h1 q_h3 P
  let t := t' s_h2 q_h1 q_h3 P
  X ≠ 1 → u = (1 - t) / (1 + t) := by
    intro X u t h1
    unfold t t'
    let u := u' s_h2 q_h1 q_h3 P
    let one_add_u'_ne_zero :=
      one_add_u'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one h1
    let two_ne_zero := two_ne_zero q_h1 q_h2 q_h3
    grind

lemma u'_eq_u
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X := X2 s P q
    X ≠ 1)
  :
  let u' := u' s_h2 q_h1 q_h3 P
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let u := u ⟨t, t_h⟩
  u' = u := by grind [u', u, u'_eq_one_sub_t'_over_one_add_t']

lemma v'_eq_v
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X := X2 s P.val q;
    X ≠ 1)
  :
  let v' := v' s_h2 q_h1 q_h3 P
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let v := v ⟨t, t_h⟩ s
  v' = v := by grind [v', v, u'_eq_one_sub_t'_over_one_add_t', u'_eq_u]

lemma X'_eq_X
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X := X2 s P q;
    X ≠ 1)
  :
  let X' := X2 s P q
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let X := X ⟨t, t_h⟩ s
  X' = X := by
    intro X' t t_h X
    let h1 := u'_eq_one_sub_t'_over_one_add_t'
      s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h2 := u'_eq_u s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h3 := v'_eq_v s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h4 := X'_eq_χ_of_v'_mul_u' s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    unfold X'
    rw [h4, h2, h3]
    change X = X
    rfl

lemma Y'_eq_Y
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X := X2 s P q;
    X ≠ 1)
  :
  let Y' := Y' s_h2 q_h1 q_h3 P
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let Y := Y ⟨t, t_h⟩ s q
  Y' = Y := by
    intro Y' t t_h Y
    let h2 := u'_eq_u s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h3 := v'_eq_v s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h4 := Y'_observation2 s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    unfold Y'
    rw [h4, h2, h3]
    change Y = Y
    rfl

/-- `x'` is the `x` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def x'
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  : F :=
  let c := c s
  let X' := X2 s P q
  let Y' := Y' s_h2 q_h1 q_h3 P
  (c - 1) * s * X' * (1 + X') / Y'

lemma x'_eq_x
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X' := X2 s P q
    X' ≠ 1)
  :
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let x := x ⟨t, t_h⟩ s q
  let x' := x' s_h2 q_h1 q_h3 P
  x' = x := by
    intro t t_h x x'
    unfold x' Elligator1.x' x Elligator1.x
    let h1 := u'_eq_u s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h2 := v'_eq_v s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h2 := Y'_eq_Y s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h2 := X'_eq_X s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    grind

/-- `y'` is the `y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
noncomputable def y'
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  : F :=
  let X' := X2 s P q
  let r := r s
  (r * X' - (1 + X')^2) / (r * X' + (1 + X')^2)

lemma y'_eq_y
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X' := X2 s P q
    X' ≠ 1)
  :
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let y := y ⟨t, t_h⟩ s
  let y' := y' s_h2 q_h1 q_h3 P
  y' = y := by
    intro t t_h y y'
    unfold y' Elligator1.y' y Elligator1.y
    let h1 := u'_eq_u s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h2 := v'_eq_v s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h2 := Y'_eq_Y s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h2 := X'_eq_X s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    grind

theorem x'_and_y'_fulfill_curve_equation
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X' := X2 s P q
    X' ≠ 1)
  :
  let x' := x' s_h2 q_h1 q_h3 P
  let y' := y' s_h2 q_h1 q_h3 P
  let d := d s
  have d_h : d ≠ 0 ∧ d ≠ 1 := by exact d_ne_zero_and_d_ne_one s_h2 q_h1 q_h3
  edwardsCurveEquation x' y' ⟨d, d_h⟩ := by
    intro x' y' d
    let t := t' s_h2 q_h1 q_h3 P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
      s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let x := x ⟨t, t_h⟩ s q
    let y := y ⟨t, t_h⟩ s
    let x'_eq_x := x'_eq_x s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let y'_eq_y := y'_eq_y s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h1 := curve_equation ⟨t, t_h⟩ s_h1 s_h2 q_h1 q_h2 q_h3
    simp only [edwardsCurveEquation_iff]
    grind [x'_eq_x, y'_eq_y]

lemma y_eq_y_of_P
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X' := X2 s P q
    X' ≠ 1)
  :
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let y := y ⟨t, t_h⟩ s
  let y_of_P := P.val.2
  y = y_of_P := by
    intro t t_h y y_of_P
    let y_with_X2 := y_with_X2 s_h1 q_h1 q_h2 q_h3 ⟨P.val, P_props⟩ y_ne_one
    unfold y_of_P
    rw [y_with_X2]
    unfold y Elligator1.y
    let h2 := X'_eq_X s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    grind

lemma x_eq_x_of_P
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X' := X2 s P q
    X' ≠ 1)
  :
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let x := x ⟨t, t_h⟩ s q
  let x_of_P := P.val.1
  x = x_of_P := by
    intro t t_h x x_of_P
    let Y' := Y' s_h2 q_h1 q_h3 P
    let c := c s
    let X := X2 s P q
    let Y'_ne_zero := Y'_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one
    change x_of_P ≠ 0 at x_ne_zero
    have h1 : Y' = (c - 1) * s * X * (1 + X) / x_of_P := by grind [Y', Elligator1.Y']
    have h2 : x_of_P = (c - 1) * s * X * (1 + X) / Y' := by
      unfold Y' Elligator1.Y'
      rw [← div_left_inj' x_ne_zero, ← mul_left_inj' Y'_ne_zero]
      change x_of_P / x_of_P * Y' = (c - 1) * s * X * (1 + X) / Y' / x_of_P * Y'
      grind
    rw [h2]
    let h3 := Y'_eq_Y s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    let h4 := X'_eq_X s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
    unfold Y' X
    rw [h3, h4]
    change x = x
    rfl

lemma x_y_of_P_eq_x_y
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (P_props : ϕOverFProps s P)
  (x_ne_zero : P.val.1 ≠ 0)
  (y_ne_one : P.val.2 ≠ 1)
  (X_h :
    let X' := X2 s P q
    X' ≠ 1)
  :
  let t := t' s_h2 q_h1 q_h3 P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_X2_ne_one
    s_h1 s_h2 q_h1 q_h2 q_h3 P P_props x_ne_zero y_ne_one X_h
  let y := y ⟨t, t_h⟩ s
  let y_of_P := P.val.2
  let x := x ⟨t, t_h⟩ s q
  let x_of_P := P.val.1
  (x, y) = (x_of_P, y_of_P) := by grind [x_eq_x_of_P, y_eq_y_of_P]

end Elligator.Elligator1
