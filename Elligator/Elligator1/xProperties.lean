/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.sProperties
public import Elligator.Elligator1.cProperties
public import Elligator.Elligator1.EdwardsCurve
public import Elligator.Elligator1.uProperties
public import Elligator.Elligator1.vProperties
public import Elligator.Elligator1.XProperties
public import Elligator.Elligator1.YProperties

/-!
# x Variable Properties

In this file we introduce some generally helpful lemmas for `x` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

@[blueprint "lemma:x_ne_zero"
  (title := "$x \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $x = (c - 1)sX(1 + X)/Y \neq 0$, since $c \neq 1$, $s \neq 0$,
  $X \neq 0$ and $1 + X \neq 0$.
  -/)]
lemma x_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let x := x t s q
  x ≠ (0 : F) := by
    let c := c s
    let X := X t s
    let Y := Y t s q
    change (c - 1) * s * X * (1 + X) / Y ≠ 0
    apply div_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · intro h1
            have h1_1 : c = 1 := by grind
            have h1_2 := c_ne_one s_h2
            contradiction
          · apply s_h1
        · apply X_ne_zero s_h1 q_h1 q_h3 t
      · apply one_add_X_ne_zero s_h1 q_h1 q_h2 q_h3 t
    · apply Y_ne_zero s_h1 q_h1 q_h3 t

lemma x_comparison
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let x1 := x t s q
  let x2 := x ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s q
  x2 = x1 := by
    intro t1 t2 x1 x2
    let c := c s
    let r := r s
    let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let X1 := X t s
    let X2 := X ⟨t2, t_h⟩ s
    let Y1 := Y t s q
    let Y2 := Y ⟨t2, t_h⟩ s q
    have X_pow_three_ne_zero : X1^3 ≠ 0 := pow_ne_zero 3 (X_ne_zero s_h1 q_h1 q_h3 t)
    calc
      x2 = (c - 1) * s * X2 * (1 + X2) / Y2 := by rfl
      _ = (c - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1^3) := by grind [X_comparison, Y_comparison]
      _ = (c - 1) * s * X1 * (1 + X1) / Y1 := by simp_all; grind
      _ = x1 := by rfl

lemma x_y_eq_zero_sign_one
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  (point : {p : F × F // p ∈ EOverF s_h2 q_h1 q_h3})
  (x_eq_zero : point.val.1 = 0)
  : point.val = ((0 : F), (1 : F)) ∨ point.val = ((0 : F), (-1 : F)) := by
    let d := d s
    let x := point.val.1
    let y := point.val.2
    unfold EOverF at point
    change (x, y) = (0, 1) ∨ (x, y) = (0, -1)
    change x = 0 at x_eq_zero
    rw [← x_eq_zero]
    have h' : x^2 + y^2 = 1 + d * x^2 * y^2 := by
      let point_h := point.prop
      simp only [edwardsCurveEquation_iff] at point_h
      exact point_h
    have h'' : y = 1 ∨ y = -1 := by grind
    rcases h'' with h | h
    · rw [← h]
      left
      rfl
    · rw [← h]
      right
      rfl

end Elligator.Elligator1
