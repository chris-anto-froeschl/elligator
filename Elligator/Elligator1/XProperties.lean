/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.sProperties
public import Elligator.Elligator1.cProperties
public import Elligator.Elligator1.uProperties
public import Elligator.Elligator1.vProperties

/-!
# X Variable Properties

In this file we introduce some generally helpful lemmas for `X` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma X_pow_two_add_one_div_c_pow_two_ne_zero
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : (X t s)^2 + 1 / (c s)^2 ≠ 0 := by
    let X := X t s
    let c := c s
    intro h
    have h' : X^2 * c^2 + c⁻¹^2 * c^2 = 0 := by grind
    have h'' : X^2 * c^2 = -1 := by grind [c_ne_zero]
    have h''' : ¬IsSquare (-1 : F) := neg_one_non_square hq_card hq_mod
    have h'''' : IsSquare (-1 : F) := by
      rw [← h'', ← mul_pow]
      apply IsSquare.sq (X * c)
    contradiction

@[blueprint "lemma:X_ne_zero"
  (title := "$X \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $X = \chi(v)u \neq 0$, since $u \neq 0$ and
  $\chi(v) \neq 0$.
  -/)]
lemma X_ne_zero
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : (X t s) ≠ 0 := by
    apply mul_ne_zero
    · apply χ_a_ne_zero (v_ne_zero hs_ne_zero hq_card hq_mod t) hq_card
    · apply u_ne_zero t

lemma X_comparison
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let X1 := X t s
  let X2 := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  X2 = 1 / X1 := by
    intro t1 t2 X1 X2
    let u1 := u t
    let u2 := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
    let v1 := v t s
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let χ_of_v1 := LegendreSymbol.χ v1
    let χ_of_v2 := LegendreSymbol.χ v2
    calc
      X2 = χ_of_v2 * u2 := by rfl
      _ = χ_of_v1 / u1 := by
        unfold χ_of_v2 v2 t2
        rw [v_comparison_implication4 t hq_card hq_mod]
        unfold u2
        rw [u_comparison t]
        change χ_of_v1 * (1 / u1) = χ_of_v1 / u1
        ring_nf
      _ = 1 / (χ_of_v1 * u1) := by
        unfold χ_of_v1
        nth_rw 1 [LegendreSymbol.one_div_χ_of_a_eq_χ_a hq_card hq_primePow hq_mod]
        ring_nf
      _ = 1 / X1 := by rfl

lemma X_of_zero
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let X_of_zero := X ⟨(0 : F), zero_h1⟩ s
  X_of_zero = 1 := by
    intro X_of_zero
    unfold X_of_zero X
    let χ_of_v := LegendreSymbol.χ (v ⟨(0 : F), zero_h1⟩ s)
    rw [u_of_zero]
    change χ_of_v * 1 = 1
    unfold χ_of_v
    rw [v_of_zero]
    rw [χ_of_a_pow_two_eq_one (r_ne_zero hs_ne_zero hq_card hq_mod) hq_card hq_mod]
    simp

end Elligator.Elligator1
