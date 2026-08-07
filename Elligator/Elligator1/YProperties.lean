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
public import Elligator.Elligator1.XProperties

/-!
# Y Variable Properties

In this file we introduce some generally helpful lemmas for `Y` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

omit [DecidableEq F] in
lemma Y_ne_zero
  [DecidableEq F]
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let Y := Y t s q
  Y ≠ 0 := by
    let u := u t
    let v := v t s
    let χ_of_sum := χ (u^2 + 1 / (c s)^2)
    intro Y
    change ((χ v) * v)^((q + 1) / 4) * (χ v) * χ_of_sum ≠ 0
    let v_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
    apply mul_ne_zero
    · apply mul_ne_zero
      · rw [mul_pow (χ v) v ((q + 1) / 4)]
        apply mul_ne_zero
        · apply pow_ne_zero (((q + 1) / 4) : ℕ)
          apply χ_a_ne_zero v_ne_zero
        · apply pow_ne_zero (((q + 1) / 4) : ℕ)
          apply v_ne_zero
      · apply χ_a_ne_zero v_ne_zero
    · apply χ_a_ne_zero (v_h1_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)

omit [DecidableEq F] in
@[blueprint "lemma:X_mul_Y_ne_zero"
  (title := "$XY \\neq 0$, so $x$ is defined")
  (statement := /--
  In the situation of Theorem 1, $XY \neq 0$; in particular $Y \neq 0$, so
  $x = (c - 1)sX(1 + X)/Y$ is defined.
  -/)]
lemma X_mul_Y_ne_zero
  [DecidableEq F]
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X := X t s
  let Y := Y t s q
  X * Y ≠ 0 := by
    open Classical in
    apply mul_ne_zero
    · apply X_ne_zero hs_ne_zero hq_card hq_mod t
    · apply Y_ne_zero hs_ne_zero hq_card hq_mod t

omit [DecidableEq F] in
@[blueprint "lemma:one_add_X_ne_zero"
  (title := "$1 + X \\neq 0$, so $x \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $1 + X \neq 0$: if $X = -1$ then $u = -\chi(v)$, so
  $v = -\chi(v)r^2$ and hence $\chi(v) = -\chi(v)$, a contradiction.
  -/)]
lemma one_add_X_ne_zero
  [DecidableEq F]
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X := X t s
  (1 + X) ≠ (0 : F) := by
    let u := u t
    let v := v t s
    let r := r s
    let v_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
    intro X
    change 1 + (χ v) * u ≠ 0
    intro h
    have h1 : (χ v) * u = -1 := by grind
    have h2 : u = -(χ v) := by grind [one_div_χ_of_a_eq_χ_a]
    have h3 : v = -(χ v) * (1 + r^2 - 2 + 1) := by
      change u^5 + (r^2 - 2) * u^3 + u = -(χ v) * (1 + r^2 - 2 + 1)
      repeat rw [h2]
      rw [← neg_one_mul, mul_pow, mul_pow]
      grind [χ_of_a_pow_n_eq_χ_a]
    have h4 : v = -(χ v) * r^2 := by grind
    have h5 : (χ v) = -(χ v) := by
      rw [h2] at h1
      change (χ v) * -(χ v) = -1 at h1
      nth_rw 1 [h4] at h1
      rw [χ_mul] at h1
      nth_rw 1 [← neg_one_mul] at h1
      rw [χ_mul, χ_neg_one hq_card hq_mod] at h1
      rw [χ_χ_eq_χ hq_card hq_mod] at h1
      have h5_1 : r^2 ≠ 0 := pow_ne_zero 2 (r_ne_zero hs_ne_zero hq_card hq_mod)
      have h5_2 : IsSquare (r^2) := IsSquare.sq r
      grind [χ_a_eq_one]
    have h6 : (χ v) ≠ -(χ v) := neg_χ_a_ne_χ_a v_ne_zero hq_card hq_mod
    contradiction

omit [DecidableEq F] in
lemma Y_comparison
  [DecidableEq F]
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let X1 := X t s
  let Y1 := Y t s q
  let Y2 := Y ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s q
  Y2 = Y1 / X1^3 := by
    intro t1 t2 X1 Y1 Y2
    let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let c := c s
    let r := r s
    let u1 := u t
    let u2 := u ⟨t2, t_h⟩
    let v1 := v t s
    let v2 := v ⟨t2, t_h⟩ s
    let x1 := x t s q
    let x2 := x ⟨t2, t_h⟩ s q
    let y1 := y t s
    let y2 := y ⟨t2, t_h⟩ s
    let χ_of_u1 := χ u1
    let χ_of_u2 := χ u2
    let χ_of_v1 := χ v1
    let χ_of_v2 := χ v2
    let χ_of_u1_mul_v1  := χ (u1 * v1)
    let u_ne_zero := @u_ne_zero F _ t
    have first_factor :
      (χ_of_v2 * v2)^((q + 1) / 4) = (χ_of_v1 * v1)^((q + 1) / 4) * χ_of_u1 / u1^3 := by
        have h1_1 : χ_of_v2 * v2 = χ_of_v1 * v1 / u1^6 := by
          unfold χ_of_v2
          rw [v_comparison_implication4 t]
          unfold v2
          rw [v_comparison_implication2 t]
          change χ_of_v1 * (v1 / u1^6) = χ_of_v1 * v1 / u1 ^ 6
          rw [← mul_div_assoc]
        have h1_2 : IsSquare (χ_of_u1 * u1^3) := by
          have h1_2_1 : χ_of_u1 * u1^3 ≠ 0 := by
            apply mul_ne_zero
            · apply χ_a_ne_zero u_ne_zero
            · apply pow_ne_zero 3 u_ne_zero
          apply (χ_eq_one_iff_isSquare h1_2_1 hq_card hq_mod).mp
          have h : (3 : ℕ) = 1 + 2 := by norm_num
          rw [h, pow_add u1 1 2, ← mul_assoc, pow_one]
          rw [χ_mul, χ_mul]
          rw [χ_χ_eq_χ hq_card hq_mod]
          rw [← χ_mul, ← pow_two]
          have h' : IsSquare (u1^2) := IsSquare.sq u1
          have h'' : χ (u1 ^ 2) = 1 := by
            apply (χ_eq_one_iff_isSquare (pow_ne_zero 2 u_ne_zero) hq_card hq_mod).mpr
            exact h'
          simp [h'']
        have h''' : (u1^6)^((q + 1) / 4) = χ_of_u1 * u1^3  := by
          have h'''' : 6 = 3 * 2 := by norm_num
          rw [h'''', ← pow_mul, mul_assoc, mul_comm, pow_mul, mul_comm]
          rw [add_comm, one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
          rw [add_comm, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_card hq_mod]
          change (χ_of_u1 * u1)^3 = χ_of_u1 * u1^3
          rw [mul_pow, χ_of_a_pow_n_eq_χ_a u1 ⟨3, by trivial⟩]
        calc
          (χ_of_v2 * v2)^((q + 1) / 4) = (χ_of_v1 * v1 / u1^6)^((q + 1) / 4) := by rw [h1_1]
          _ = (χ_of_v1 * v1)^((q + 1) / 4) * χ_of_u1 / u1^3:= by
            rw [div_pow, h''']
            unfold χ_of_u1
            nth_rw 2 [one_div_χ_of_a_eq_χ_a]
            ring_nf
    have second_factor : χ_of_v2 = χ_of_v1 := v_comparison_implication4 t
    have third_factor : χ (u2^2 + 1 / c^2) = χ (u1 * v1 * (u1^2 + 1 / c^2)) := by
      calc
        χ (u2^2 + 1 / c^2)
          = χ ((c^2 * u1^4 * (u2^2 + 1 / c^2)) * (u1^2 + 1 / c^2)^2) := by
          rw [← χ_of_a_eq_χ_a_mul_b_pow_two (c_ne_zero hs_ne_zero hq_card hq_mod)]
          rw [mul_comm, ← χ_of_a_eq_χ_a_mul_b_pow_two (pow_ne_zero 2 u_ne_zero)]
          rw [χ_of_a_eq_χ_a_mul_b_pow_two (v_h1_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)]
          grind
        _ = χ ((u1^2 * (c^2 + u1^2)) * (u1^2 + 1 / c^2)^2) := by
          rw [pow_two u2]
          unfold u2
          rw [u_comparison t]
          change χ (c^2 * u1^4 * (1 / u1 * (1 / u1) + 1 / c^2) * (u1^2 + 1 / c^2)^2)
            = χ (u1^2 * (c^2 + u1^2) * (u1^2 + 1 / c^2)^2)
          have h1 : c^2 * u1^4 * (1 / u1 * (1 / u1) + 1 / c^2) = u1^2 * (c^2 + u1^2) := by
            have h1_1 : c^2 ≠ 0 := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)
            grind
          rw [h1]
        _ = χ (u1 * v1 * (u1^2 + 1 / c^2)) := by grind [v_h1]
    calc
      Y2 = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1^3 := by
        unfold Y2 Y
        change (χ_of_v2 * v2)^((q + 1) / 4) * χ_of_v2 * χ (u2^2 + 1 / c^2)
          = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1^3
        rw [first_factor, second_factor, third_factor, χ_mul]
        change
          (χ_of_v1 * v1)^((q + 1) / 4) * χ_of_u1 / u1^3 * χ_of_v1
          * (χ_of_u1_mul_v1 * (χ (u1 ^ 2 + 1 / c^2)))
            = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3
        have h1 : (χ_of_v1 * v1)^((q + 1) / 4) * χ_of_u1 / u1^3 * χ_of_v1
          * (χ_of_u1_mul_v1 * (χ (u1^2 + 1 / c^2)))
          = (χ_of_v1 * v1) ^ ((q + 1) / 4) * χ_of_v1 * (χ (u1^2 + 1 / c^2))
            * χ_of_u1 * χ_of_u1_mul_v1 / u1^3 := by ring_nf
        rw [h1]
        change Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1^3 = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1^3
        rfl
      _ = Y1 / (χ_of_v1 * u1)^3 := by
        unfold χ_of_u1_mul_v1 χ_of_u1
        rw [χ_mul, ← mul_assoc, mul_assoc Y1 (χ u1) (χ u1)]
        rw [← χ_mul, ← pow_two]
        rw [χ_sq u_ne_zero]
        rw [one_div_χ_of_a_eq_χ_a]
        let v_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
        rw [← χ_of_a_pow_n_eq_χ_a v1 ⟨3, by trivial⟩]
        change Y1 * 1 * (1 / χ_of_v1^3) / u1^3 = Y1 / (χ_of_v1 * u1)^3
        grind
      _ = Y1 / X1^3 := by rfl

end Elligator.Elligator1
