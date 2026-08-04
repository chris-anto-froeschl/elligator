/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.cProperties

/-!
# r Variable Properties

In this file we introduce some generally helpful lemmas for `r` as introduced
in `Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

@[blueprint "lemma:r_ne_zero"
  (title := "$r \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $r = c + 1/c \neq 0$: if $r = 0$ then $c = -1/c$, so
  $c^2 = -1$, a contradiction since $-1$ is not a square in $\mathbb{F}_q$.
  -/)]
lemma r_ne_zero
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : (r s) ≠ 0 := by
    intro h
    let c := c s
    change c + 1 / c = 0 at h
    have h1 : c = (-1 : F) / c := by grind
    have h2 : c^2 = -1 := by
      calc
        c^2 = -1 / c * c := by grind
        _ = -1 := by
          nth_rw 1 [← neg_one_mul 1]
          ring_nf
          rw [mul_inv_cancel₀ (c_ne_zero s_h1 q_h1 q_h3)]
    have h3 : IsSquare (-1 : F) := by
      rw [← h2, pow_two]
      apply IsSquare.mul_self c
    have h4 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff, q_h1] at h3
      exact h3
    contradiction

lemma four_add_r_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : 4 + (r s) ≠ 0 := by
    let c := c s
    change 4 + (c + 1 / c) ≠ 0
    intro h
    have hc : c ≠ 0 := c_ne_zero s_h1 q_h1 q_h3
    have h2 : (2 : F) ≠ 0 := FiniteFieldBasic.two_ne_zero q_h1 q_h3
    have h_quad : c ^ 2 + 4 * c + 1 = 0 := by grind
    have h_neg_sq : IsSquare (-1 : F) := by
      set a : F := s ^ 2 + 4
      have ha : a ^ 2 = 12 := by
        unfold c Elligator1.c at h_quad
        grind
      set u : F := a / 2
      have hu : u ^ 2 = 3 := by grind
      have h_neg_one : -1 = ((u - 1) / s) ^ 2 := by grind
      exact ⟨ _, h_neg_one.trans ( sq _ ) ⟩
    have h_not_sq : ¬ IsSquare (-1 : F) := by
      rw [FiniteField.isSquare_neg_one_iff, q_h1]
      omega
    exact h_not_sq h_neg_sq

lemma r_h1 (s_h1 : s ≠ 0) (q_h1 : Fintype.card F = q) (q_h2 : IsPrimePow q) (q_h3 : q % 4 = 3)
  :
  let r := r s
  let c := c s
  (r^2 - 2) = c^2 + 1 / c^2 := by
    intro r c
    calc
      r^2 - 2 = (c + 1 / c)^2 - 2 := by trivial
      _ = c^2 + 2 * (c * (1 / c)) + (1 / c)^2 - 2 := by grind
      _ = c^2 + 2 + 1 / c^2 - 2 := by
        ring_nf
        rw [mul_inv_cancel₀ (c_ne_zero s_h1 q_h1 q_h3)]
        ring_nf
      _ = c^2 + 1 / c^2 := by ring_nf

lemma r_sub_two_ne_zero
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : (r s) - 2 ≠ 0 := by
    let c := c s
    let c_ne_zero := c_ne_zero s_h1 q_h1 q_h3
    let c_ne_one := c_ne_one s_h2
    change (c + 1 / c) - 2 ≠ 0
    have h1 : (c + 1 / c) - 2 = (c - 1)^2 / c := by grind
    rw [h1]
    apply div_ne_zero (by grind) c_ne_zero

end Elligator.Elligator1
