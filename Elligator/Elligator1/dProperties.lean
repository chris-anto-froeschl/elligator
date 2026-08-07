/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.cProperties

/-!
# d Variable Properties

In this file we introduce some generally helpful lemmas for `d` as introduced
in `Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

@[blueprint "lemma:d_nonsquare"
  (title := "$d$ is not a square")
  (statement := /--
  In the situation of Theorem 1, $d = -(c + 1)^2/(c - 1)^2$ is not a square in $\mathbb{F}_q$:
  otherwise $-1 = d(c - 1)^2/(c + 1)^2$ would be a square, a contradiction.
  -/)]
lemma d_nonsquare
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : ¬IsSquare (d s) := by
    rw [isSquare_iff_exists_mul_self (d s)]
    change ¬∃ r, (-((2 / s^2) + 1)^2 / ((2 / s^2) - 1)^2) = r * r
    rintro ⟨w, Pw⟩
    have h1 : (2 / s^2 - 1)^2 ≠ 0 := by grind
    have h2 : (2 / s^2 + 1)^2 ≠ 0 := by grind
    have h3 : w^2 * ((2 / s^2) - 1)^2 / ((2 / s^2) + 1)^2 = -1 := by grind
    have h4 : IsSquare (-1 : F) := by
      rw [← h3]
      have h5 : IsSquare (w^2) := by
        rw [pow_two]
        apply IsSquare.mul_self w
      have h6 : IsSquare (((2 / s^2) - 1)^2 / ((2 / s^2) + 1)^2) := by
        apply IsSquare.div
        · rw [pow_two]
          apply IsSquare.mul_self (2 / s^2 - 1)
        · rw [pow_two]
          apply IsSquare.mul_self (2 / s^2 + 1)
      rw [mul_div_assoc]
      apply IsSquare.mul h5 h6
    have h7 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h4
      rw [hq_card] at h4
      exact h4
    contradiction

lemma d_ne_zero
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (d s) ≠ 0 := by
    let d_nonsquare := d_nonsquare sq_ne_pm_two hq_card hq_mod
    intro h
    have h' : IsSquare (d s) := by
      unfold IsSquare
      use 0
      grind
    contradiction

lemma one_div_d_nonsquare
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : ¬IsSquare (1 / (d s)) := by
      intro h
      unfold IsSquare at h
      let d_nonsquare := d_nonsquare sq_ne_pm_two hq_card hq_mod
      let d_ne_zero := d_ne_zero sq_ne_pm_two hq_card hq_mod
      rcases h with ⟨a, ah⟩
      rw [← pow_two, ← mul_left_inj' d_ne_zero] at ah
      ring_nf at ah
      rw [mul_inv_cancel₀ d_ne_zero] at ah
      change 1 = (d s) * a^2 at ah
      by_cases h' : a = 0
      · grind
      · have h'' : a^2 ≠ 0 := by grind
        rw [← div_left_inj' h'', mul_div_assoc, div_self h'', mul_one] at ah
        rw [← one_pow 2, ← div_pow] at ah
        have d_square : IsSquare (d s) := by
          use 1 / a
          grind
        contradiction

lemma d_ne_one
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : (d s) ≠ 1 := by grind [d_nonsquare]

lemma d_ne_zero_and_d_ne_one
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (d s) ≠ 0 ∧ (d s) ≠ 1 := by
    constructor
    · exact d_ne_zero sq_ne_pm_two hq_card hq_mod
    · exact d_ne_one sq_ne_pm_two hq_card hq_mod

lemma neg_d_eq_r_add_two_div_r_sub_two
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let r := r s;
  let d := d s;
  -d = (r + 2) / (r - 2) := by
    intro r d
    let c := c s
    calc
      -d = (c + 2 + 1 / c) / (c - 2 + 1 / c) := by
        change -(-(c + 1)^2 / (c - 1)^2) = (c + 2 + 1 / c) / (c - 2 + 1 / c)
        rw [← neg_one_mul]
        nth_rw 2 [← neg_one_mul]
        rw [mul_div_assoc, ← mul_assoc]
        rw [add_pow_two, sub_pow_two]
        have h : 1 / c ≠ 0 := by
          rw [← inv_eq_one_div]
          apply inv_ne_zero
          apply c_ne_zero hs_ne_zero hq_card hq_mod
        grind
      _ = (r + 2) / (r - 2) := by
        rw [add_assoc, add_comm 2 (1 / c), ← add_assoc]
        nth_rw 3 [add_comm]
        rw [← add_sub_assoc]
        nth_rw 3 [add_comm]
        rfl

end Elligator.Elligator1
