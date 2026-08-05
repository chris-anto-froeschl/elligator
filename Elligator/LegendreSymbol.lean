/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.FiniteFieldBasic

/-!
# Legendre Symbol

In this file we introduce some a special case of the traditional Legendre Symbol.

This definition differs from the normal textbook definition, and therefore of mathlib's existing
`Mathlib.NumberTheory.LegendreSymbol.Basic` or `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`
by being bound to a finite field with `q` fulfilling `IsPrimePow`, `Fintype.card F = q` and
`q % 4 = 3`.

## References

See [bernstein2013a], Section 3.2 for the original account on this version of the Legendre Symbol.
-/

@[expose] public section

namespace Elligator.LegendreSymbol

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

/-- χ(a) is the quadratic character of a in the finite field F with q elements, where q is a
prime congruent to 3 modulo 4.

This function was added, since Mathlib.NumberTheory.LegendreSymbol.Basic is restricted to ℤ.

Original: definition at, Section 3.2.
-/
@[blueprint "def:χ"
  (title := "The quadratic character $\\chi$")
  (statement := /--
  Fix a prime power $q \equiv 3 \pmod 4$. Define $\chi : \mathbb{F}_q \to \mathbb{F}_q$ by
  $$
  \chi(a) = a^{(q-1)/2} .
  $$
  If $a$ is a nonzero square then $\chi(a) = 1$; if $a$ is a non-square then $\chi(a) = -1$;
  if $a = 0$ then $\chi(a) = 0$.
  -/)]
noncomputable def χ (a : F) : F := a^((Fintype.card F - 1) / 2)

@[simp]
lemma χ_a_zero_eq_zero
  {a : F}
  (a_eq_zero : a = 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : χ a = 0 := by
    unfold χ
    rw [hq_card, a_eq_zero]
    apply zero_pow (q_sub_one_div_two_ne_zero hq_card hq_primePow hq_mod)

lemma χ_a_ne_zero
  {a : F}
  (a_ne_zero : a ≠ 0)
  (hq_card : Fintype.card F = q)
  : χ a ≠ 0 := by
    unfold χ
    rw [hq_card]
    apply pow_ne_zero ((q - 1) / 2) at a_ne_zero
    exact a_ne_zero

lemma neg_χ_a_ne_χ_a
  {a : F}
  (a_ne_zero : a ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ a ≠ -(χ a) := by
    unfold χ
    rw [hq_card]
    intro h
    rw [← add_right_inj (a ^ ((q - 1) / 2))] at h
    ring_nf at h
    have h1 : a ^ ((q - 1) / 2) * 2 ≠ 0 := by
      simp_all
      grind [FiniteFieldBasic.two_ne_zero]
    contradiction

@[simp]
lemma χ_a_eq_one
  {a : F}
  (a_ne_zero : a ≠ 0)
  (a_square : IsSquare a)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ a = 1 := by
    unfold χ
    have h1 : ∃ r, a = r * r := by apply IsSquare.exists_mul_self a a_square
    rcases h1 with ⟨r, r_h⟩
    rw [r_h, ← pow_two]
    ring_nf
    have h2 : (Fintype.card F - 1) / 2 * 2 = Fintype.card F - 1 := by
      rw [hq_card]
      apply Nat.div_two_mul_two_of_even (q_sub_one_even hq_mod)
    rw [h2]
    have h3 : r ≠ 0 := by grind
    apply FiniteField.pow_card_sub_one_eq_one r h3

lemma a_IsSquare
  {a : F}
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (χ_a_eq_one : χ a = 1)
  : IsSquare a := by
    let χ_of_a := χ a
    unfold χ at χ_a_eq_one
    unfold IsSquare
    let b := a^((Fintype.card F + 1) / 4 )
    use b
    unfold b
    rw [← pow_two, ← pow_mul, add_comm, hq_card]
    rw [one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
    have h : (1 + Fintype.card F) / 2 = (Fintype.card F - 1 + 2) / 2 := by omega
    simp_all
    grind

lemma χ_a_eq_one_iff_a_square
  {a : F}
  (a_ne_zero : a ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ a = 1 ↔ IsSquare a := by
    constructor
    · intro χ_a_eq_one
      exact a_IsSquare hq_card hq_mod χ_a_eq_one
    · intro a_square
      exact χ_a_eq_one a_ne_zero a_square hq_card hq_mod

lemma a_pow_q_add_one_div_two_eq_χ_of_a_mul_a
  {a : F}
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : a^((q + 1) / 2) = (χ a) * a := by
    unfold χ
    have h : (q - 1) / 2 = (q + 1) / 2 - 1 := by omega
    rw [hq_card, h]
    nth_rw 3 [← pow_one a]
    rw [← pow_add]
    have h'' : (q + 1) / 2 - 1 + 1 = (q + 1) / 2 := by omega
    rw [h'']

lemma χ_a_mul_a_eq_a
  {a : F}
  (a_ne_zero : a ≠ 0)
  (a_square : IsSquare a)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (χ a) * a = a := by simp_all

@[simp]
lemma a_pow_q_add_one_div_two_eq_a
  {a : F}
  (a_square : IsSquare a)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : a^((q + 1) / 2) = a := by
    by_cases h : a = 0
    · rw [h, add_comm, zero_pow,]
      exact q_add_one_div_two_ne_zero hq_mod
    · rw [a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_card hq_mod]
      rw [χ_a_mul_a_eq_a h a_square hq_card hq_mod]

@[simp]
lemma χ_of_a_pow_two_eq_one
  {a : F}
  (a_ne_zero : a ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ (a^2) = 1 := by
    unfold χ
    rw [← pow_mul, mul_comm]
    rw [hq_card, Nat.div_mul_cancel (even_iff_two_dvd.mp
        (q_sub_one_even hq_mod))]
    rw [← hq_card, FiniteField.pow_card_sub_one_eq_one a a_ne_zero]

lemma χ_of_a_eq_neg_one
  {a : F}
  (a_ne_zero : a ≠ 0)
  (a_nonsquare : ¬IsSquare a)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ a = -1 := by
    -- Euler's criterion
    have h : (a^((Fintype.card F - 1) / 2))^2 = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel (by omega)]
      exact FiniteField.pow_card_sub_one_eq_one a a_ne_zero
    rw [sq_eq_one_iff] at h
    unfold χ
    rcases h with h' | h'
    · contrapose a_nonsquare
      unfold IsSquare
      have h' : (q + 1) / 4 * 2 = (q - 1) / 2 + 1 := by grind
      have h_square : ∃ b : F, a = b^2 := by
        use a^((Fintype.card F + 1) / 4)
        rw [← pow_mul, hq_card, h']
        grind
      obtain ⟨b, b_h⟩ := h_square
      use b
      rw [← pow_two]
      exact b_h
    · exact h'

lemma χ_of_neg_one_eq_neg_one
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ (-1 : F) = -1 := by
    let h1 := @FiniteFieldBasic.neg_one_ne_zero F _
    let h2 := neg_one_non_square hq_card hq_mod
    apply χ_of_a_eq_neg_one h1 h2 hq_card hq_mod

lemma χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b {a b : F} : χ (a * b) = (χ a) * χ b := by
  unfold χ
  rw [mul_pow]

@[simp]
lemma χ_of_a_even_pow_n_eq_one
  {a : F}
  (a_ne_zero : a ≠ 0)
  (n : {n : ℕ | Even n})
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ a^(n.val) = 1 := by
    have n_even := n.prop
    unfold Even at n_even
    rcases n_even with ⟨k, kh⟩
    rw [← mul_two] at kh
    rw [kh, mul_comm, pow_mul, pow_two]
    rw [← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, ← pow_two]
    rw [χ_of_a_pow_two_eq_one a_ne_zero hq_card hq_mod]
    rw [one_pow]

@[simp]
lemma χ_of_a_pow_n_eq_χ_a
  (a : F)
  (n : {n : ℕ | Odd n})
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : (χ a)^(n.val) = χ a := by
    obtain ⟨k, hk⟩ := n.2
    rw [hk, pow_add]
    have h : Even (2 * k) := by simp only [even_two, Even.mul_right]
    by_cases h_a : a = 0
    · simp_all
    · rw [χ_of_a_even_pow_n_eq_one h_a ⟨2 * k, h⟩  hq_card hq_mod]
      simp

lemma χ_values
  {a : F}
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : χ a = 0 ∨ χ a = -1 ∨ χ a = 1 := by
    by_cases h : a = 0
    · left
      exact χ_a_zero_eq_zero h hq_card hq_primePow hq_mod
    · rw [← ne_eq] at h
      by_cases h' : IsSquare a
      · right
        right
        apply χ_a_eq_one h h' hq_card hq_mod
      · right
        left
        apply χ_of_a_eq_neg_one h h' hq_card hq_mod

lemma χ_of_χ_of_a_eq_χ_of_a
  {a : F}
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : χ (χ a) = χ a := by
    let h : χ a = 0 ∨ χ a = -1 ∨ χ a = 1 :=
      by exact χ_values hq_card hq_primePow hq_mod
    rcases h with h' | h' | h'
    · simp_all
    · rw [h']
      unfold χ
      rw [hq_card]
      apply Odd.neg_one_pow (q_sub_one_div_two_odd hq_mod)
    · rw [h']
      unfold χ
      rw [one_pow]

lemma χ_of_one_div_a_eq_χ_a
  {a : F}
  (a_ne_zero : a ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ a = χ (1 / a) := by
    unfold χ;
    rw [div_pow, one_pow, hq_card]
    have h : a ^ ((q - 1) / 2) ≠ 0 := by simp_all
    rw [← mul_left_inj' h]
    rw [← pow_add]
    have h' : (q - 1) / 2 + (q - 1) / 2 = q - 1 := by grind
    rw [h']
    rw [← hq_card]
    rw [FiniteField.pow_card_sub_one_eq_one a a_ne_zero]
    simp_all

lemma one_div_χ_of_a_eq_χ_a
  {a : F}
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : χ a = 1 / χ a := by
      -- If a is zero, then χ(a) is zero by definition, so 1/χ(a) is also zero.
    by_cases ha : a = 0
    · simp_all
    · have h : χ a ≠ 0 := by exact χ_a_ne_zero ha hq_card
      rw [← mul_left_inj' h]
      unfold χ
      rw [← mul_pow, ← pow_two]
      change χ (a ^ 2) = 1 / a ^ ((Fintype.card F - 1) / 2) * a ^ ((Fintype.card F - 1) / 2)
      rw [χ_a_eq_one (by simp_all) (by aesop) hq_card hq_mod]
      simp_all

-- Introduced in paper theory theorem 3.A proof
lemma χ_of_a_eq_χ_a_mul_b_pow_two {a : F} {b : F}
  (b_ne_zero : b ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : χ (a * b^2) = χ a := by
    -- By definition of χ, we know that χ(a * b^2) = (a * b^2)^((q - 1) / 2).
    unfold χ
    rw [mul_pow]
    have h : b^2 ≠ 0 := by simp_all
    change a ^ ((Fintype.card F - 1) / 2) * χ (b ^ 2) = a ^ ((Fintype.card F - 1) / 2)
    rw [χ_a_eq_one h (by aesop) hq_card hq_mod]
    rw [mul_one]

lemma b_eq_χ_of_b_mul_principal_sqrt_a
  {a : F}
  (a_square : IsSquare a)
  {b : F}
  (b_h1 : b ^ 2 = a)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : (χ b) * a^((q + 1) / 4) = b := by
    have h : χ b = b ^ ((q - 1) / 2) := by aesop
    -- Substitute $a$ with $b^2$ in the right-hand side of the equation.
    have h' : b ^ ((q - 1) / 2) * (b ^ 2) ^ ((q + 1) / 4) = b := by
      rw [← pow_mul, ← pow_add]
      have h'' : ( q - 1 ) / 2 + 2 * ( ( q + 1 ) / 4 ) = q := by omega
      rw [h'', ← hq_card, FiniteField.pow_card]
    simp_all +decide

lemma b_pow_q_add_one_div_four_eq_χ_of_a_mul_a
  {a : F}
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (a^2)^((q + 1) / 4) = (χ a) * a := by
    rw [← pow_mul, mul_comm, add_comm]
    rw [one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
    rw [← a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_card hq_mod]
    rw [← hq_card, add_comm]

lemma χ_a_mul_a_IsSquare
  {a : F}
  (a_ne_zero : a ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_primePow : IsPrimePow q)
  (hq_mod : q % 4 = 3)
  : IsSquare ((χ a) * a) := by
    have h : (χ a) * a ≠ 0 := by
      apply mul_ne_zero
      · exact χ_a_ne_zero a_ne_zero hq_card
      · exact a_ne_zero
    apply (χ_a_eq_one_iff_a_square h hq_card hq_mod).mp
    rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
    rw [χ_of_χ_of_a_eq_χ_of_a hq_card hq_primePow hq_mod]
    rw [← pow_two]
    rw [χ_of_a_even_pow_n_eq_one a_ne_zero ⟨2, even_two⟩ hq_card hq_mod]

lemma a_eq_zero_of_χ_of_a_eq_zero {a : F} :
  χ a = 0 → a = 0 := by
    intro h
    unfold χ at h
    apply eq_zero_of_pow_eq_zero at h
    exact h

end Elligator.LegendreSymbol
