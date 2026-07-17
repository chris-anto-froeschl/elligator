/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Elligator.FiniteFieldBasic

/-!
# Legendre Symbol

In this file we introduce some a special case of the traditional Legendre Symbol.
This definition differs from the normal textbook definition, and therefore of mathlib's existing
`Mathlib.NumberTheory.LegendreSymbol.Basic` or `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`
by being bound to a finite field with `q` fulfilling `IsPrimePow`, `Fintype.card F = q` and
`q % 4 = 3`.

## References

See [bernstein2013a] chapter 3.1 for the original account on this version of the Legendre Symbol.
-/

@[expose] public section

namespace LegendreSymbol

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

/-- χ(a) is the quadratic character of a in the finite field F with q elements, where q is a
prime congruent to 3 modulo 4.

This function was added, since Mathlib.NumberTheory.LegendreSymbol.Basic is restricted to ℤ.

Original: definition at chapter 3.1.
-/
@[blueprint "def:χ"]
noncomputable def χ (a : F) : F := a^((Fintype.card F - 1) / 2)

@[simp, blueprint "lemma:χ_a_zero_eq_zero"]
lemma χ_a_zero_eq_zero
  {a : F}
  (a_eq_zero : a = 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ a = 0 := by
    unfold χ
    rw [field_cardinality, a_eq_zero]
    apply zero_pow (FiniteFieldBasic.q_sub_one_over_two_ne_zero
      field_cardinality q_prime_power q_mod_4_congruent_3)

@[blueprint "lemma:χ_a_ne_zero"]
lemma χ_a_ne_zero
  {a : F}
  (a_nonzero : a ≠ 0)
  (field_cardinality : Fintype.card F = q)
  : χ a ≠ 0 := by
    unfold χ
    rw [field_cardinality]
    apply pow_ne_zero ((q - 1) / 2) at a_nonzero
    exact a_nonzero

@[blueprint "lemma:neg_χ_a_ne_χ_a"]
lemma neg_χ_a_ne_χ_a
  {a : F}
  (a_nonzero : a ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ a ≠ -(χ a) := by
    unfold χ
    rw [field_cardinality]
    intro h
    rw [← add_right_inj (a ^ ((q - 1) / 2))] at h
    ring_nf at h
    have h1 : a ^ ((q - 1) / 2) * 2 ≠ 0 := by
      simp_all
      grind [FiniteFieldBasic.two_ne_zero]
    contradiction

@[simp, blueprint "lemma:χ_a_eq_one"]
lemma χ_a_eq_one
  {a : F}
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ a = 1 := by
    unfold χ
    have h1 : ∃ r, a = r * r := by apply IsSquare.exists_mul_self a a_square
    rcases h1 with ⟨r, h1_1⟩
    rw [h1_1, ← pow_two]
    ring_nf
    have h2 : (Fintype.card F - 1) / 2 * 2 = Fintype.card F - 1 := by
      apply Nat.div_two_mul_two_of_even
        (FiniteFieldBasic.q_sub_one_even field_cardinality q_mod_4_congruent_3)
    rw [h2]
    have h3 : r ≠ 0 := by grind
    apply FiniteField.pow_card_sub_one_eq_one r h3

@[blueprint "lemma:a_IsSquare"]
lemma a_IsSquare
  {a : F}
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (χ_a_eq_one : χ a = 1)
  : IsSquare a := by
    let χ_of_a := χ a
    unfold χ at χ_a_eq_one
    unfold IsSquare
    let b := a^((Fintype.card F + 1) / 4 )
    use b
    unfold b
    rw [← pow_two, ← pow_mul, add_comm]
    rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two
      field_cardinality q_mod_4_congruent_3]
    have h : (1 + Fintype.card F) / 2 = (Fintype.card F - 1 + 2) / 2 := by omega
    simp_all
    grind

@[blueprint "lemma:χ_a_eq_one_iff_a_square"]
lemma χ_a_eq_one_iff_a_square
  {a : F}
  (a_nonzero : a ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ a = 1 ↔ IsSquare a := by
    constructor
    · intro χ_a_eq_one
      exact a_IsSquare field_cardinality q_mod_4_congruent_3 χ_a_eq_one
    · intro a_square
      exact χ_a_eq_one a_nonzero a_square field_cardinality q_mod_4_congruent_3

@[blueprint "lemma:a_pow_q_add_one_over_two_eq_χ_of_a_mul_a"]
lemma a_pow_q_add_one_over_two_eq_χ_of_a_mul_a
  {a : F}
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : a^((q + 1) / 2) = (χ a) * a := by
    unfold χ
    rw [field_cardinality]
    rw [FiniteFieldBasic.card_sub_one_over_four_mul_two_eq_one_add_card_over_two]
    nth_rw 3 [← pow_one a]
    rw [← pow_add]
    have h'' : (q + 1) / 2 - 1 + 1 = (q + 1) / 2 := by omega
    rw [h'']

@[simp, blueprint "lemma:χ_a_mul_a_eq_a"]
lemma χ_a_mul_a_eq_a
  {a : F}
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (χ a) * a = a := by simp_all

@[simp, blueprint "lemma:a_pow_q_add_one_over_two_eq_a"]
lemma a_pow_q_add_one_over_two_eq_a
  {a : F}
  (a_square : IsSquare a)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : a^((q + 1) / 2) = a := by
    by_cases h : a = 0
    · rw [h, add_comm, zero_pow,]
      exact FiniteFieldBasic.q_add_one_over_two_ne_zero q_mod_4_congruent_3
    · rw [a_pow_q_add_one_over_two_eq_χ_of_a_mul_a field_cardinality q_mod_4_congruent_3]
      rw [χ_a_mul_a_eq_a h a_square field_cardinality q_mod_4_congruent_3]

@[simp, blueprint "lemma:χ_of_a_pow_two_eq_one"]
lemma χ_of_a_pow_two_eq_one
  {a : F}
  (a_nonzero : a ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ (a^2) = 1 := by
    unfold χ
    rw [← pow_mul, mul_comm]
    rw [Nat.div_mul_cancel (even_iff_two_dvd.mp
        (FiniteFieldBasic.q_sub_one_even field_cardinality q_mod_4_congruent_3))]
    rw [FiniteField.pow_card_sub_one_eq_one a a_nonzero]

@[blueprint "lemma:χ_of_a_eq_neg_one"]
lemma χ_of_a_eq_neg_one
  {a : F}
  (a_nonzero : a ≠ 0)
  (a_nonsquare : ¬IsSquare a)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ a = -1 := by
    -- Euler's criterion
    -- TODO any standard lemma to reuse here?
    have h1 : (a^((Fintype.card F - 1) / 2))^2 = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel (by omega)]
      exact FiniteField.pow_card_sub_one_eq_one a a_nonzero
    rw [sq_eq_one_iff] at h1
    unfold χ
    rcases h1 with h2 | h2
    · contrapose a_nonsquare
      unfold IsSquare
      have h_square : ∃ b : F, a = b^2 := by
        use a^((Fintype.card F + 1) / 4)
        rw [← pow_mul, FiniteFieldBasic.q_h1 (by omega)]
        grind
      obtain ⟨b, b_h⟩ := h_square
      use b
      rw [← pow_two]
      exact b_h
    · exact h2

@[blueprint "lemma:χ_of_neg_one_eq_neg_one"]
lemma χ_of_neg_one_eq_neg_one
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ (-1 : F) = -1 := by
    let h1 := @FiniteFieldBasic.neg_one_ne_zero F _
    let h2 := FiniteFieldBasic.neg_one_non_square
      field_cardinality q_prime_power q_mod_4_congruent_3
    apply χ_of_a_eq_neg_one h1 h2 field_cardinality q_mod_4_congruent_3

@[blueprint "lemma:χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b"]
lemma χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b {a b : F} : χ (a * b) = (χ a) * χ b := by
  unfold χ
  rw [mul_pow]

@[blueprint "lemma:χ_of_a_even_pow_n_eq_one"]
lemma χ_of_a_even_pow_n_eq_one
  {a : F}
  (a_nonzero : a ≠ 0)
  (n : {n : ℕ | Even n})
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ a^(n.val) = 1 := by
    have n_even := n.prop
    unfold Even at n_even
    rcases n_even with ⟨k, kh⟩
    rw [← mul_two] at kh
    rw [kh, mul_comm, pow_mul, pow_two]
    rw [← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b, ← pow_two]
    rw [χ_of_a_pow_two_eq_one a_nonzero field_cardinality q_mod_4_congruent_3]
    rw [one_pow]

@[blueprint "lemma:χ_of_a_pow_n_eq_χ_a"]
lemma χ_of_a_pow_n_eq_χ_a
  (a : F)
  (n : {n : ℕ | Odd n})
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (χ a)^(n.val) = χ a := by
    obtain ⟨k, hk⟩ := n.2
    rw [hk, pow_add]
    have h : Even (2 * k) := by simp only [even_two, Even.mul_right]
    by_cases h_a : a = 0
    · simp_all
    · rw [χ_of_a_even_pow_n_eq_one h_a ⟨2 * k, h⟩  field_cardinality q_mod_4_congruent_3]
      simp

@[blueprint "lemma:χ_values"]
lemma χ_values
  {a : F}
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ a = 0 ∨ χ a = -1 ∨ χ a = 1 := by
    by_cases h : a = 0
    · left
      exact χ_a_zero_eq_zero h field_cardinality q_prime_power q_mod_4_congruent_3
    · rw [← ne_eq] at h
      by_cases h' : IsSquare a
      · right
        right
        apply χ_a_eq_one h h' field_cardinality q_mod_4_congruent_3
      · right
        left
        apply χ_of_a_eq_neg_one h h' field_cardinality q_mod_4_congruent_3

@[blueprint "lemma:χ_of_χ_of_a_eq_χ_of_a"]
lemma χ_of_χ_of_a_eq_χ_of_a
  {a : F}
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ (χ a) = χ a := by
    let h : χ a = 0 ∨ χ a = -1 ∨ χ a = 1 :=
      by exact χ_values field_cardinality q_prime_power q_mod_4_congruent_3
    rcases h with h' | h' | h'
    · simp_all
    · rw [h']
      unfold χ
      let h'' := FiniteFieldBasic.q_sub_one_over_two_odd field_cardinality q_mod_4_congruent_3
      apply Odd.neg_one_pow h''
    · rw [h']
      unfold χ
      rw [one_pow]

@[blueprint "lemma:χ_of_one_over_a_eq_χ_a"]
lemma χ_of_one_over_a_eq_χ_a
  {a : F}
  (a_non_zero : a ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ (1 / a) = χ a := by
    unfold χ;
    rw [div_pow, one_pow, field_cardinality]
    have h : a ^ ((q - 1) / 2) ≠ 0 := by simp_all
    rw [← mul_left_inj' h]
    rw [← pow_add]
    have h' : (q - 1) / 2 + (q - 1) / 2 = q - 1 := by grind
    rw [h']
    rw [← field_cardinality]
    rw [FiniteField.pow_card_sub_one_eq_one a a_non_zero]
    simp_all

@[blueprint "lemma:one_over_χ_of_a_eq_χ_a"]
lemma one_over_χ_of_a_eq_χ_a
  {a : F}
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 1 / χ a  = χ a := by
      -- If a is zero, then χ(a) is zero by definition, so 1/χ(a) is also zero.
    by_cases ha : a = 0
    · simp_all
    · have h : χ a ≠ 0 := by exact χ_a_ne_zero ha field_cardinality
      rw [← mul_left_inj' h]
      unfold χ
      rw [← mul_pow, ← pow_two]
      change 1 / a ^ ((Fintype.card F - 1) / 2) * a ^ ((Fintype.card F - 1) / 2) = χ (a ^ 2)
      rw [χ_a_eq_one (by simp_all) (by aesop) field_cardinality q_mod_4_congruent_3]
      simp_all

  -- Introduced in paper theory theorem 3.A proof
@[blueprint "lemma:χ_of_a_eq_χ_a_mul_b_pow_two"]
lemma χ_of_a_eq_χ_a_mul_b_pow_two {a : F} {b : F}
  (b_nonzero : b ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : χ a = χ (a * b^2) := by
    -- By definition of χ, we know that χ(a * b^2) = (a * b^2)^((q - 1) / 2).
    unfold χ
    rw [mul_pow]
    have h : b^2 ≠ 0 := by simp_all
    change a ^ ((Fintype.card F - 1) / 2) = a ^ ((Fintype.card F - 1) / 2) * χ (b ^ 2)
    rw [χ_a_eq_one h (by aesop) field_cardinality q_mod_4_congruent_3]
    rw [mul_one]

@[blueprint "lemma:b_eq_χ_of_b_mul_principal_sqrt_a"]
lemma b_eq_χ_of_b_mul_principal_sqrt_a
  {a : F}
  (a_square : IsSquare a)
  {b : F}
  (b_h1 : b ^ 2 = a)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : b = (χ b) * a^((q + 1) / 4) := by
    have h : χ b = b ^ ((q - 1) / 2) := by aesop
    -- Substitute $a$ with $b^2$ in the right-hand side of the equation.
    have h' : b ^ ((q - 1) / 2) * (b ^ 2) ^ ((q + 1) / 4) = b := by
      rw [← pow_mul, ← pow_add]
      have h'' : ( q - 1 ) / 2 + 2 * ( ( q + 1 ) / 4 ) = q := by omega
      rw [h'', ← field_cardinality, FiniteField.pow_card]
    simp_all +decide

@[blueprint "lemma:b_pow_q_add_one_over_four_eq_χ_of_a_mul_a"]
lemma b_pow_q_add_one_over_four_eq_χ_of_a_mul_a
  {a : F}
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (a^2)^((q + 1) / 4) = (χ a) * a := by
    rw [← pow_mul, mul_comm, ← field_cardinality, add_comm]
    rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two
      field_cardinality q_mod_4_congruent_3]
    rw [← a_pow_q_add_one_over_two_eq_χ_of_a_mul_a field_cardinality q_mod_4_congruent_3]
    rw [← field_cardinality, add_comm]

@[blueprint "lemma:χ_a_mul_a_IsSquare"]
lemma χ_a_mul_a_IsSquare
  {a : F}
  (a_nonzero : a ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : IsSquare ((χ a) * a) := by
    have h : (χ a) * a ≠ 0 := by
      apply mul_ne_zero
      · exact χ_a_ne_zero a_nonzero field_cardinality
      · exact a_nonzero
    apply (χ_a_eq_one_iff_a_square h field_cardinality q_mod_4_congruent_3).mp
    rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b]
    rw [χ_of_χ_of_a_eq_χ_of_a field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [← pow_two]
    rw [χ_of_a_even_pow_n_eq_one a_nonzero ⟨2, even_two⟩ field_cardinality q_mod_4_congruent_3]

@[blueprint "lemma:a_eq_zero_of_χ_of_a_eq_zero"]
lemma a_eq_zero_of_χ_of_a_eq_zero {a : F} :
  χ a = 0 → a = 0 := by
    intro h
    unfold χ at h
    apply eq_zero_of_pow_eq_zero at h
    exact h

end LegendreSymbol
