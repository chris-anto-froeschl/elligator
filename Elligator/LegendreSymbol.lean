/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Elligator.FiniteFieldBasic

@[expose] public section

/-!
# Legendre Symbol

In this file we introduce some a special case of the traditional Legendre Symbol.
This definition differs from the normal textbook definition, and therefore of mathlib's existing
`Mathlib.NumberTheory.LegendreSymbol.Basic` or `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`
by being bound to a finite field with `q` fulfilling `IsPrimePow`, `Fintype.card F = q` and `q % 4 = 3`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.1 for the original account on this version of the Legendre Symbol.
-/

namespace LegendreSymbol

variable {F : Type*} [Field F] [Fintype F]

/-- χ(a) is the quadratic character of a in the finite field F with q elements, where q is a prime congruent to 3 modulo 4.

This function was added, since Mathlib.NumberTheory.LegendreSymbol.Basic is restricted to ℤ.

Paper definition at chapter 3.1.
-/
noncomputable def χ
  (a : F)
  (q : ℕ)
  -- TODO remove context
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := a^((Fintype.card F - 1) / 2)

lemma χ_a_zero_eq_zero
  (a : F)
  (a_eq_zero : a = 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 0 := by
    change a^((Fintype.card F -1)/2) = 0
    rw [field_cardinality]
    rw [a_eq_zero]
    apply zero_pow (FiniteFieldBasic.q_sub_one_over_two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma χ_a_ne_zero
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a ≠ 0 := by
    change a^((Fintype.card F -1)/2) ≠ 0
    rw [field_cardinality]
    apply pow_ne_zero ((q - 1) / 2) at a_nonzero
    exact a_nonzero

-- TODO make a implicit
lemma neg_χ_a_ne_χ_a
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a ≠ -χ_of_a := by
    let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
    change a^((Fintype.card F -1)/2) ≠ -a^((Fintype.card F -1)/2)
    rw [field_cardinality]
    intro h
    rw [← add_right_inj (a ^ ((q - 1) / 2))] at h
    ring_nf at h
    rw [← field_cardinality] at h
    change χ_of_a * 2 = 0 at h
    apply mul_ne_zero at h
    · exact h
    · exact χ_a_ne_zero a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3
    · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3

lemma χ_a_eq_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 1 := by
    change a^((Fintype.card F - 1)/2) = 1
    have h1 : ∃ r, a = r * r := by apply IsSquare.exists_mul_self a a_square
    rcases h1 with ⟨r, h1_1⟩
    rw [h1_1, ← pow_two]
    ring_nf
    have h2 : (Fintype.card F - 1) / 2 * 2 = Fintype.card F - 1 := by
      apply Nat.div_two_mul_two_of_even (FiniteFieldBasic.q_sub_one_even q field_cardinality q_prime_power q_mod_4_congruent_3)
    rw [h2]
    have h3 : r ≠ 0 := by
      intro h3_1
      rw [h3_1, mul_zero] at h1_1
      contradiction
    apply FiniteField.pow_card_sub_one_eq_one r h3

lemma a_IsSquare
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (χ_a_eq_one : χ a q field_cardinality q_prime_power q_mod_4_congruent_3 = 1)
  :
  IsSquare a := by
    let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold χ at χ_a_eq_one
    unfold IsSquare
    let b := a^((Fintype.card F + 1) / 4 )
    use b
    unfold b
    rw [← pow_two, ← pow_mul, add_comm]
    rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two q field_cardinality q_mod_4_congruent_3]
    have h : (1 + Fintype.card F) / 2 = (Fintype.card F - 1 + 2) / 2 := by
      omega
    rw [h]
    rw [Nat.add_div_of_dvd_right (FiniteFieldBasic.q_sub_one_dvd_two q field_cardinality q_prime_power q_mod_4_congruent_3) , pow_add]
    simp
    change a = χ_of_a * a
    rw [← mul_left_inj' a_nonzero] at χ_a_eq_one
    simp at χ_a_eq_one
    symm
    trivial

lemma χ_a_eq_one_iff_a_square
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 1 ↔ IsSquare a := by
    intro χ_of_a
    constructor
    · intro χ_a_eq_one
      exact a_IsSquare a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3 χ_a_eq_one
    · intro a_square
      exact χ_a_eq_one a a_nonzero a_square q field_cardinality q_prime_power q_mod_4_congruent_3

lemma a_pow_q_add_one_over_two_eq_χ_of_a_mul_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  a ^ ((q + 1) / 2) = χ_of_a * a := by
    intro χ_of_a
    unfold χ_of_a χ
    rw [field_cardinality]
    rw [FiniteFieldBasic.card_sub_one_over_four_mul_two_eq_one_add_card_over_two]
    nth_rw 3 [← pow_one a]
    rw [← pow_add]
    have h'' : (q + 1) / 2 - 1 + 1 = (q + 1) / 2 := by omega
    rw [h'']

lemma χ_a_mul_a_eq_a
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a * a = a := by
    have h := (χ_a_eq_one_iff_a_square a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3).mpr
    rw [h a_square]
    intro χ_of_a
    unfold χ_of_a
    simp

lemma a_pow_q_add_one_over_two_eq_a
  {a : F}
  (a_square : IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  a ^ ((q + 1) / 2) = a := by
    by_cases h : a = 0
    · rw [h, add_comm, zero_pow,]
      exact FiniteFieldBasic.q_add_one_over_two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    · rw [a_pow_q_add_one_over_two_eq_χ_of_a_mul_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [χ_a_mul_a_eq_a a h a_square q field_cardinality q_prime_power q_mod_4_congruent_3]

lemma χ_of_a_pow_two_eq_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ (a^2) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 1 := by
    convert FiniteField.pow_card_sub_one_eq_one _ _ using 1;
    convert pow_right_comm _ _ _ using 1;
    rw [ ← pow_mul, Nat.div_mul_cancel ( even_iff_two_dvd.mp ( FiniteFieldBasic.q_sub_one_even q field_cardinality q_prime_power q_mod_4_congruent_3 ) ) ];
    exact a_nonzero

lemma χ_of_a_eq_neg_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_nonsquare : ¬IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = -1 := by
    field_simp;
    -- By Euler's criterion, since $a$ is not a square, we have $a^{(q-1)/2} \equiv -1 \pmod{q}$.
    have h_euler : a ^ ((Fintype.card F - 1) / 2) = -1 ∨ a ^ ((Fintype.card F - 1) / 2) = 1 := by
      have h_euler : (a ^ ((Fintype.card F - 1) / 2))^2 = 1 := by
        rw [ ← pow_mul, Nat.div_mul_cancel ];
        · exact FiniteField.pow_card_sub_one_eq_one a a_nonzero;
        · omega;
      exact Or.symm ( sq_eq_one_iff.mp h_euler );
    convert h_euler.resolve_right _;
    contrapose! a_nonsquare;
    -- If $a^{(q-1)/2} = 1$, then $a$ is a square in $F$.
    have h_square : ∃ b : F, a = b^2 := by
      use a ^ ((Fintype.card F + 1) / 4);
      rw [ ← pow_mul, show ( Fintype.card F + 1 ) / 4 * 2 = ( Fintype.card F - 1 ) / 2 + 1 from ?_, pow_add, pow_one ];
      · rw [ a_nonsquare, one_mul ];
      · omega;
    exact h_square.elim fun b hb => ⟨ b, by rw [ hb, sq ] ⟩

lemma χ_of_neg_one_eq_neg_one
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_neg_one := χ (-1 : F) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_neg_one = -1 := by
    apply χ_of_a_eq_neg_one
    · apply FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    · apply FiniteFieldBasic.neg_one_non_square q field_cardinality q_prime_power q_mod_4_congruent_3

lemma χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b
  (a b : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_b := χ b q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_a_mul_b := χ (a * b) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a_mul_b = χ_of_a * χ_of_b := by
    convert mul_pow _ _ _

lemma χ_of_a_even_pow_n_eq_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (n : {n : ℕ | Even n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a^(n.val) = 1 := by
    intro χ_of_a
    have n_even := n.prop
    unfold Even at n_even
    rcases n_even with ⟨k, kh⟩
    rw [← mul_two] at kh
    rw [kh, mul_comm, pow_mul, pow_two]
    rw [← χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b a a q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
    rw [χ_of_a_pow_two_eq_one a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [one_pow]

lemma χ_of_a_pow_n_eq_χ_a
  (a : F)
  (n : {n : ℕ | Odd n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a^(n.val) = χ_of_a := by
    obtain ⟨ k, hk ⟩ := n.2;
    by_cases ha : a = 0 <;> simp_all +decide [ pow_add, pow_mul ];
    · unfold χ;
      by_cases h : ( Fintype.card F - 1 ) / 2 = 0 <;> simp +decide [ h ];
    · -- By definition of χ, we know that χ(a)^2 = a^(q-1).
      have hχ_sq : χ a q field_cardinality q_prime_power q_mod_4_congruent_3 ^ 2 = a ^ (q - 1) := by
        unfold χ; ring;
        rw [ Nat.div_mul_cancel ( even_iff_two_dvd.mp ( by rw [ field_cardinality ] ; exact Nat.even_iff.mpr ( by omega ) ) ), field_cardinality ];
      have := FiniteField.pow_card_sub_one_eq_one a; aesop;

lemma χ_of_χ_of_a_eq_χ_of_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_χ_of_a := χ (χ_of_a) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_χ_of_a = χ_of_a := by
    convert χ_of_a_pow_n_eq_χ_a a _ q field_cardinality q_prime_power q_mod_4_congruent_3 using 1;
    swap;
    exact ⟨ ( Fintype.card F - 1 ) / 2, by
      exact Nat.odd_iff.mpr ( by omega ) ⟩
    generalize_proofs at *;
    rfl

lemma χ_of_one_over_a_eq_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_1_over_a = χ_of_a := by
    unfold χ;
    simp +zetaDelta at *;
    rw [ inv_eq_of_mul_eq_one_right ];
    rw [ ← pow_add, ← two_mul, Nat.mul_div_cancel' ];
    · exact FiniteField.pow_card_sub_one_eq_one a a_non_zero;
    · omega

-- TODO a_ne_zero unused?
lemma χ_of_one_over_a_eq_one_over_χ_a
  (a : F)
  (a_ne_zero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_1_over_a = 1 / χ_of_a := by
    unfold χ; simp +decide [ a_ne_zero ]

lemma one_over_χ_of_a_eq_χ_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  1 / χ_of_a  = χ_of_a := by
      -- If a is zero, then χ(a) is zero by definition, so 1/χ(a) is also zero.
    by_cases ha : a = 0;
    · simp_all +decide [ χ ];
      rcases q with ( _ | _ | _ | q ) <;> simp_all +decide;
    · have h_sq : (χ a q field_cardinality q_prime_power q_mod_4_congruent_3) ^ 2 = 1 := by
        convert FiniteField.pow_card_sub_one_eq_one a ha using 1;
        unfold χ; rw [ ← pow_mul, Nat.div_mul_cancel ] ; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, field_cardinality ] ; rw [ ← Nat.mod_add_div q 4, q_mod_4_congruent_3 ] ; norm_num;
        norm_num [ Nat.mul_mod ];
      rw [ div_eq_iff ] <;> aesop

lemma square_of_a
  (a : {n : F // IsSquare n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  a.val^((q + 1) / 2) = a.val := by
    obtain ⟨ r, hr ⟩ := a.2;
    by_cases hr : r = 0 <;> simp_all +decide [ mul_pow, pow_mul' ];
    · exact field_cardinality ▸ Fintype.card_pos_iff.mpr ⟨ 0 ⟩;
    · rw [ ← pow_add, ← two_mul, Nat.mul_div_cancel' ];
      · have := FiniteField.pow_card_sub_one_eq_one r hr; simp_all +decide [ pow_succ' ] ;
        rw [ ← Nat.sub_add_cancel ( show 1 ≤ q from field_cardinality ▸ Fintype.card_pos ), pow_add, pow_one, this, one_mul ];
      · omega

  -- Introduced in paper theory theorem 3.A proof
lemma χ_of_a_eq_χ_a_mul_b_pow_two
  (a : F)
  {b : F}
  (b_nonzero : b ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_a_mul_b_pow_two := χ (a * b^2) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = χ_of_a_mul_b_pow_two := by
    -- By definition of χ, we know that χ(a * b^2) = (a * b^2)^((q - 1) / 2).
    simp [χ];
    rw [ mul_pow, show ( b ^ 2 ) ^ ( ( Fintype.card F - 1 ) / 2 ) = 1 from ?_ ] ; ring;
    rw [ ← pow_mul, Nat.mul_div_cancel' ];
    · exact FiniteField.pow_card_sub_one_eq_one b b_nonzero;
    · omega

-- TODO use?
lemma b_eq_χ_of_b_mul_principal_sqrt_a
  (a : {a : F // IsSquare a})
  {b : F}
  (b_h1 : b^2 = a.val)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_b := χ b q field_cardinality q_prime_power q_mod_4_congruent_3
  b = χ_of_b * a.val^((q + 1) / 4) := by
    -- By definition of $χ$, we know that $χ(b) = b^{(q - 1) / 2}$.
    have hχ_b : χ b q field_cardinality q_prime_power q_mod_4_congruent_3 = b ^ ((q - 1) / 2) := by
      aesop;
    -- Substitute $a$ with $b^2$ in the right-hand side of the equation.
    have h_sub : b ^ ((q - 1) / 2) * (b ^ 2) ^ ((q + 1) / 4) = b := by
      rw [ ← pow_mul, ← pow_add ];
      rw [ show ( q - 1 ) / 2 + 2 * ( ( q + 1 ) / 4 ) = q by omega ];
      rw [ ← field_cardinality, FiniteField.pow_card ];
    simp_all +decide [ ← sq ]

lemma b_pow_q_add_one_over_four_eq_χ_of_a_mul_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  (a^2)^((q + 1) / 4) = χ_of_a * a := by
    intro χ_of_a
    rw [← pow_mul, mul_comm, ← field_cardinality, add_comm]
    rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two q field_cardinality q_mod_4_congruent_3]
    rw [← a_pow_q_add_one_over_two_eq_χ_of_a_mul_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [← field_cardinality, add_comm]

lemma χ_a_mul_a_IsSquare
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  IsSquare (χ_of_a * a) := by
    intro χ_of_a
    have h1 : χ_of_a * a ≠ 0 := by
      apply mul_ne_zero
      · exact χ_a_ne_zero a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact a_nonzero
    apply (χ_a_eq_one_iff_a_square (χ_of_a * a) h1 q field_cardinality q_prime_power q_mod_4_congruent_3).mp
    rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b χ_of_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [χ_of_χ_of_a_eq_χ_of_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [← pow_two]
    rw [χ_of_a_even_pow_n_eq_one a a_nonzero ⟨2, even_two⟩ ]

lemma χ_values
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 0 ∨ χ_of_a = -1 ∨ χ_of_a = 1 := by
    intro χ_of_a
    by_cases h : a = 0
    · left
      exact χ_a_zero_eq_zero a h q field_cardinality q_prime_power q_mod_4_congruent_3
    · rw [← ne_eq] at h
      by_cases h' : IsSquare a
      · right
        right
        apply χ_a_eq_one a h h' q field_cardinality q_prime_power q_mod_4_congruent_3
      · right
        left
        apply χ_of_a_eq_neg_one a h h' q field_cardinality q_prime_power q_mod_4_congruent_3

lemma a_eq_zero_of_χ_of_a_eq_zero
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 0 → a = 0 := by
    intro χ_of_a h
    unfold χ_of_a χ at h
    apply eq_zero_of_pow_eq_zero at h
    exact h
