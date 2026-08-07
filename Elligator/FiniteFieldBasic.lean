/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl, Matthias Güdemann
-/
module

public import Elligator.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Finite Field Basic

In this file we introduce some generally helpful lemmas for the finite field `F` with
`q` fulfilling `IsPrimePow`/`Prime`, `Fintype.card F = q` and `q % 4 = 3`.

## References

See [bernstein2013a] for the original account on this specifc finite field.
-/

@[expose] public section

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

namespace Elligator.FiniteFieldBasic

omit [Field F] in
lemma q_odd (hq_mod : q % 4 = 3) : Odd q := by
  rw [Nat.odd_iff]
  omega

omit [Field F] in
lemma q_sub_one_div_two_odd (hq_mod : q % 4 = 3) : Odd ((q - 1) / 2) := by
  rw [Nat.odd_iff]
  omega

omit [Field F] in
lemma q_sub_one_even (hq_mod : q % 4 = 3) : Even (q - 1) := by
  rw [Nat.even_iff]
  omega

omit [Fintype F] in
lemma one_ne_zero : (1 : F) ≠ 0 := by grind

lemma q_add_one_div_four_ne_zero (hq_mod : q % 4 = 3) : (1 + q) / 4 ≠ 0 := by grind

lemma q_add_one_div_two_ne_zero (hq_mod : q % 4 = 3) : (1 + q) / 2 ≠ 0 := by grind

lemma two_ne_zero {F : Type*} [Field F] [Fintype F] {q : ℕ}
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (2 : F) ≠ 0 := by
  intro h
  -- turn `(2 : F) = 0` into a divisibility statement about the characteristic
  have hdvd : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F (ringChar F) 2).mp h
  -- ringChar F ∣ 2 and ringChar F ≠ 1 (F is nontrivial) forces ringChar F = 2
  have hp : ringChar F = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 (CharP.char_ne_one F (ringChar F))
    · exact h1
  haveI : CharP F 2 := by
    rw [← hp]
    exact ringChar.charP F
  -- a finite field of characteristic 2 has cardinality a power of 2
  obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
  have hqeq : q = 2^(n : ℕ) := by rw [← hq_card, hcard]
  have hdvd2 : (2 : ℕ) ∣ q := by
    rw [hqeq]
    exact dvd_pow_self 2 n.pos.ne'
  -- 2 ∣ q contradicts q % 4 = 3
  omega

lemma four_ne_zero
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (4 : F) ≠ 0 := by
    have h1 : (4 : F) = 2 * 2 := by norm_num
    rw [h1]
    apply mul_ne_zero
    · exact (two_ne_zero hq_card hq_mod)
    · exact (two_ne_zero hq_card hq_mod)

lemma ringChar_ne_two (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : ringChar F ≠ 2 := by
    intro h
    refine two_ne_zero hq_card hq_mod ?_
    have h' : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).mpr (by rw [h])
    exact h'

omit [Fintype F] in
lemma neg_one_ne_zero : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero

lemma neg_one_non_square (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : ¬IsSquare (-1 : F) := by grind [FiniteField.isSquare_neg_one_iff]

omit [Fintype F] in
lemma one_sub_t_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : (1 : F) - t.val ≠ 0 :=
  sub_ne_zero.mpr t.property.1.symm

omit [Fintype F] in
lemma one_add_t_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : (1 : F) + t.val ≠ 0 := by
  intro h
  rw [add_comm] at h
  exact t.property.2 (eq_neg_of_add_eq_zero_left h)

omit [Fintype F] in
lemma neg_t_ne_one_and_neg_t_ne_neg_one (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
  -t.val ≠ 1 ∧ -t.val ≠ -1 :=
    ⟨fun h => t.property.2 (neg_eq_iff_eq_neg.mp h), fun h => t.property.1 (neg_inj.mp h)⟩

omit [Field F] in
lemma one_add_q_div_four_mul_two_eq_one_add_q_div_two (hq_mod : q % 4 = 3)
  : ((1 + q) / 4 * 2) = (1 + q) / 2 := by omega

lemma ringChar_of_F_eq_q (hq_card : Fintype.card F = q) (q_prime : Prime q) : ringChar F = q := by
  have := FiniteField.card F (ringChar F)
  aesop

lemma fin_to_finfield_injective (hq_card : Fintype.card F = q) (q_prime : Prime q)
  : Function.Injective (fun n : Fin q => (n : F)) := by
    have h : CharP F q := by
      rw [← ringChar_of_F_eq_q hq_card q_prime]
      exact ringChar.charP F
    intro a b hab
    exact Fin.ext (CharP.natCast_injOn_Iio F q a.isLt b.isLt hab)

/-- Every element of `F` is the cast of some `n : Fin q`: the cast `Fin q → F` is injective
and `Fin q` and `F` have the same cardinality, so it is bijective. -/
lemma exists_fin_cast_eq (hq_card : Fintype.card F = q) (q_prime : Prime q) (t : F)
  : ∃ n : Fin q, (n : F) = t := by
    -- `Fin q` and `F` have matching cardinalities.
    have hcard : Fintype.card (Fin q) = Fintype.card F := by rw [Fintype.card_fin, hq_card]
    -- An injective map between finite types of equal cardinality is automatically bijective.
    have h : Function.Bijective (fun n : Fin q => (n : F)) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fin_to_finfield_injective hq_card q_prime, hcard⟩
    exact h.surjective t

/- Every element of F can be written as (n : F) for some n < q because Fintype.card F = q and
the natural cast n ↦ (n : F) has period equal to ringChar F = q (since q is prime),
so {(0 : F), (1 : F), ..., (q-1 : F)} gives all q distinct elements.  -/
lemma exists_nat_cast_eq
  (hq_card : Fintype.card F = q)
  (q_prime : Prime q)
  (t : F)
  : ∃ (n : ℕ), n < q ∧ (n : F) = t := by
    obtain ⟨n, hn⟩ : ∃ n : Fin q, (n : F) = t := exists_fin_cast_eq hq_card q_prime t
    exact ⟨n.val, n.isLt, hn⟩

end Elligator.FiniteFieldBasic
