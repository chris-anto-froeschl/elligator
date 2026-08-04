/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl, Matthias Güdemann
-/
module

public import Elligator.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.IntegralDomain


/-!
# Finite Field Basic

In this file we introduce some generally helpful lemmas for the finite field `F` with
`q` fulfilling `IsPrimePow`, `Fintype.card F = q` and `q % 4 = 3`.

## References

See [bernstein2013a] for the original account on this specifc finite field.
-/

@[expose] public section

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

namespace Elligator.FiniteFieldBasic

omit [Field F] in
lemma q_odd (q_h3 : q % 4 = 3) : Odd q := by
  rw [Nat.odd_iff]
  omega

omit [Field F] in
lemma q_sub_one_over_two_odd (q_h3 : q % 4 = 3) : Odd ((q - 1) / 2) := by
  rw [Nat.odd_iff]
  omega

omit [Field F] in
lemma q_sub_one_even (q_h3 : q % 4 = 3) : Even (q - 1) := by
  rw [Nat.even_iff]
  omega

omit [Field F] in
lemma q_sub_one_dvd_two (q_h3 : q % 4 = 3) : 2 ∣ q - 1 := Even.two_dvd (q_sub_one_even q_h3)

lemma primepow_ne_one (q_h2 : IsPrimePow q) : q ≠ 1 := by
  intro h
  have h' : ¬ IsPrimePow q := by
    intro h2_1_1
    apply IsPrimePow.two_le at h2_1_1
    rw [h] at h2_1_1
    contradiction
  contradiction

lemma odd_prime_power_gt_two (q_h2 : IsPrimePow q) (hq : Odd q) : q > 2 := by
  have h1 : q ≠ 0 := by grind
  have h2 : q ≠ 1 := primepow_ne_one q_h2
  have h3 : q ≠ 2 := by grind
  lia

omit [Fintype F] in
lemma one_ne_zero : (1 : F) ≠ 0 := by grind

lemma q_add_one_over_four_ne_zero (q_h3 : q % 4 = 3) : (1 + q) / 4 ≠ 0 := by grind

lemma q_add_one_over_two_ne_zero (q_h3 : q % 4 = 3) : (1 + q) / 2 ≠ 0 := by grind

lemma two_ne_zero {F : Type*} [Field F] [Fintype F] {q : ℕ}
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
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
  have hqeq : q = 2^(n : ℕ) := by rw [← q_h1, hcard]
  have hdvd2 : (2 : ℕ) ∣ q := by
    rw [hqeq]
    exact dvd_pow_self 2 n.pos.ne'
  -- 2 ∣ q contradicts q % 4 = 3
  omega

lemma four_ne_zero
  (q_h1 : Fintype.card F = q)
  (q_h3 : q % 4 = 3)
  : (4 : F) ≠ 0 := by
    have h1 : (4 : F) = 2 * 2 := by norm_num
    rw [h1]
    apply mul_ne_zero
    · exact (two_ne_zero q_h1 q_h3)
    · exact (two_ne_zero q_h1 q_h3)

omit [Fintype F] in
lemma neg_one_ne_zero : (-1 : F) ≠ 0 := by
  have he: Odd (-1 : F) := by
    rw [Odd]
    use (-1)
    ring
  have hne: Even (0 : F) := by
    rw [Even]
    use 0
    simp
  simp_all

lemma neg_one_non_square (q_h1 : Fintype.card F = q) (q_h3 : q % 4 = 3)
  : ¬IsSquare (-1 : F) := by grind [FiniteField.isSquare_neg_one_iff]

lemma p_odd_power_odd (p k : ℕ) (hp : Odd p) : Odd (p^k) := Odd.pow hp

omit [Field F] in
lemma q_sub_one_over_two_ne_zero
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : (q - 1) / 2 ≠ 0 := by
    have hodd : Odd q := by grind [q_odd]
    have hgt : q > 2 := odd_prime_power_gt_two q_h2 hodd
    omega

omit [Fintype F] in
lemma pow_two_ne_zero {a : F} (a_ne_zero : a ≠ 0) : a^2 ≠ 0 := by simp_all

omit [Fintype F] in
lemma one_sub_t_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : (1 : F) - t.val ≠ 0 := by
  intro h
  have h1 : t.val = 1 := by
    rw [← add_right_inj t.val] at h
    rw [add_zero] at h
    rw [add_comm] at h
    have h' : t.val - t.val = 0 := by ring
    rw [sub_add] at h
    rw [h'] at h
    rw [sub_zero] at h
    symm at h
    exact h
  have h2 : t.val ≠ 1 := by
    apply And.left
    exact t.property
  contradiction

omit [Fintype F] in
lemma one_add_t_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : (1 : F) + t.val ≠ 0 := by
  intro h
  have h1 : t.val = -1 := by
    rw [← add_left_inj (-1 : F)] at h
    ring_nf at h
    exact h
  have h2 : t.val ≠ -1 := by
    apply And.right
    exact t.property
  contradiction

omit [Fintype F] in
lemma zero_h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by
  constructor
  · symm
    exact one_ne_zero
  · symm
    exact neg_one_ne_zero

omit [Fintype F] in
lemma neg_t_ne_one_and_neg_t_ne_neg_one (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
  let t1 := t.val
  let t2 := -t1
  t2 ≠ 1 ∧ t2 ≠ -1 := by
    intro t1 t2
    rw [ne_eq, ne_eq]
    constructor
    · intro h2_2_1
      have h2_2_1_1 : t1 = -1 := by
        rw [← neg_one_mul]
        nth_rw 2 [← h2_2_1]
        unfold t2
        simp
      have h2_2_1_2 : t1 ≠ -1 := by exact t.property.right
      contradiction
    · intro h2_2_2
      have h2_2_1_1 : t1 = 1 := by
        unfold t2 at h2_2_2
        simp only [neg_inj] at h2_2_2
        exact h2_2_2
      have h2_2_1_2 : t1 ≠ 1 := by exact t.property.left
      contradiction

lemma q_sub_one_over_four_mul_two_eq_one_add_q_over_two
  : (q - 1) / 2 = (q + 1) / 2 - 1 := by omega

omit [Field F] in
lemma one_add_q_mod_four_eq_zero (q_h3 : q % 4 = 3) : (1 + q) % 4 = 0 := by omega

omit [Field F] in
lemma four_dvd_one_add_q (q_h3 : q % 4 = 3) : 4 ∣ (1 + q) :=
  Nat.dvd_of_mod_eq_zero (one_add_q_mod_four_eq_zero q_h3)

omit [Field F] in
lemma one_add_q_over_four_mul_two_eq_one_add_q_over_two (q_h3 : q % 4 = 3)
  : ((1 + q) / 4 * 2) = (1 + q) / 2 := by
    have h : (1 + q) % 4 = 0 :=
      one_add_q_mod_four_eq_zero q_h3
    omega

omit [Fintype F] in
lemma one_add_one_a_pow_two_eq_a_add_one_over_a_over_a {a : F} (a_ne_zero : a ≠ 0)
  : 1 + 1 / a^2 = (a + 1 / a) / a := by
    ring_nf
    rw [mul_inv_cancel₀ a_ne_zero]

lemma q_h1 (q_h3 : q % 4 = 3) : (q + 1) / 4 * 2 = (q - 1) / 2 + 1 := by grind

lemma ringChar_of_F_eq_q (q_h1 : Fintype.card F = q) (q_prime : Prime q) : ringChar F = q := by
  have := FiniteField.card F (ringChar F)
  aesop

@[simp, blueprint "lemma:ringChar_to_q"]
lemma ringChar_to_q (q_h1 : Fintype.card F = q) (q_prime : Prime q)
  : ringChar F = q := by
    have := FiniteField.card F (ringChar F)
    aesop

-- TODO ugly proof, this is just type coercion issues which I do not know how to solve
lemma fin_to_finfield_func_injective
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  : Function.Injective (fun n : Fin q => (n : F)) := by
    unfold Function.Injective
    intro a b h1
    let h2 := ringChar.spec F
    specialize h2 (Int.natAbs (a - b))
    cases abs_cases (( a : ℤ ) - b)
    · rename_i h3
      simp_all only [Nat.cast_natAbs, Int.cast_sub, Int.cast_natCast,
        sub_self, ringChar_to_q, true_iff, abs_eq_self, Int.sub_nonneg,
        Nat.cast_le, Fin.val_fin_le, and_self]
      apply Fin.ext
      have h4 : a ≤ b := by
        apply Nat.le_of_not_lt
        intro h1
        have := Nat.le_of_dvd (by omega) h2
        omega
      apply Nat.le_antisymm h4 h3
    · simp_all only [Nat.cast_natAbs, neg_sub, Int.cast_sub,
        Int.cast_natCast, sub_self, ringChar_to_q, true_iff,
        sub_neg, Nat.cast_lt, Fin.val_fin_lt]
      apply absurd h2
      apply (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))

lemma fin_to_finfield_func_surjective
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  : Function.Surjective (fun n : Fin q => (n : F)) := by
    let h1 := fin_to_finfield_func_injective q_h1 q_prime
    have h2 : Fintype.card (Fin q) = Fintype.card F := by simp_all
    let h3 := (Fintype.bijective_iff_injective_and_card _).mpr ⟨h1, h2⟩
    exact h3.2

lemma nat_to_finfield_func_surjective
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  : Function.Surjective (fun n : ℕ => (n : F)) := by
    intro t
    let h := fin_to_finfield_func_surjective q_h1 q_prime
    exact Exists.elim (h t) fun n hn => ⟨n, hn⟩

/-
Every element of F can be written as (n : F) for some n < q because Fintype.card F = q and
the natural cast n ↦ (n : F) has period equal to ringChar F = q (since q is prime),
so {(0 : F), (1 : F), ..., (q-1 : F)} gives all q distinct elements.
-/
lemma exists_nat_cast_eq
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  (t : F)
  : ∃ (n : ℕ), n < q ∧ (n : F) = t := by
    let h1 := nat_to_finfield_func_surjective q_h1 q_prime
    obtain ⟨n, hn⟩ := h1 t
    use n % q
    split_ands
    · apply Nat.mod_lt n (q_prime.nat_prime.pos)
    · rw [← hn, Nat.mod_def, Nat.cast_sub (Nat.mul_div_le _ _ )]
      aesop

end Elligator.FiniteFieldBasic
