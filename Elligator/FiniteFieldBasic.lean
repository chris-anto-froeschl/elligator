/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl, Matthias Güdemann
-/
module

public import Architect
public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.Cases

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

namespace FiniteFieldBasic

omit [Field F] in
@[blueprint "lemma:q_odd"]
lemma q_odd (field_cardinality : Fintype.card F = q) (q_mod_4_congruent_3 : q % 4 = 3)
  : Odd (Fintype.card F) := by
    rw [Nat.odd_iff]
    omega

omit [Field F] in
@[blueprint "lemma:q_sub_one_even"]
lemma q_sub_one_even (field_cardinality : Fintype.card F = q) (q_mod_4_congruent_3 : q % 4 = 3)
  : Even (Fintype.card F - 1) := by
    rw [Nat.even_iff]
    omega

omit [Field F] in
@[blueprint "lemma:q_sub_one_dvd_two"]
lemma q_sub_one_dvd_two (field_cardinality : Fintype.card F = q) (q_mod_4_congruent_3 : q % 4 = 3)
  : 2 ∣ Fintype.card F - 1 := Even.two_dvd (q_sub_one_even field_cardinality q_mod_4_congruent_3)

@[blueprint "lemma:primepow_ne_one"]
lemma primepow_ne_one (q_prime_power : IsPrimePow q)
  : q ≠ 1 := by
    intro h
    have h' : ¬ IsPrimePow q := by
      intro h2_1_1
      apply IsPrimePow.two_le at h2_1_1
      rw [h] at h2_1_1
      contradiction
    contradiction

@[blueprint "lemma:odd_prime_power_gt_two"]
lemma odd_prime_power_gt_two (q_prime_power : IsPrimePow q) (hq : Odd q) : q > 2 := by
  have h1 : q ≠ 0 := by grind
  have h2 : q ≠ 1 := primepow_ne_one q_prime_power
  have h3 : q ≠ 2 := by grind
  lia

omit [Fintype F] in
@[blueprint "lemma:one_ne_zero"]
lemma one_ne_zero : (1 : F) ≠ 0 := by grind

@[blueprint "lemma:q_add_one_over_four_ne_zero"]
lemma q_add_one_over_four_ne_zero (q_mod_4_congruent_3 : q % 4 = 3) : (1 + q) / 4 ≠ 0 := by grind

@[blueprint "lemma:q_add_one_over_two_ne_zero"]
lemma q_add_one_over_two_ne_zero (q_mod_4_congruent_3 : q % 4 = 3) : (1 + q) / 2 ≠ 0 := by grind

omit [Field F] in
@[blueprint "lemma:char_ne_two"]
lemma char_ne_two (field_cardinality : Fintype.card F = q) (q_mod_4_congruent_3 : q % 4 = 3)
  : Fintype.card F ≠ 2 := by
    rw [field_cardinality]
    omega

@[blueprint "lemma:ring_char_ne_two"]
lemma ring_char_ne_two
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ringChar F ≠ 2 := by
    obtain ⟨p, k, hp, hk, hpk⟩ := q_prime_power
    obtain ⟨n, hrc, hcard⟩ := FiniteField.card F (ringChar F)
    rw [field_cardinality, ← hpk] at hcard
    have h1 : p ∣ ringChar F := hp.dvd_of_dvd_pow (hcard ▸ dvd_pow_self p hk.ne')
    have h2 : p = ringChar F := (Nat.prime_dvd_prime_iff_eq hp.nat_prime hrc).mp h1
    have h3 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ q := by grind
      omega
    rw [← h2]
    exact h3

@[blueprint "lemma:two_ne_zero"]
lemma two_ne_zero
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (2 : F) ≠ 0 := by
    intro h
    apply ring_char_ne_two field_cardinality q_prime_power q_mod_4_congruent_3
    obtain ⟨n, hp, _⟩ := FiniteField.card F (ringChar F)
    have h1 : ringChar F ∣ 2 := (ringChar.spec F 2).mp (by simp_all)
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 := hp.two_le
    omega

@[blueprint "lemma:four_ne_zero"]
lemma four_ne_zero
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (4 : F) ≠ 0 := by
    have h1 : (4 : F) = 2 * 2 := by norm_num
    rw [h1]
    apply mul_ne_zero
    · exact (FiniteFieldBasic.two_ne_zero field_cardinality q_prime_power q_mod_4_congruent_3)
    · exact (FiniteFieldBasic.two_ne_zero field_cardinality q_prime_power q_mod_4_congruent_3)

omit [Fintype F] in
@[blueprint "lemma:neg_one_ne_zero"]
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

@[blueprint "lemma:neg_one_non_square"]
lemma neg_one_non_square
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ¬IsSquare (-1 : F) := by
    have h_neg_one_not_square : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := by
      apply_rules [ FiniteField.isSquare_neg_one_iff ];
    aesop

@[blueprint "lemma:p_odd_power_odd"]
lemma p_odd_power_odd (p k : ℕ) (hp : Odd p) : Odd (p^k) := Odd.pow hp

omit [Field F] in
@[blueprint "lemma:q_sub_one_over_two_ne_zero"]
lemma q_sub_one_over_two_ne_zero
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (q - 1) / 2 ≠ 0 := by
    have hodd : Odd q := by grind [q_odd]
    have hgt : q > 2 := odd_prime_power_gt_two q_prime_power hodd
    omega

omit [Fintype F] in
@[blueprint "lemma:pow_two_ne_zero"]
lemma pow_two_ne_zero {a : F} (a_ne_zero : a ≠ 0) : a^2 ≠ 0 := by simp_all

omit [Fintype F] in
@[blueprint "lemma:one_sub_t_ne_zero"]
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
@[blueprint "lemma:one_add_t_ne_zero"]
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
@[blueprint "lemma:zero_h"]
lemma zero_h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by
  constructor
  · symm
    exact FiniteFieldBasic.one_ne_zero
  · symm
    exact FiniteFieldBasic.neg_one_ne_zero

omit [Fintype F] in
@[blueprint "lemma:neg_t_ne_one_and_neg_t_ne_neg_one"]
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

omit [Field F] in
@[blueprint "lemma:one_add_card_mod_four_eq_zero"]
lemma one_add_card_mod_four_eq_zero
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (1 + Fintype.card F) % 4 = 0 := by omega

omit [Field F] in
@[blueprint "lemma:four_dvd_one_add_card"]
lemma four_dvd_one_add_card
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 4 ∣ (1 + Fintype.card F) := by
    exact Nat.dvd_of_mod_eq_zero (
      one_add_card_mod_four_eq_zero field_cardinality q_mod_4_congruent_3)

omit [Field F] in
@[blueprint "lemma:one_add_card_over_four_mul_two_eq_one_add_card_over_two"]
lemma one_add_card_over_four_mul_two_eq_one_add_card_over_two
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let card := Fintype.card F
  ((1 + card) / 4 * 2) = (1 + card) / 2 := by
    intro card
    have h : (1 + card) % 4 = 0 :=
      one_add_card_mod_four_eq_zero field_cardinality q_mod_4_congruent_3
    omega

omit [Fintype F] in
@[blueprint "lemma:one_add_one_a_pow_two_eq_a_add_one_over_a_over_a"]
lemma one_add_one_a_pow_two_eq_a_add_one_over_a_over_a
  {a : F}
  (a_ne_zero : a ≠ 0)
  : 1 + 1 / a^2 = (a + 1 / a) / a := by
    ring_nf
    rw [mul_inv_cancel₀ a_ne_zero]

@[blueprint "lemma:card_sub_one_over_four_mul_two_eq_one_add_card_over_two"]
lemma card_sub_one_over_four_mul_two_eq_one_add_card_over_two :
  (q - 1) / 2 = (q + 1) / 2 - 1 := by omega

@[blueprint "lemma:ringChar_of_F_eq_q"]
lemma ringChar_of_F_eq_q (field_cardinality : Fintype.card F = q) (q_prime : Prime q)
  : ringChar F = q := by
    have := FiniteField.card F (ringChar F)
    aesop

-- TODO remove or above
@[simp, blueprint "lemma:ringChar_to_q"]
lemma ringChar_to_q (field_cardinality : Fintype.card F = q) (q_prime : Prime q)
  : ringChar F = q := by
    have := FiniteField.card F (ringChar F)
    aesop

@[blueprint "lemma:nat_to_finfield_func_surjective"]
lemma fin_to_finfield_func_injective
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  : Function.Injective (fun n : Fin (Fintype.card F) => (n : F)) := by
    intro a b hab
    have := ringChar.spec F;
    specialize this ( a - b |> Int.natAbs )
    cases abs_cases ( ( a : ℤ ) - b ) <;> simp_all +decide
    · exact Fin.ext ( Nat.le_antisymm ( Nat.le_of_not_lt fun h => by have := Nat.le_of_dvd ( by omega ) this; omega ) ‹_› );
    · exact absurd this ( Nat.not_dvd_of_pos_of_lt ( by omega ) ( by omega ) );

@[blueprint "lemma:fin_to_finfield_func_surjective"]
lemma fin_to_finfield_func_surjective
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  : Function.Surjective (fun n : Fin (Fintype.card F) => (n : F)) := by
    let h1 := fin_to_finfield_func_injective field_cardinality q_prime
    have h2 : Fintype.card (Fin (Fintype.card F)) = Fintype.card F := by simp_all
    let h3 := (Fintype.bijective_iff_injective_and_card _).mpr ⟨h1, h2⟩
    exact h3.2

@[blueprint "lemma:nat_to_finfield_func_surjective"]
lemma nat_to_finfield_func_surjective
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  : Function.Surjective (fun n : ℕ => (n : F)) := by
    intro t
    let h := fin_to_finfield_func_surjective field_cardinality q_prime
    exact Exists.elim (h t) fun n hn => ⟨ n, hn ⟩;

/-
Every element of F can be written as (n : F) for some n < q because Fintype.card F = q and
the natural cast n ↦ (n : F) has period equal to ringChar F = q (since q is prime),
so {(0 : F), (1 : F), ..., (q-1 : F)} gives all q distinct elements.
-/
@[blueprint "lemma:exists_nat_cast_eq"]
lemma exists_nat_cast_eq
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (t : F)
  : ∃ (n : ℕ), n < q ∧ (n : F) = t := by
    let h1 := nat_to_finfield_func_surjective field_cardinality q_prime
    obtain ⟨n, hn⟩ := h1 t
    use n % q
    split_ands
    · apply Nat.mod_lt n (q_prime.nat_prime.pos)
    · rw [← hn, Nat.mod_def, Nat.cast_sub (Nat.mul_div_le _ _ )]
      aesop

end FiniteFieldBasic
