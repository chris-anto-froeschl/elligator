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

@[expose] public section

/-!
# Finite Field Basic

In this file we introduce some generally helpful lemmas for the finite field `F` with
`q` fulfilling `IsPrimePow`, `Fintype.card F = q` and `q % 4 = 3`.

## Main results

- TODO

## References

See [bernstein2013a] for the original account on this specifc finite field.
-/

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

namespace FiniteFieldBasic

@[blueprint "lemma:q_ne_two"]
lemma q_ne_two (q_mod_4_congruent_3 : q % 4 = 3) : q ≠ 2 := by omega

@[blueprint "lemma:q_mod_two_congruent_one"]
lemma q_mod_two_congruent_one (q_mod_4_congruent_3 : q % 4 = 3) : q % 2 = 1 := by omega

omit [Field F] in
@[blueprint "lemma:q_odd"]
lemma q_odd (field_cardinality : Fintype.card F = q) (q_mod_4_congruent_3 : q % 4 = 3)
  : Odd (Fintype.card F) := by
    rw [field_cardinality]
    have hq: q % 2 = 1 := by apply q_mod_two_congruent_one q_mod_4_congruent_3
    have hq1: ∃ k, q = 2 * k + 1 := by
      apply Nat.mod_eq_iff.1 at hq
      cases hq
      · simp_all
      · simp_all
    rw [Odd]
    exact hq1

omit [Field F] in
@[blueprint "lemma:q_add_one_even"]
lemma q_add_one_even
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : Even (q + 1) := by
    refine Nat.even_add_one.mpr ?_
    have h0: Odd (Fintype.card F) := by
      apply q_odd field_cardinality q_mod_4_congruent_3
    rw [field_cardinality] at h0
    exact Nat.not_even_iff_odd.mpr h0

omit [Field F] in
@[blueprint "lemma:q_sub_one_even"]
lemma q_sub_one_even
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : Even (Fintype.card F - 1) := by
    rw [field_cardinality]
    have hq: Odd q := by
      rw [<- field_cardinality]
      apply q_odd field_cardinality q_mod_4_congruent_3
    rw [Odd] at hq
    rw [Even]
    cases hq
    rename_i k hk
    use k
    simp_all
    linarith

omit [Field F] in
@[blueprint "lemma:q_sub_one_dvd_two"]
lemma q_sub_one_dvd_two
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 2 ∣ Fintype.card F - 1 := by
    apply Even.two_dvd (q_sub_one_even field_cardinality q_mod_4_congruent_3)

omit [Field F] in
@[blueprint "lemma:q_not_dvd_two"]
lemma q_not_dvd_two
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ¬(2 ∣ q) := by
    intro h
    -- Since q is prime and (q % 4 = 3 => q ≠ 2), it cannot divide 2.
    -- So in this assumption, q must be 2.
    --rw [Nat.prime_dvd_prime_iff_eq q_prime_power (Nat.prime_two)] at h
    --apply q_ne_two q q_prime_power q_mod_4_congruent_3 at h
    --have h1 : q ≠ 2 := q_ne_two q q_prime_power q_mod_4_congruent_3
    --contradiction
    have hq: Odd q := by
      rw [<- field_cardinality]
      apply q_odd field_cardinality q_mod_4_congruent_3
    have hq': Even q := by
      exact (even_iff_exists_two_nsmul q).mpr h
    have hq'': Odd q → ¬ Even q := by
      intro h1
      exact Nat.not_even_iff_odd.mpr hq
    simp_all

@[blueprint "lemma:power_odd_p_odd"]
lemma power_odd_p_odd
  (p k : ℕ)
  (hk: 0 < k)
  (hp: Odd (p^k))
  :
  Odd p := by
    cases k
    · simp_all
    · rename_i k
      have hpn_one: p^(k+1) = p^k * p := by ring
      -- cases hp
      --rename_i k1 hk1
      have h: Odd (p^k * p) → Odd (p^k) ∧ Odd p := by
        exact fun a ↦ (fun {m n} ↦ Nat.odd_mul.mp) a
      rw [hpn_one] at hp
      have h': Odd (p^k) ∧ Odd p := by apply h hp
      simp_all

@[blueprint "lemma:odd_prime_power_gt_two"]
lemma odd_prime_power_gt_two (q_prime_power : IsPrimePow q) (hq: Odd q)
  : q > 2 := by
    rw [IsPrimePow] at q_prime_power
    cases q_prime_power
    rename_i p hk
    cases hk
    rename_i k hp
    cases hp
    rename_i right
    cases right
    rename_i hprime k_gt_zero q_p_power
    have odd_p_pow_k: Odd (p^k) := by
      rw [<- q_p_power] at hq
      exact hq
    have hp: Odd p := by apply power_odd_p_odd p k k_gt_zero odd_p_pow_k
    have hp1: p > 2 := by
      refine Nat.two_lt_of_ne ?_ ?_ ?_
      · intro h_zero
        simp_all
      · intro h_one
        simp_all
      · intro p_two
        rw [p_two] at hp
        have even_two: Even 2 := by
          exact Nat.even_iff.mpr rfl
        have not_odd_two: ¬ Odd 2 := by exact Nat.not_odd_iff_even.mpr even_two
        contradiction
    have h_p_pow_gt_two: p^k > 2 := by
      cases k
      · simp_all
      · rename_i k
        have p_k_p_one: p^(k+1) = p^k * p := by ring
        rw [p_k_p_one]
        have p_k_gt_zero: p^k > 0 := by
          refine Nat.pow_pos ?_
          linarith
        exact lt_mul_of_one_le_of_lt p_k_gt_zero hp1
    simp_all

omit [Fintype F] in
@[blueprint "lemma:one_ne_zero"]
lemma one_ne_zero : (1 : F) ≠ 0 := by
  have he: Odd (-1 : F) := by
    rw [Odd]
    use (-1)
    ring
  have hne: Even (0 : F) := by
    rw [Even]
    use 0
    simp
  simp_all

@[blueprint "lemma:q_add_one_over_four_ne_zero"]
lemma q_add_one_over_four_ne_zero (q_mod_4_congruent_3 : q % 4 = 3)
  : (1 + q) / 4 ≠ 0 := by
    apply Nat.div_ne_zero_iff.2
    constructor
    · norm_num
    · grind

@[blueprint "lemma:q_add_one_over_two_ne_zero"]
lemma q_add_one_over_two_ne_zero (q_mod_4_congruent_3 : q % 4 = 3) :
  (1 + q) / 2 ≠ 0 := by
    apply Nat.div_ne_zero_iff.2
    constructor
    · norm_num
    · grind

@[blueprint "lemma:char_ne_two"]
lemma char_ne_two
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : Fintype.card F ≠ 2 := by
    have h1 := FiniteField.card F ( ringChar F )
    simp_all +decide;
    rintro h
    simp_all +decide

@[blueprint "lemma:ring_char_ne_two"]
lemma ring_char_ne_two
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ringChar F ≠ 2 := by
    have h1 := FiniteField.card F ( ringChar F )
    simp_all +decide;
    rintro h
    simp_all +decide
    rcases h1 with ⟨ x, rfl ⟩; rcases x with ( _ | _ | x ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;

@[blueprint "lemma:two_ne_zero"]
lemma two_ne_zero
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (2 : F) ≠ 0 := by
    let char_ne_two := ring_char_ne_two field_cardinality q_prime_power q_mod_4_congruent_3
    let h1 := FiniteField.card F ( ringChar F )
    intro h2
    apply char_ne_two
    have h3 := ringChar.spec F;
    specialize h3 2; simp_all +decide [ Nat.dvd_prime ];
    exact not_subsingleton _ h3

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
lemma p_odd_power_odd
  (p k : ℕ)
  (hp: Odd p)
  : Odd (p^k) := by
    induction' k
    · simp
    · rename_i n hn
      rw [Odd] at hn
      cases hn
      rename_i k hyp
      have hpn_one: p^(n+1) = p^n * p := by ring
      rw [Odd, hpn_one]
      rw [Odd] at hp
      cases hp
      rename_i k1 hp
      rw [hyp] at hpn_one
      nth_rw 2 [hp] at hpn_one
      have h0: (2*k+1)*(2*k1 + 1) = 4*k*k1 + 2*k + 2*k1 + 1 := by ring
      have h1: 4*k*k1 + 2*k + 2*k1 + 1 = 2*(2*k*k1 + k + k1) + 1:= by ring
      use 2*k*k1 + k + k1
      simp_all

@[blueprint "lemma:q_sub_one_over_two_ne_zero"]
lemma q_sub_one_over_two_ne_zero
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (q - 1) / 2 ≠ 0 := by
    have q_odd: Odd q := by
        rw [<- field_cardinality]
        apply q_odd field_cardinality q_mod_4_congruent_3
    apply Nat.div_ne_zero_iff.2
    constructor
    · norm_num
    · rw [IsPrimePow] at q_prime_power
      cases q_prime_power
      rename_i p hp
      cases hp
      rename_i k hk
      cases hk
      rename_i hp hpk
      cases hpk
      rename_i hk hpk
      have p_power_odd: Odd (p^k) := by
        rw [<- hpk] at q_odd
        exact q_odd
      have p_odd: Odd p := by
        apply power_odd_p_odd p k hk p_power_odd
      have q_gte_q: q ≥ p := by
        simp_all
        rw [<- hpk]
        exact Nat.le_pow hk
      have p_gt_2: p > 2 := by
        simp_all
        refine odd_prime_power_gt_two ?_ p_odd
        rw [IsPrimePow]
        use p, 1
        simp_all
      simp_all
      refine (Nat.le_sub_one_iff_lt ?_).mpr ?_
      · refine Nat.zero_lt_of_ne_zero ?_
        intro hq
        simp_all
      · exact Nat.lt_of_lt_of_le p_gt_2 q_gte_q

omit [Fintype F] in
@[blueprint "lemma:pow_two_ne_zero"]
lemma pow_two_ne_zero
  {a : F}
  (a_ne_zero : a ≠ 0)
  :
  a^2 ≠ 0 := by
    rw [pow_two]
    apply mul_ne_zero
    · exact a_ne_zero
    · exact a_ne_zero

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
        simp at h2_2_2
        exact h2_2_2
      have h2_2_1_2 : t1 ≠ 1 := by exact t.property.left
      contradiction

omit [Field F] in
@[blueprint "lemma:one_add_card_mod_four_eq_zero"]
lemma one_add_card_mod_four_eq_zero
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (1 + Fintype.card F) % 4 = 0 := by
    omega

omit [Field F] in
@[blueprint "lemma:four_dvd_one_add_card"]
lemma four_dvd_one_add_card
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 4 ∣ (1 + Fintype.card F) := by
    exact Nat.dvd_of_mod_eq_zero (one_add_card_mod_four_eq_zero field_cardinality q_mod_4_congruent_3)

omit [Field F] in
@[blueprint "lemma:one_add_card_over_four_mul_two_eq_one_add_card_over_two"]
lemma one_add_card_over_four_mul_two_eq_one_add_card_over_two
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let card := Fintype.card F
  ((1 + card) / 4 * 2) = (1 + card) / 2 := by
    intro card
    obtain ⟨k, hk⟩ := four_dvd_one_add_card field_cardinality q_mod_4_congruent_3
    rw [hk]
    nth_rw 3 [mul_comm]
    simp_all
    rw [Nat.mul_div_assoc]
    simp_all

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
  (q - 1) / 2 = (q + 1) / 2 - 1 := by
    omega

@[blueprint "lemma:ringChar_of_F_eq_q"]
lemma ringChar_of_F_eq_q
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  : ringChar F = q := by
      have := FiniteField.card F (ringChar F)
      aesop

@[blueprint "lemma:CharP_of_F_eq_q"]
lemma CharP_of_F_eq_q
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  : CharP F q := by
    let h1 := ringChar_of_F_eq_q field_cardinality q_prime
    exact h1 ▸ by infer_instance

/-
Every element of F can be written as (n : F) for some n < q because Fintype.card F = q and the natural cast n ↦ (n : F) has period equal to ringChar F
= q (since q is prime), so {(0 : F), (1 : F), ..., (q-1 : F)} gives all q distinct elements.
-/
@[blueprint "lemma:exists_nat_cast_eq"]
lemma exists_nat_cast_eq
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (t : F)
  : ∃ (n : ℕ), n < q ∧ (n : F) = t := by
    have h_nat_cast : Function.Surjective (fun n : ℕ => (n : F)) := by
      intro t
      have h_order : ringChar F = q := by
        have := FiniteField.card F ( ringChar F ); aesop;
      have h_order : Function.Injective (fun n : Fin (Fintype.card F) => (n : F)) := by
        intro a b hab;
        have := ringChar.spec F;
        specialize this ( a - b |> Int.natAbs ); simp_all +decide
        cases abs_cases ( ( a : ℤ ) - b ) <;> simp_all +decide
        · exact Fin.ext ( Nat.le_antisymm ( Nat.le_of_not_lt fun h => by have := Nat.le_of_dvd ( by omega ) this; omega ) ‹_› );
        · exact absurd this ( Nat.not_dvd_of_pos_of_lt ( by omega ) ( by omega ) );
      have h_order : Function.Surjective (fun n : Fin (Fintype.card F) => (n : F)) := by
        exact ( Fintype.bijective_iff_injective_and_card _ ).mpr ⟨ h_order, by simp +decide [ Fintype.card_fin ] ⟩ |>.2;
      exact Exists.elim ( h_order t ) fun n hn => ⟨ n, hn ⟩;
    cases' h_nat_cast t with n hn;
    refine' ⟨ n % q, Nat.mod_lt _ q_prime.nat_prime.pos, _ ⟩;
    rw [ ← hn, Nat.mod_def ];
    rw [ Nat.cast_sub ( Nat.mul_div_le _ _ ) ]; aesop

/-
In a prime field with `q ≡ 3 (mod 4)` (hence `q` odd), for any `n < q`, either
`n ≤ (q-1)/2` or `q - n ≤ (q-1)/2` (i.e., `n` or its "negation" `q-n` lies in the
lower half).
-/
@[blueprint "lemma:nat_or_neg_in_lower_half"]
lemma nat_or_neg_in_lower_half
  (q_prime : Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (n : ℕ) (hn : n < q)
  : n ≤ (q - 1) / 2 ∨ (q - n ≤ (q - 1) / 2 ∧ 0 < n) := by
    cases Nat.Prime.eq_two_or_odd q_prime.nat_prime <;> omega

/-
Negation in `F_q` for a natural number cast: `-(n : F) = (q - n : F)` when
`q = Fintype.card F` is the characteristic.
-/
@[blueprint "lemma:neg_natCast_eq"]
lemma neg_natCast_eq
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (n : ℕ) (hn' : n < q)
  : -(n : F) = ((q - n : ℕ) : F) := by
    rw [ Nat.cast_sub hn'.le ];
    rw [ neg_eq_iff_add_eq_zero ]; aesop
