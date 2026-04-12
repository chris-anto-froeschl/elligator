/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Elligator.FiniteFieldBasic
public import Elligator.LegendreSymbol
public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.phiProperties
public import Elligator.Elligator1.bProperties
public import Elligator.Elligator1.bitsToNatProperties

@[expose] public section

/-!
# S Properties

In this file we introduce some generally helpful lemmas for `S`.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section SProperties

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

lemma image_of_bitsToNat_of_S_eq_icc_zero_to_q_sub_one_over_two
  : Finset.image bitsToNat (@S q) = Finset.Icc 0 ((q - 1) / 2) := by
    unfold S
    ext m
    simp [bitsToNat]
    constructor <;> intro hm;
    · lia
    · have h1 : m < 2^(@b q) := by
        apply lt_of_le_of_lt hm
        apply @half_q_lt_two_pow_b q
      obtain ⟨τ, hτ⟩ := bitsToNat_surj (@b q ) m h1
      use τ
      aesop

lemma S_card_eq_icc_zero_to_q_sub_one_over_two_card
  : (@S q).card = (Finset.Icc 0 ((q - 1) / 2)).card := by
    rw [← image_of_bitsToNat_of_S_eq_icc_zero_to_q_sub_one_over_two, Finset.card_image_of_injective _ bitsToNat_injective];

lemma S_card_eq_q_add_one_over_two (q_mod_4_congruent_3 : q % 4 = 3)
  : (@S q).card = (q + 1) / 2 := by
    rw [S_card_eq_icc_zero_to_q_sub_one_over_two_card]
    simp_all
    grind
