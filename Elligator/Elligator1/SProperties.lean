/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.phiProperties
public import Elligator.Elligator1.bProperties
public import Elligator.Elligator1.bitsToNatProperties

/-!
# S Properties

This file identifies the binary values represented by `S`, the lower-half string set used in
Theorem 4, and computes its cardinality.

## Main results

- `image_of_bitsToNat_of_S_eq_icc_zero_to_q_sub_one_over_two`: binary evaluation maps `S` onto
  the integer interval `[0, (q - 1) / 2]`.
- `S_card_eq_q_add_one_over_two`: when `q ≡ 3 (mod 4)`, the set `S` has `(q + 1) / 2` elements.

## References

See [bernstein2013a], Section 3.4, Theorem 4.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

/-- Binary evaluation maps the admissible strings `S` onto exactly the natural-number interval
from `0` through `(q - 1) / 2`, as required by the definition of `S` in Theorem 4. -/
@[blueprint "lemma:image_of_bitsToNat_of_S_eq_icc_zero_to_q_sub_one_over_two"]
lemma image_of_bitsToNat_of_S_eq_icc_zero_to_q_sub_one_over_two
  : Finset.image bitsToNat (@S q) = Finset.Icc 0 ((q - 1) / 2) := by
    unfold S bitsToNat
    ext m
    constructor
    · grind
    · intro h
      have h' : m < 2^(@b q) := by grind [half_q_lt_two_pow_b]
      obtain ⟨τ, hτ⟩ := bitsToNat_surj (@b q ) m h'
      rw [Finset.mem_image]
      use τ
      aesop

@[blueprint "lemma:S_card_eq_icc_zero_to_q_sub_one_over_two_card"]
lemma S_card_eq_icc_zero_to_q_sub_one_over_two_card
  : (@S q).card = (Finset.Icc 0 ((q - 1) / 2)).card := by
    rw [← image_of_bitsToNat_of_S_eq_icc_zero_to_q_sub_one_over_two]
    rw [Finset.card_image_of_injective _ bitsToNat_injective]

/-- The lower-half string set `S` has `(q + 1) / 2` elements when `q ≡ 3 (mod 4)`.
This is the cardinality computation used in Theorem 4 of the paper. -/
@[blueprint "lemma:S_card_eq_q_add_one_over_two"]
lemma S_card_eq_q_add_one_over_two (q_h3 : q % 4 = 3)
  : (@S q).card = (q + 1) / 2 := by
    rw [S_card_eq_icc_zero_to_q_sub_one_over_two_card]
    rw [Nat.card_Icc]
    grind

end Elligator.Elligator1
