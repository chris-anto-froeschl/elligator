/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Context
public import Elligator.LegendreSymbol
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Finite fields of odd characteristic

Elligator 1 is stated for a finite field `F` with `Fintype.card F % 4 = 3`; Elligator 2 is
stated for *any* finite field of odd characteristic ([Bernstein2013a], Section 5: "We emphasize
that the characteristic is not required to be 3 modulo 4").

This file collects the field- and quadratic-character facts that hold under the weaker
hypothesis `IsOddCard F`, i.e. `q` odd. Everything here is independent of both Elligator 1 and
Elligator 2 and is phrased in the existing namespaces `Elligator.FiniteFieldBasic` and
`Elligator.LegendreSymbol`, so that it can be used from either development.

## Main results

* `FiniteFieldBasic.two_ne_zero_of_odd_card`, `FiniteFieldBasic.four_ne_zero_of_odd_card`:
  `2` and `4` are invertible in a finite field of odd cardinality.
* `FiniteFieldBasic.neg_ne_self_of_odd_card`: `-a ≠ a` for `a ≠ 0`.
* `LegendreSymbol.χ_eq_one_iff_isSquare_of_odd_card`,
  `LegendreSymbol.χ_eq_neg_one_iff_not_isSquare_of_odd_card`: the two-valuedness of `χ` on
  `F ˣ`, i.e. the description of `χ` used throughout Section 5 of the paper.

## References

See [Bernstein2013a], Sections 3.1 and 5.1.
-/

@[expose] public section

namespace Elligator

variable {F : Type*} [Field F] [Fintype F]

namespace FiniteFieldBasic

/-- A finite field of odd cardinality has odd characteristic. -/
lemma ringChar_ne_two_of_odd_card [IsOddCard F] : ringChar F ≠ 2 := by
  intro hchar
  have hcharP : CharP F 2 := by rw [← hchar]; exact ringChar.charP F
  obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
  have hdvd : (2 : ℕ) ∣ Fintype.card F := by
    rw [show Fintype.card F = 2 ^ (n : ℕ) from by rw [hcard]]
    exact dvd_pow_self 2 n.pos.ne'
  have := card_odd (F := F)
  omega

/-- `2 ≠ 0` in a finite field of odd cardinality. -/
lemma two_ne_zero_of_odd_card [IsOddCard F] : (2 : F) ≠ 0 := by
  intro h
  refine ringChar_ne_two_of_odd_card (F := F) ?_
  have hdvd : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F (ringChar F) 2).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hchar | hchar
  · exact absurd hchar (CharP.char_ne_one F (ringChar F))
  · exact hchar

/-- `4 ≠ 0` in a finite field of odd cardinality. -/
lemma four_ne_zero_of_odd_card [IsOddCard F] : (4 : F) ≠ 0 := by
  have h : (4 : F) = 2 * 2 := by norm_num
  rw [h]
  exact mul_ne_zero two_ne_zero_of_odd_card two_ne_zero_of_odd_card

/-- In odd characteristic a nonzero element differs from its negative. -/
lemma neg_ne_self_of_odd_card [IsOddCard F] {a : F} (ha : a ≠ 0) : -a ≠ a := by
  intro h
  have h2 : (2 : F) * a = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact two_ne_zero_of_odd_card h'
  · exact ha h'

end FiniteFieldBasic

namespace LegendreSymbol

open Elligator.FiniteFieldBasic

variable [DecidableEq F]

/-- Euler's criterion in odd characteristic: `χ a = 1` exactly for the nonzero squares. -/
lemma χ_eq_one_iff_isSquare_of_odd_card [IsOddCard F] {a : F} (a_ne_zero : a ≠ 0) :
    χ a = 1 ↔ IsSquare a := by
  refine ⟨fun h => ?_, χ_a_eq_one a_ne_zero⟩
  rcases quadraticChar_dichotomy a_ne_zero with h' | h'
  · exact (quadraticChar_one_iff_isSquare a_ne_zero).mp h'
  · rw [χ, h'] at h
    exact absurd (by linear_combination -h : (2 : F) = 0) two_ne_zero_of_odd_card

/-- In odd characteristic `χ a = -1` exactly for the non-squares. -/
lemma χ_eq_neg_one_iff_not_isSquare_of_odd_card [IsOddCard F] {a : F} (a_ne_zero : a ≠ 0) :
    χ a = -1 ↔ ¬IsSquare a := by
  constructor
  · intro h hsq
    rw [(χ_eq_one_iff_isSquare_of_odd_card a_ne_zero).mpr hsq] at h
    exact absurd (by linear_combination h : (2 : F) = 0) two_ne_zero_of_odd_card
  · intro hsq
    rcases χ_values (a := a) with h | h | h
    · exact absurd h (χ_a_ne_zero a_ne_zero)
    · exact h
    · exact absurd ((χ_eq_one_iff_isSquare_of_odd_card a_ne_zero).mp h) hsq

/-- The quadratic character of a non-square is `-1`. -/
lemma χ_of_not_isSquare [IsOddCard F] {a : F} (hsq : ¬IsSquare a) : χ a = -1 := by
  have ha : a ≠ 0 := fun h => hsq (h ▸ IsSquare.zero)
  exact (χ_eq_neg_one_iff_not_isSquare_of_odd_card ha).mpr hsq

/-- An element whose quadratic character is not `-1` is a square. -/
lemma isSquare_of_χ_ne_neg_one [IsOddCard F] {a : F} (h : χ a ≠ -1) :
    IsSquare a := by
  by_contra hsq
  exact h (χ_of_not_isSquare hsq)

omit [DecidableEq F] in
/-- For `q ≡ 5 (mod 8)` the element `2` is a non-square, so Elligator 2 may take `u = 2`.

See [Bernstein2013a], Section 5.1. -/
lemma not_isSquare_two_of_card_five_mod_eight (h : Fintype.card F % 8 = 5) :
    ¬IsSquare (2 : F) := by
  rw [FiniteField.isSquare_two_iff]
  omega

/-- For `q ≡ 1 (mod 4)` the element `-1` is a square, so `χ (-1) = 1`.

This is the point where Elligator 2 differs from Elligator 1: see [Bernstein2013a], Theorem 5,
last paragraph ("`χ(±1) = 1`"). -/
lemma χ_neg_one_of_card_one_mod_four [IsCardOneModFour F] : χ (-1 : F) = 1 := by
  have hsq : IsSquare (-1 : F) := by
    refine FiniteField.isSquare_neg_one_iff.mpr ?_
    have := card_mod_four_eq_one (F := F)
    omega
  exact χ_a_eq_one (by simp) hsq

end LegendreSymbol

end Elligator
