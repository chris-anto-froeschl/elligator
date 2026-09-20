/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.OddCharacteristic

/-!
# Square-root functions

[Bernstein2013a], Section 5.1, parametrizes Elligator 2 by a *square-root function* for `F`, that
is a function `√ : F² → F` with `√(a ^ 2) ∈ {a, -a}` for each `a ∈ F`, where `F²` denotes the set
of squares. Such a function is completely described by its image `√(F²)`, and the paper's
inversion formula (Theorem 7) branches on whether the `y`-coordinate of a point lies in `√(F²)`.

A square-root function is modelled here by a total function `sqrt : F → F` satisfying the class
`IsSqrtFun`, which only constrains its values on squares. The predicate `IsSqrtValue` describes
the image `√(F²)`.

For `q ≡ 3 (mod 4)` the paper takes the principal square root, and this file verifies that
`principalSqrt`, the `(q + 1) / 4`-th power map of Section 3.1, is indeed a square-root function.

## Main results

* `sq_sqrt`: `sqrt w ^ 2 = w` for every square `w`.
* `sqrt_sq_eq_or_eq_neg`: `sqrt (a ^ 2) = a` or `sqrt (a ^ 2) = -a`.
* `isSqrtValue_iff_mem_range`: `IsSqrtValue sqrt y` holds exactly when `y` lies in the image
  of the square-root function.
* `principalSqrt_isSqrtFun`: for `q ≡ 3 (mod 4)` the principal square root is a square-root
  function, so the Elligator 1 setting is a special case of the Elligator 2 setting.

## References

See [Bernstein2013a], Sections 3.1 and 5.1.
-/

@[expose] public section

namespace Elligator.SquareRootFunction

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F]
variable (sqrt : F → F) [IsSqrtFun sqrt]

/-- A square-root function returns one of the two square roots of `a ^ 2`. -/
lemma sqrt_sq_eq_or_eq_neg (a : F) : sqrt (a ^ 2) = a ∨ sqrt (a ^ 2) = -a :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (sq_sqrt_sq (sqrt := sqrt) a)

/-- On a square `w`, the square-root function really does return a square root of `w`. -/
lemma sq_sqrt {w : F} (hw : IsSquare w) : sqrt w ^ 2 = w := by
  obtain ⟨a, rfl⟩ := hw
  rw [← sq]
  exact sq_sqrt_sq a

lemma sqrt_zero : sqrt (0 : F) = 0 := by
  have h : sqrt (0 : F) ^ 2 = 0 := sq_sqrt sqrt IsSquare.zero
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

/-- A square root of a nonzero square is nonzero. -/
lemma sqrt_ne_zero {w : F} (hw : IsSquare w) (hw_ne_zero : w ≠ 0) : sqrt w ≠ 0 := by
  intro h
  exact hw_ne_zero (by rw [← sq_sqrt sqrt hw, h]; ring)

/-- The predicate describing the image `√(F²)` of the square-root function, i.e. the paper's
condition `y ∈ √(F²)` in the inversion formula of Theorem 7. -/
def IsSqrtValue (y : F) : Prop := sqrt (y ^ 2) = y

instance [DecidableEq F] (y : F) : Decidable (IsSqrtValue sqrt y) := by
  unfold IsSqrtValue; infer_instance

/-- `IsSqrtValue sqrt y` holds exactly when `y` is a value of the square-root function. -/
lemma isSqrtValue_iff_mem_range (y : F) :
    IsSqrtValue sqrt y ↔ ∃ a : F, sqrt (a ^ 2) = y := by
  constructor
  · intro h
    exact ⟨y, h⟩
  · rintro ⟨a, rfl⟩
    unfold IsSqrtValue
    rw [sq_sqrt_sq a]

/-- If `y` is not a value of the square-root function, then `sqrt (y ^ 2)` is `-y`. -/
lemma sqrt_sq_eq_neg_of_not_isSqrtValue {y : F} (h : ¬IsSqrtValue sqrt y) :
    sqrt (y ^ 2) = -y :=
  (sqrt_sq_eq_or_eq_neg sqrt y).resolve_left h

section principal

variable [Fintype F]

/-- The principal square root of [Bernstein2013a], Section 3.1: for `q ≡ 3 (mod 4)` the
`(q + 1) / 4`-th power map is a square-root function. -/
def principalSqrt (a : F) : F := a ^ ((Fintype.card F + 1) / 4)

lemma principalSqrt_sq [DecidableEq F] [IsCardThreeModFour F] (a : F) :
    principalSqrt (a ^ 2) = χ a * a :=
  b_pow_q_add_one_div_four_eq_χ_of_a_mul_a card_mod_four

instance principalSqrt_isSqrtFun [IsCardThreeModFour F] :
    IsSqrtFun (principalSqrt : F → F) where
  sq_sqrt_sq a := by
    classical
    rw [principalSqrt_sq a, mul_pow]
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [χ_of_a_even_pow_n_eq_one ha ⟨2, even_two⟩, one_mul]

end principal

end Elligator.SquareRootFunction
