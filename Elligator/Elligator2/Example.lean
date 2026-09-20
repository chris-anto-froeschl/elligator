/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public meta import Elligator.Elligator2.Map
public import Elligator.Elligator2.InvertedMap
public meta import Elligator.Elligator2.StringEncoding
public meta import Mathlib.Algebra.Field.Defs
public meta import Mathlib.Algebra.Field.ZMod

/-!
# Computational sanity checks for Elligator 2

This is the Elligator 2 counterpart of `Elligator.Elligator1.Example`: brute-force numeric
evidence, complementary to the actual proofs.

The example uses the field with `13` elements, the curve `y ^ 2 = x ^ 3 + x ^ 2 + 2x`, the
non-square `u = 2` and the square-root function that returns the smallest square root. Here
`q ≡ 1 (mod 4)` and `A ^ 2 - 4B = -7` is a non-square, so the hypotheses of the last part of
Theorem 5 and of Theorem 8 hold and `ψ` is defined on all of `F_13`.
-/

@[expose] public section

namespace Elligator.Elligator2.Example

open Elligator.LegendreSymbol
open Elligator.Primitives.ECC
open Elligator.StringEncoding
open Elligator.Elligator2.CurveParameters

/-! ### The field, the curve and the parameters -/

/-- The field with 13 elements. -/
abbrev F13 : Type := ZMod 13

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

lemma card_F13 : Fintype.card F13 = 13 := ZMod.card 13

instance : IsCardOneModFour F13 := ⟨by rw [card_F13]⟩

instance : IsPrimeCard F13 := ⟨by rw [card_F13]; exact Nat.prime_iff.mp (by decide)⟩

/-- The square-root function of `F13` returning the smallest square root, given by the table of
squares `1, 4, 9, 3, 12, 10` of `1, 2, 3, 4, 5, 6`. -/
def sqrt13 (a : F13) : F13 :=
  match a.val with
  | 0 => 0
  | 1 => 1
  | 4 => 2
  | 9 => 3
  | 3 => 4
  | 12 => 5
  | 10 => 6
  | _ => 0

/-- The Elligator 2 parameters `A = 1`, `B = 2`, `u = 2` over `F13`. -/
def P13 : ParamData F13 := ⟨1, 2, 2, sqrt13⟩

instance : IsSqrtFun P13.sqrt := ⟨by decide⟩

instance : IsRegularABParam P13.A P13.B := ⟨by decide⟩

instance : IsNonsquareParam P13.u := ⟨by decide⟩

instance : IsNonsquareDisc P13.A P13.B := ⟨by decide⟩

/-! ### Decoding: `ψ : R → E(F13)`, Theorem 5 and Definition 6 -/

-- Here `R` is all of `F13`, by the last part of Theorem 5.
lemma R13_eq_univ : P13.R = Set.univ := R_eq_univ P13

-- `ψ` at `0` is the point of order two, and at a nonzero input it is `(x, y)`.
#eval P13.ψ 0
#eval P13.ψ 3
#eval P13.ψ 5

-- Theorem 7.1's sign ambiguity, checked computationally: `ψ r = ψ (-r)`.
#eval decide (P13.ψ 3 = P13.ψ (-3))

-- Every decoded point is genuinely on the curve, by Theorem 5.
lemma decode_three_on_curve : (P13.ψ 3).2 ^ 2 = P13.rhs (P13.ψ 3).1 :=
  ψ_mem_EOverF P13 (mem_R_of_nonsquare_disc P13 3)

/-! ### Encoding as strings, Theorem 8 -/

/-- `mkBits n` reads off the bits of `n`, giving an element of `Fin (b 13) → Bool`. -/
def mkBits (n : ℕ) : Fin (@b (Fintype.card F13)) → Bool := fun i => n.testBit i.val

lemma b13_eq : (@b 13) = 3 := by decide

-- `S` has `(q + 1) / 2 = 7` elements, per Theorem 8.
#eval (@S 13).card

lemma S13_card : (@S (Fintype.card F13)).card = 7 := by
  have h := S_card (F := F13)
  rw [card_F13] at h
  exact h

/-- The bit strings of value at most `6` are exactly the admissible ones for `q = 13`. -/
lemma mkBits_mem_S (n : ℕ) (h : n < 7) : mkBits n ∈ @S (Fintype.card F13) := by
  unfold S mkBits bitsToNat
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  interval_cases n <;> decide

-- The string `101` (binary value `5`), encoded via `ι` and evaluated by the compiler.
#eval (ι P13 ⟨mkBits 5, mkBits_mem_S 5 (by norm_num)⟩).val

-- `ι` is injective on `S`, per Theorem 8.
lemma encode_injective_showcase :
    Function.Injective (fun ρ : @S (Fintype.card F13) => ι P13 ρ) :=
  ι_injective P13

end Elligator.Elligator2.Example

end
