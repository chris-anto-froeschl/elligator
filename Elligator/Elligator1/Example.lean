/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public meta import Elligator.Elligator1.Map
public import Elligator.Elligator1.InvertedMap
public import Elligator.Primitives.ECC.Curves.Curve1174Prime
public meta import Elligator.Elligator1.StringEncoding
public meta import Mathlib.Algebra.Field.Defs
public meta import Mathlib.Algebra.Field.ZMod

/-!
# Computational sanity checks

This plays the same role for the Lean development that the Sage scripts at
<https://elligator.cr.yp.to/thm1.sage> and <https://elligator.cr.yp.to/thm4.sage> play for the
original paper: brute-force numeric evidence, complementary to the actual proofs.

TODO order this a bit and find meaningful examples to check, rather than just dumping a bunch of
random computations.
-/

@[expose] public section

namespace Elligator.Elligator1.Example

open Elligator.LegendreSymbol
open Elligator.Primitives.PrimalityCertificate
open Elligator.Primitives.ECC
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.OutputCoordinates

/-! ### The field and parameter -/

/-- The field with 7 elements -/
abbrev F7 : Type := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma q7_prime : Nat.Prime 7 := by norm_num
lemma F7_isPrimePow : IsPrimePow (7 : ℕ) := q7_prime.isPrimePow
lemma card_F7 : Fintype.card F7 = 7 := ZMod.card 7
lemma F7_mod_four : (7 : ℕ) % 4 = 3 := by decide

/-- A non-zero element of `F7` -/
def s7 : F7 := 2
lemma s7_ne_zero : s7 ≠ 0 := by decide
lemma s7_sq_ne_pm_two : (s7 ^ 2 - 2) * (s7 ^ 2 + 2) ≠ 0 := by decide

/-! ### Decoding: `ϕ : F7 → E(F7)`, Definition 2 -/

/-- The Elligator 1 parameter `s7` of `F7`, bundled. -/
def D7 : ParamData F7 := ⟨s7⟩

instance : IsCardThreeModFour F7 := ⟨by rw [card_F7]⟩

instance : IsPrimeCard F7 := ⟨by rw [card_F7]; exact Nat.prime_iff.mp q7_prime⟩

instance : IsNonzeroParam D7.s := ⟨s7_ne_zero⟩

instance : IsRegularParam D7.s := ⟨s7_sq_ne_pm_two⟩

-- `ϕ` at a nonexceptional point, evaluated by the compiler.
#eval (D7.ϕ (3 : F7)).val

-- The two exceptional inputs both hit the neutral point `(0, 1)`, per Definition 2.
#eval (D7.ϕ (1 : F7)).val
#eval (D7.ϕ (-1 : F7)).val

-- Theorem 3's sign ambiguity, checked computationally: `ϕ t = ϕ (-t)`.
#eval decide ((D7.ϕ (3 : F7)).val = (D7.ϕ (-3 : F7)).val)

-- Every decoded point is genuinely on the curve
lemma decode_three_on_curve :
    let P := (D7.ϕ (3 : F7)).val
    P.1 ^ 2 + P.2 ^ 2 = 1 + D7.d * P.1 ^ 2 * P.2 ^ 2 := by
  have := (D7.ϕ (3 : F7)).prop
  rwa [mem_EOverF_iff] at this

/-- `mkBits n` reads off the bits of `n`, giving an element of `Fin (b 7) → Bool` for any `n`
without needing to know `b 7`'s concrete value up front. -/
def mkBits (n : ℕ) : Fin (@b (Fintype.card F7)) → Bool := fun i => n.testBit i.val

lemma b7_eq : (@b 7) = 2 := by decide

/-- All four `2`-bit strings land in `S` for `q = 7`, since `(7-1)/2 = 3` is the largest
possible `2`-bit value. -/
lemma mkBits_mem_S (n : ℕ) (h : n < 4) : mkBits n ∈ @S (Fintype.card F7) := by
  unfold S mkBits bitsToNat
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  interval_cases n <;> decide

-- `S` has all `4` of the `2`-bit strings, matching `S_card`'s `(q+1)/2 = 4` for `q = 7`.
#eval (@S 7).card

lemma S7_card : (@S (Fintype.card F7)).card = 4 := by
  have h := S_card (F := F7)
  rw [card_F7] at h
  exact h

-- The string `11` (binary value `3`), encoded via `ι` and evaluated by the compiler.
#eval (ι D7 ⟨mkBits 3, mkBits_mem_S 3 (by norm_num)⟩).val

-- `ι` is injective on `S`, per Theorem 4.2
lemma encode_injective_showcase :
    Function.Injective (fun τ : @S (Fintype.card F7) => ι D7 τ) :=
  ι_injective D7

end Elligator.Elligator1.Example

end
