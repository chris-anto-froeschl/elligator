/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Elligator.Elligator1.Curve1174Prime
public import Elligator.Elligator1.DecodingFunction
public import Elligator.Elligator1.InvertedMap
public import Elligator.Elligator1.StringEncoding
public meta import Mathlib.Data.ZMod.Defs

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
open Elligator.PrimalityCertificate
open Elligator.Elligator1

/-! ### The field and parameter -/

abbrev F7 : Type := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem q7_prime : Nat.Prime 7 := by norm_num
theorem F7_isPrimePow : IsPrimePow (7 : ℕ) := q7_prime.isPrimePow
theorem card_F7 : Fintype.card F7 = 7 := ZMod.card 7
theorem F7_mod_four : (7 : ℕ) % 4 = 3 := by decide

def s7 : F7 := 2
theorem s7_ne_zero : s7 ≠ 0 := by decide
theorem s7_sq_ne_pm_two : (s7 ^ 2 - 2) * (s7 ^ 2 + 2) ≠ 0 := by decide

/-! ### Decoding: `ϕ : F7 → E(F7)`, Definition 2 -/

-- `ϕ` at a nonexceptional point, evaluated by the compiler.
#eval (ϕ (3 : F7) s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four).val

-- The two exceptional inputs both hit the neutral point `(0, 1)`, per Definition 2.
#eval (ϕ (1 : F7) s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four).val
#eval (ϕ (-1 : F7) s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four).val

-- Theorem 3's sign ambiguity, checked computationally: `ϕ t = ϕ (-t)`.
#eval decide
  ((ϕ (3 : F7) s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four).val
    = (ϕ (-3 : F7) s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four).val)

-- Every decoded point is genuinely on the curve
theorem decode_three_on_curve :
  let P := (ϕ (3 : F7) s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four).val
  P.1 ^ 2 + P.2 ^ 2 = 1 + d s7 * P.1 ^ 2 * P.2 ^ 2 := by
    have := (ϕ (3 : F7) s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four).prop
    unfold EOverF at this
    simpa using this

/-- `mkBits n` reads off the bits of `n`, giving an element of `Fin (b 7) → Bool` for any `n`
without needing to know `b 7`'s concrete value up front. -/
def mkBits (n : ℕ) : Fin (@b 7) → Bool := fun i => n.testBit i.val

theorem b7_eq : (@b 7) = 2 := by decide

/-- All four `2`-bit strings land in `S` for `q = 7`, since `(7-1)/2 = 3` is the largest
possible `2`-bit value. -/
theorem mkBits_mem_S (n : ℕ) (h : n < 4) : mkBits n ∈ @S 7 := by
  unfold S mkBits bitsToNat
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  interval_cases n <;> decide

-- `S` has all `4` of the `2`-bit strings, matching `S_card`'s `(q+1)/2 = 4` for `q = 7`.
#eval (@S 7).card
theorem S7_card : (@S 7).card = 4 := S_card F7_mod_four

-- The string `11` (binary value `3`), encoded via `ι` and evaluated by the compiler.
#eval (ι ⟨mkBits 3, mkBits_mem_S 3 (by norm_num)⟩
      s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four).val

-- `ι` is injective on `S`, per Theorem 4.2
theorem encode_injective_showcase : Function.Injective
  (fun τ : @S 7 => ι τ s7_ne_zero s7_sq_ne_pm_two card_F7 F7_isPrimePow F7_mod_four) := by
    have := ι_injective s7_ne_zero s7_sq_ne_pm_two card_F7 (by decide) F7_mod_four
    simpa using this

end Elligator.Elligator1.Example

end
