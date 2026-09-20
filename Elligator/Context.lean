/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Basic
public import Elligator.FiniteFieldBasic

/-!
# Bundled data and hypotheses for Elligator

Almost every statement of the Elligator 1 development repeats the same variables and the same
standing hypotheses:

* a finite field `F` whose cardinality `q` satisfies `q % 4 = 3`,
* a curve parameter `s`, sometimes with `s ≠ 0`, sometimes with `(s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0`,
* an input `t ∉ {1, -1}` or a point `P` of `E(F)`.

This file provides two independent mechanisms for getting rid of this repetition:

1. *the variables are bundled* into a small inheritance hierarchy of `structure`s carrying data
   only (`ParamData`, `InputData`, `MapData`, `PointData`), which is what makes dot notation such
   as `M.u`, `M.v`, `M.X` available;
2. *the hypotheses are unbundled* into one `class` per hypothesis (`IsCardThreeModFour`,
   `IsPrimeCard`, `IsNonzeroParam`, `IsRegularParam`), which a statement lists individually and
   which are found by instance resolution instead of being passed by hand.
-/

@[expose] public section

namespace Elligator

variable {F : Type*} [Field F]

/-- The base field has cardinality `q ≡ 3 (mod 4)`. -/
class IsCardThreeModFour (F : Type*) [Fintype F] : Prop where
  /-- The cardinality of `F` is congruent to `3` modulo `4`. -/
  card_mod_four : Fintype.card F % 4 = 3

/-- The base field has cardinality `q ≡ 1 (mod 4)`.

This is the extra assumption of [Bernstein2013a], Theorem 5 (last part) and Theorem 8, under
which the Elligator 2 map is defined on all of `F`. -/
class IsCardOneModFour (F : Type*) [Fintype F] : Prop where
  /-- The cardinality of `F` is congruent to `1` modulo `4`. -/
  card_mod_four_eq_one : Fintype.card F % 4 = 1

/-- The base field has odd cardinality, i.e. odd characteristic.

This is the standing hypothesis of [Bernstein2013a], Section 5: Elligator 2 works over every
finite field of odd characteristic, and in particular does not require `q % 4 = 3`. -/
class IsOddCard (F : Type*) [Fintype F] : Prop where
  /-- The cardinality of `F` is odd. -/
  card_odd : Fintype.card F % 2 = 1

/-- The base field has prime cardinality; this is the extra assumption of Theorem 4. -/
class IsPrimeCard (F : Type*) [Fintype F] : Prop where
  /-- The cardinality of `F` is prime. -/
  card_prime : Prime (Fintype.card F)

/-- The curve parameter `s` is nonzero. -/
class IsNonzeroParam {F : Type*} [Field F] (s : F) : Prop where
  /-- The parameter `s` is nonzero. -/
  s_ne_zero : s ≠ 0

/-- The curve parameter `s` satisfies `s ^ 2 ≠ ± 2`. -/
class IsRegularParam {F : Type*} [Field F] (s : F) : Prop where
  /-- The parameter `s` satisfies `(s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0`. -/
  s_sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0

/-- The parameter `u` is a non-square; this is the parameter of Elligator 2. -/
class IsNonsquareParam {F : Type*} [Field F] (u : F) : Prop where
  /-- The parameter `u` is not a square. -/
  u_nonsquare : ¬IsSquare u

/-- `sqrt` is a *square-root function* in the sense of [Bernstein2013a], Section 5.1: a function
defined on the squares of `F` with `sqrt (a ^ 2) ∈ {a, -a}` for every `a`.

The paper's `√ : F² → F` is modelled here by a total function `F → F`, of which only the values
on squares are constrained; this is harmless since Elligator 2 never evaluates it elsewhere. -/
class IsSqrtFun {F : Type*} [Field F] (sqrt : F → F) : Prop where
  /-- `sqrt (a ^ 2)` is a square root of `a ^ 2`, i.e. `sqrt (a ^ 2) ∈ {a, -a}`. -/
  sq_sqrt_sq : ∀ a : F, sqrt (a ^ 2) ^ 2 = a ^ 2

export IsCardThreeModFour (card_mod_four)
export IsCardOneModFour (card_mod_four_eq_one)
export IsOddCard (card_odd)
export IsPrimeCard (card_prime)
export IsNonzeroParam (s_ne_zero)
export IsRegularParam (s_sq_ne_pm_two)
export IsNonsquareParam (u_nonsquare)
export IsSqrtFun (sq_sqrt_sq)

/-- A field with `q ≡ 3 (mod 4)` has odd cardinality. -/
instance (priority := 100) IsCardThreeModFour.toIsOddCard
    (F : Type*) [Fintype F] [IsCardThreeModFour F] : IsOddCard F :=
  ⟨by have := card_mod_four (F := F); omega⟩

/-- A field with `q ≡ 1 (mod 4)` has odd cardinality. -/
instance (priority := 100) IsCardOneModFour.toIsOddCard
    (F : Type*) [Fintype F] [IsCardOneModFour F] : IsOddCard F :=
  ⟨by have := card_mod_four_eq_one (F := F); omega⟩

/-- The curve parameter `s` of Theorem 1, bundled.

No hypotheses: the quantities `c`, `r`, `d` and the curve `E` are defined for every `s`. -/
structure ParamData (F : Type*) [Field F] where
  /-- The Elligator 1 curve parameter. -/
  s : F

/-- An admissible input `t ∉ {1, -1}` of the Elligator 1 map, bundled.

The two disequalities are data rather than hypotheses: they are exactly the subtype
`{n : F // n ≠ 1 ∧ n ≠ -1}` on which the unbundled definitions are given, i.e. the domain of `u`. -/
structure InputData (F : Type*) [Field F] where
  /-- The input of the Elligator 1 map. -/
  t : F
  /-- The input is not `1`. -/
  t_ne_one : t ≠ 1
  /-- The input is not `-1`. -/
  t_ne_neg_one : t ≠ -1

/-- A curve parameter together with an admissible input: the data of Theorem 1. -/
structure MapData (F : Type*) [Field F] extends ParamData F, InputData F

/-- A curve parameter together with a point of the plane: the data of Theorem 3. -/
structure PointData (F : Type*) [Field F] extends ParamData F where
  /-- The point. -/
  P : F × F

namespace InputData

variable (I : InputData F)

/-- The input, as an element of the subtype `{n : F // n ≠ 1 ∧ n ≠ -1}` on which the unbundled
definitions are given. -/
def tSub : {n : F // n ≠ 1 ∧ n ≠ -1} := ⟨I.t, I.t_ne_one, I.t_ne_neg_one⟩

/-- The input `t` replaced by `-t`. -/
def neg : InputData F where
  t := -I.t
  t_ne_one := (FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one I.tSub).1
  t_ne_neg_one := (FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one I.tSub).2

end InputData

namespace ParamData

/-- The `MapData` assembled from a curve parameter and an admissible input `t ∉ {1, -1}`. -/
@[reducible]
def withInput (D : ParamData F) (t : F) (t_ne_one : t ≠ 1) (t_ne_neg_one : t ≠ -1) : MapData F :=
  { toParamData := D, t := t, t_ne_one := t_ne_one, t_ne_neg_one := t_ne_neg_one }

end ParamData

namespace MapData

variable (M : MapData F)

/-- The input `t` replaced by `-t`, the curve parameter kept. -/
def neg : MapData F := { M with toInputData := M.toInputData.neg }

/-- Negating the input does not change the curve parameter. -/
lemma neg_s : M.neg.s = M.s := rfl

/-- Negating the input negates it. -/
lemma neg_t : M.neg.t = -M.t := rfl

instance instIsNonzeroParamNeg [IsNonzeroParam M.s] : IsNonzeroParam M.neg.s :=
  ⟨s_ne_zero (s := M.s)⟩

instance instIsRegularParamNeg [IsRegularParam M.s] : IsRegularParam M.neg.s :=
  ⟨s_sq_ne_pm_two (s := M.s)⟩

end MapData

end Elligator
