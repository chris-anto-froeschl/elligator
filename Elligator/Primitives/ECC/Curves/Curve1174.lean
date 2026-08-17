/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module
public import Elligator.Primitives.ECC.Curves.Curve1174Prime
public import Elligator.Primitives.ECC.EdwardsCurve
public import Elligator.LegendreSymbol
public meta import Mathlib.Data.ZMod.Defs

/-!
# Curve1174

This file collects the data of the elliptic curve Curve1174 of [bernstein2013a], Section 4: its
base field, its Edwards model, the fact that its Edwards coefficient is a non-square, and the base
point of Section 4.1.

Nothing here mentions Elligator: Curve1174 is described directly as the complete Edwards curve
$$ x ^ 2 + y ^ 2 = 1 - 1174 x ^ 2 y ^ 2 $$
over the prime field $\mathbb{F}_q$ with $q = 2 ^ {251} - 9$, using only the general Edwards curve
API of `Elligator.ECCPrimitives.EdwardsCurve`. That the Elligator 1 construction reproduces exactly
this curve from its parameter `s` is the subject of `Elligator.Elligator1.Curve1174`.
All numerical statements are checked by kernel computation. Field elements of `F1174` are `Fin`
residues, so `decide` evaluates ring operations directly; the two places where an exponent is
astronomically large (the primality certificate and the quadratic character) go through the binary
modular exponentiation of `Elligator.PrimalityCertificate`.

## Main definitions

* `q1174`, `F1174`: the characteristic `q = 2 ^ 251 - 9` and the base field `F_q`.
* `curve1174`: Curve1174 as the Edwards curve with coefficient `-1174`.
* `basePoint1174`: the base point `(4/V, 3/5)` of [bernstein2013a], Section 4.1.

## Main results

* `prime_q1174`, `card_F1174`, `q1174_mod_four`: `F1174` is a field with `q = 2 ^ 251 - 9`
  elements and `q ≡ 3 (mod 4)`.
* `curve1174_equation`, `curve1174_isValid`: the defining equation and nonsingularity of the model.
* `chi_neg1174_eq_neg_one`, `neg1174_not_isSquare`: `-1174` is a non-square in `F1174`, which is
  the completeness criterion quoted in Section 4.1.
* `basePointV_montgomery`, `basePoint1174_mem_affinePoints`: the point `(U, V) = (4, V)` of
  Section 4.1 lies on the Montgomery model, and the corresponding point `(4/V, 3/5)` lies on
  Curve1174.

## References
See [bernstein2013a], Section 4.
-/

@[expose] public section

namespace Elligator.Primitives.ECC.Curves.Curve1174

open Elligator.LegendreSymbol
open Elligator.Primitives.PrimalityCertificate

set_option maxRecDepth 20000

/-! ### The base field -/
/-- The characteristic of the Curve1174 base field, `q = 2 ^ 251 - 9`. -/
@[blueprint "def:q1174"
  (title := "The Curve1174 characteristic $q$")
  (statement := /--
  Curve1174 is defined over $\mathbb{F}_q$ with
  $$
  q = 2^{251} - 9 .
  $$
  -/)]
def q1174 : ℕ := 3618502788666131106986593281521497120414687020801267626233049500247285301239

/-- The numeral defining `q1174` is `2 ^ 251 - 9`. -/
theorem q1174_eq_two_pow : q1174 = 2 ^ 251 - 9 := by
  unfold q1174
  norm_num
@[blueprint "lemma:q1174-prime"
  (title := "$q$ is prime")
  (statement := /--
  The number $q = 2^{251} - 9$ is prime.
  -/)]
theorem prime_q1174 : Nat.Prime q1174 := q1174_prime

instance : Fact (Nat.Prime q1174) := ⟨prime_q1174⟩
instance : NeZero q1174 := ⟨by trivial⟩

/-- The Curve1174 base field `F_q` with `q = 2 ^ 251 - 9`. -/
@[blueprint "def:F1174"
  (title := "The Curve1174 base field")
  (statement := /--
  Let $\mathbb{F}_q$ be the prime field with $q = 2^{251} - 9$ elements.
  -/)]
abbrev F1174 : Type := ZMod q1174

/-- `F1174` has `q1174` elements. -/
theorem card_F1174 : Fintype.card F1174 = q1174 := ZMod.card q1174

/-- `q ≡ 3 (mod 4)`; among other things this is one of the standing hypotheses of Elligator 1. -/
@[blueprint "lemma:q1174-mod-four"
  (title := "$q \\equiv 3 \\pmod 4$")
  (statement := /--
  The characteristic satisfies $q \equiv 3 \pmod 4$.
  -/)]
theorem q1174_mod_four : q1174 % 4 = 3 := by decide

/-- `q1174` is a prime power. -/
theorem q1174_isPrimePow : IsPrimePow q1174 := prime_q1174.prime.isPrimePow

/-! ### The curve -/
/-- Curve1174, the complete Edwards curve with coefficient `-1174` over `F1174`. -/
@[blueprint "def:curve1174"
  (title := "Curve1174")
  (statement := /--
  Curve1174 is the complete Edwards curve
  $$
  x ^ 2 + y ^ 2 = 1 - 1174 x ^ 2 y ^ 2
  $$
  over $\mathbb{F}_q$.
  -/)]
def curve1174 : TwistedEdwardsCurve F1174 := edwardsCurve (-1174 : F1174)

/-- The defining equation of Curve1174: `x ^ 2 + y ^ 2 = 1 - 1174 x ^ 2 y ^ 2`. -/
theorem curve1174_equation (x y : F1174) :
    curve1174.Equation x y ↔ x ^ 2 + y ^ 2 = 1 - 1174 * x ^ 2 * y ^ 2 := by
  rw [curve1174, edwardsCurve_equation_iff]
  ring_nf

/-- Curve1174 is a valid (nonsingular) Edwards model. -/
theorem curve1174_isValid : curve1174.IsValid := by
  rw [curve1174, edwardsCurve_isValid_iff]
  exact ⟨by decide, by decide⟩
/-! ### The Edwards coefficient is a non-square -/
/-- The quadratic character of the Edwards coefficient is `-1`. -/
@[blueprint "lemma:chi-d1174"
  (title := "$\\chi(-1174) = -1$")
  (statement := /--
  The quadratic character of the Edwards coefficient satisfies $\chi(-1174) = -1$.
  -/)]
theorem chi_neg1174_eq_neg_one : χ (-1174 : F1174) = -1 := by
  have hneg :
    ((3618502788666131106986593281521497120414687020801267626233049500247285300065 : ℕ) : F1174)
    = -1174 := by decide
  have hone :
    ((3618502788666131106986593281521497120414687020801267626233049500247285301238 : ℕ) : F1174)
    = -1 := by decide
  rw [χ_eq_pow (-1174 : F1174) card_F1174 q1174_mod_four, ← hneg, ← hone]
  exact natCast_pow_eq_natCast _ _ _ 256 (by decide) (by decide)

/-- `-1174` is not a square in `F1174`; by [bernstein2013a], Section 4.1 this is what makes
Curve1174 a complete Edwards curve. -/
@[blueprint "thm:d1174-nonsquare"
  (title := "$-1174$ is a non-square")
  (statement := /--
  The coefficient $-1174$ is a non-square in $\mathbb{F}_q$; this is the criterion of
  [bernstein2013a, Theorem 3.3] making Curve1174 a complete Edwards curve.
  -/)]
theorem neg1174_not_isSquare : ¬IsSquare (-1174 : F1174) := by
  intro hsq
  have hne : (-1174 : F1174) ≠ 0 := by decide
  have h1 : χ (-1174 : F1174) = 1 := (χ_eq_one_iff_isSquare hne card_F1174 q1174_mod_four).2 hsq
  rw [chi_neg1174_eq_neg_one] at h1
  exact absurd h1 (by decide)

/-! ### The base point -/
/-- The `V`-coordinate of the base point of Section 4.1 on the Montgomery model
`(4/1175) V ^ 2 = U ^ 3 + (4/1175 - 2) U ^ 2 + U`, at `U = 4`. -/
def basePointV : F1174 := 19225777642111670230408712442205514783403012708409058383774613284963344096
/-- The base point `(x, y) = (4/V, 3/5)` of Curve1174 given in [bernstein2013a], Section 4.1. -/
@[blueprint "def:basePoint1174"
  (title := "The Curve1174 base point")
  (statement := /--
  The base point of [bernstein2013a], Section 4.1 is $(x, y) = (4/V, 3/5)$, where $V$ is the
  $V$-coordinate of the point of order $4p_1$ on the Montgomery model at $U = 4$.
  -/)]
def basePoint1174 : F1174 × F1174 :=
  (1732556372810548511963925612826482930760269237516198826254492409990286433383,
   2171101673199678664191955968912898272248812212480760575739829700148371180744)

/-- The point `(U, V) = (4, V)` of [bernstein2013a], Section 4.1 lies on the Montgomery model
`(4/1175) V ^ 2 = U ^ 3 + (4/1175 - 2) U ^ 2 + U` to which Curve1174 is birationally equivalent. -/
@[blueprint "lemma:basePointMontgomery"
  (title := "The Montgomery base point")
  (statement := /--
  The point $(U, V) = (4, V)$ lies on the Montgomery curve
  $$
  (4/1175) V ^ 2 = U ^ 3 + (4/1175 - 2) U ^ 2 + U .
  $$
  -/)]
theorem basePointV_montgomery :
    (4 / 1175 : F1174) * basePointV ^ 2 = 4 ^ 3 + (4 / 1175 - 2) * 4 ^ 2 + 4 := by
  have h : (1175 : F1174) ≠ 0 := by decide
  have key : (4 / 1175 : F1174)
    = 3276669759268734891773391703437338669039342119261743620691033760223924732356 := by
      rw [div_eq_iff h]
      decide
  rw [key]
  decide

/-- The first coordinate of the base point is `4/V`. -/
theorem basePoint1174_fst : basePoint1174.1 * basePointV = 4 := by decide

/-- The second coordinate of the base point is `3/5`. -/
theorem basePoint1174_snd : basePoint1174.2 * 5 = 3 := by decide

/-- The base point of Section 4.1 lies on Curve1174. -/
@[blueprint "lemma:basePoint1174"
  (title := "The base point lies on Curve1174")
  (statement := /--
  The point $(4/V, 3/5)$ satisfies the Curve1174 equation.
  -/)]
theorem basePoint1174_mem_affinePoints : basePoint1174 ∈ curve1174.affinePoints := by
  rw [TwistedEdwardsCurve.affinePoints, Set.mem_ofPred_eq, curve1174_equation]
  decide

end Elligator.Primitives.ECC.Curves.Curve1174
