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
# Curve1174

This file instantiates the general Elligator 1 development at the concrete curve of
[bernstein2013a], Section 4: Curve1174, the complete Edwards curve

$$ x^2 + y^2 = 1 - 1174 x^2 y^2 $$

over the prime field $\mathbb{F}_q$ with $q = 2^{251} - 9$.

Following the paper, the curve is not given by its coefficient but produced by the Elligator 1
construction from the parameter

$$ s = 1806494121122717992522804053500797229648438766985538871240722010849934886421, $$

and the resulting coefficient `d s` is shown to be exactly `-1174`.

All numerical statements are checked by kernel computation. Field elements of `F1174` are `Fin`
residues, so `decide` evaluates ring operations directly; the two places where an exponent is
astronomically large (the primality certificate and the quadratic character) go through the binary
modular exponentiation of `Elligator.PrimalityCertificate`.

## Main results

* `q1174_prime`, `card_F1174`, `q1174_mod_four`: `F1174` is a field with `q = 2^251 - 9`
  elements and `q ≡ 3 (mod 4)`, so it satisfies the standing hypotheses of Elligator 1.
* `s1174_ne_zero`, `s1174_sq_ne_pm_two`: the parameter `s` satisfies the hypotheses of Theorem 1.
* `c1174_eq`, `r1174_eq`: the values of the derived parameters `c = 2/s^2` and `r = c + 1/c`.
* `d1174_eq`: `d = -(c + 1)^2/(c - 1)^2 = -1174`, i.e. the Elligator 1 curve for `(q, s)` is
  Curve1174.
* `chi_d1174_eq_neg_one`, `d1174_not_isSquare`: `-1174` is a non-square in `F1174`, which is the
  completeness criterion quoted in Section 4.1.
* `decode1174_mem_affinePoints`, `decode1174_equation`: Theorem 1 and Definition 2 for Curve1174.
* `decode1174_neg`, `decode1174_preimages`: Theorem 3 for Curve1174.
* `b1174`, `S1174_card`, `encode1174_injective`, `encode1174_bijective`: Theorem 4 for Curve1174.
* `basePointV_montgomery`, `basePoint1174_mem_affinePoints`: the point `(U, V) = (4, V)` of
  Section 4.1 lies on the Montgomery model, and the corresponding point `(4/V, 3/5)` lies on
  Curve1174.

## References

See [bernstein2013a], Section 4.
-/

@[expose] public section

namespace Elligator.Elligator1.Curve1174

open Elligator.LegendreSymbol
open Elligator.PrimalityCertificate

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

/-- `q ≡ 3 (mod 4)`, one of the standing hypotheses of Elligator 1. -/
@[blueprint "lemma:q1174-mod-four"
  (title := "$q \\equiv 3 \\pmod 4$")
  (statement := /--
  The characteristic satisfies $q \equiv 3 \pmod 4$, so the standing hypotheses of Elligator 1
  are met by $\mathbb{F}_q$.
  -/)]
theorem q1174_mod_four : q1174 % 4 = 3 := by decide

/-- `q1174` is a prime power, as required by the Elligator 1 development. -/
theorem q1174_isPrimePow : IsPrimePow q1174 := prime_q1174.prime.isPrimePow

/-! ### The Elligator 1 parameter `s` and the derived parameters `c`, `r`, `d` -/

/-- The Elligator 1 parameter `s` chosen for Curve1174 in [bernstein2013a], Section 4.1. -/
@[blueprint "def:s1174"
  (title := "The Curve1174 parameter $s$")
  (statement := /--
  Define $s \in \mathbb{F}_q$ to be
  $$
  s = 1806494121122717992522804053500797229648438766985538871240722010849934886421 .
  $$
  -/)]
def s1174 : F1174 := 1806494121122717992522804053500797229648438766985538871240722010849934886421

/-- The parameter `s` is nonzero. -/
theorem s1174_ne_zero : s1174 ≠ 0 := by trivial

/-- The parameter `s` satisfies `(s^2 - 2)(s^2 + 2) ≠ 0`. -/
@[blueprint "lemma:s1174-hypotheses"
  (title := "$s$ satisfies the hypotheses of Theorem 1")
  (statement := /--
  The element $s$ is nonzero and satisfies $(s^2 - 2)(s^2 + 2) \neq 0$.
  -/)]
theorem s1174_sq_ne_pm_two : (s1174 ^ 2 - 2) * (s1174 ^ 2 + 2) ≠ 0 := by decide

/-- The value of the curve parameter `c = 2/s^2` for Curve1174. -/
@[blueprint "lemma:c1174"
  (title := "The value of $c$ for Curve1174")
  (statement := /--
  With $s$ as above, $c = 2/s^2$ equals
  $$
  2179648967284864129978754827181620133949030013113193603783078030367640144353 .
  $$
  -/)]
theorem c1174_eq :
  c s1174 = 2179648967284864129978754827181620133949030013113193603783078030367640144353 := by
    have h : s1174 ^ 2 ≠ 0 := by decide
    change (2 : F1174) / s1174 ^ 2 = _
    rw [div_eq_iff h]
    decide

/-- The value of the curve parameter `r = c + 1/c` for Curve1174. -/
@[blueprint "lemma:r1174"
  (title := "The value of $r$ for Curve1174")
  (statement := /--
  With $c$ as above, $r = c + 1/c$ equals
  $$
  169665518650159600071835149602457239235130252467237612483220564802728637315 .
  $$
  -/)]
theorem r1174_eq : r s1174 =
    169665518650159600071835149602457239235130252467237612483220564802728637315 := by
  have h : c s1174 ≠ 0 := by
    rw [c1174_eq]
    decide
  have key : (1 : F1174) / (c s1174)
    =  169665518650159600071835149602457239235130252467237612483220564802728637315 - (c s1174) := by
      rw [div_eq_iff h, c1174_eq]
      decide
  change c s1174 + 1 / c s1174 = _
  rw [key]
  ring

/-- The Edwards coefficient produced by Elligator 1 from `(q, s)` is `-1174`: the curve of
Theorem 1 and Definition 2 for this choice of parameters is exactly Curve1174. -/
@[blueprint "thm:d1174"
  (title := "The Elligator 1 curve for $(q, s)$ is Curve1174")
  (statement := /--
  With $c = 2/s^2$ as above,
  $$
  d = -(c + 1)^2/(c - 1)^2 = -1174 ,
  $$
  so the complete Edwards curve of Theorem 1 and Definition 2 for this choice of $(q, s)$ is
  exactly Curve1174, $x^2 + y^2 = 1 - 1174 x^2 y^2$.
  -/)]
theorem d1174_eq : d s1174 = -1174 := by
  have h : ((c s1174 : F1174) - 1) ^ 2 ≠ 0 := by
    rw [c1174_eq]
    decide
  change -(c s1174 + 1) ^ 2 / (c s1174 - 1) ^ 2 = -1174
  rw [div_eq_iff h, c1174_eq]
  decide

/-- The quadratic character of the Edwards coefficient is `-1`. -/
@[blueprint "lemma:chi-d1174"
  (title := "$\\chi(-1174) = -1$")
  (statement := /--
  The quadratic character of the Edwards coefficient satisfies $\chi(d) = -1$.
  -/)]
theorem chi_d1174_eq_neg_one : χ (d s1174) = -1 := by
  have hneg :
    ((3618502788666131106986593281521497120414687020801267626233049500247285300065 : ℕ) : F1174)
    = -1174 := by decide
  have hone :
    ((3618502788666131106986593281521497120414687020801267626233049500247285301238 : ℕ) : F1174)
    = -1 := by decide
  change (d s1174) ^ ((Fintype.card F1174 - 1) / 2) = -1
  rw [d1174_eq, card_F1174, ← hneg, ← hone]
  exact natCast_pow_eq_natCast _ _ _ 256 (by decide) (by decide)

/-- `-1174` is not a square in `F1174`; by [bernstein2013a], Section 4.1 this is what makes
Curve1174 a complete Edwards curve. -/
@[blueprint "thm:d1174-nonsquare"
  (title := "$-1174$ is a non-square")
  (statement := /--
  The coefficient $-1174$ is a non-square in $\mathbb{F}_q$; this is the criterion of
  [bernstein2013a, Theorem 3.3] making Curve1174 a complete Edwards curve.
  -/)]
theorem d1174_not_isSquare : ¬ IsSquare (d s1174) := by
  intro hsq
  have hne : d s1174 ≠ 0 := by
    rw [d1174_eq]
    decide
  have h1 : χ (d s1174) = 1 := (χ_a_eq_one_iff_a_square hne card_F1174 q1174_mod_four).2 hsq
  rw [chi_d1174_eq_neg_one] at h1
  exact absurd h1 (by decide)

/-! ### The curve -/

/-- Curve1174 as the Edwards curve produced by Elligator 1 from the parameter `s`. -/
@[blueprint "def:curve1174"
  (title := "Curve1174")
  (statement := /--
  Curve1174 is the complete Edwards curve
  $$
  x^2 + y^2 = 1 - 1174 x^2 y^2
  $$
  over $\mathbb{F}_q$, obtained from the Elligator 1 construction with the parameter $s$.
  -/)]
def curve1174 : TwistedEdwardsCurve F1174 := curve s1174

/-- Curve1174 is the Edwards curve with coefficient `-1174`. -/
theorem curve1174_eq : curve1174 = edwardsCurve (-1174 : F1174) := by
  unfold curve1174 curve
  rw [d1174_eq]

/-- The defining equation of Curve1174: `x^2 + y^2 = 1 - 1174 x^2 y^2`. -/
theorem curve1174_equation (x y : F1174) :
  curve1174.Equation x y ↔ x ^ 2 + y ^ 2 = 1 - 1174 * x ^ 2 * y ^ 2 := by
    rw [curve1174_eq]
    unfold edwardsCurve
    rw [TwistedEdwardsCurve.ofD_equation]
    group

/-- Curve1174 is a valid (nonsingular) Edwards model. -/
theorem curve1174_isValid : curve1174.IsValid :=
  curve_isValid s1174_sq_ne_pm_two card_F1174 q1174_mod_four

/-! ### The Elligator 1 maps for Curve1174 -/

/-- The Elligator 1 decoding function `φ : F_q → E(F_q)` of Definition 2, for Curve1174. -/
@[blueprint "def:decode1174"
  (title := "The Curve1174 decoding function")
  (statement := /--
  The map $\varphi : \mathbb{F}_q \to E(\mathbb{F}_q)$ of Definition 2, specialised to
  Curve1174.
  -/)]
def decode1174 (t : F1174) : F1174 × F1174 :=
  DecodingFunction t s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_isPrimePow q1174_mod_four

/-- Theorem 1 for Curve1174: every decoded value is a point of the curve. -/
theorem decode1174_mem_affinePoints (t : F1174) : decode1174 t ∈ curve1174.affinePoints :=
  (ϕ t s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_isPrimePow q1174_mod_four).prop

/-- Theorem 1 for Curve1174, in coordinates. -/
@[blueprint "thm:decode1174"
  (title := "Theorem 1 for Curve1174")
  (statement := /--
  For every $t \in \mathbb{F}_q$ the point $\varphi(t)$ lies on Curve1174.
  -/)]
theorem decode1174_equation (t : F1174) :
  let x := (decode1174 t).1
  let y := (decode1174 t).2
  x^2 + y^2 = 1 - 1174 * x^2 * y^2 := (curve1174_equation _ _).1 (decode1174_mem_affinePoints t)

/-- Theorem 3 for Curve1174: `φ` identifies `t` and `-t`. -/
theorem decode1174_neg (t : F1174) : decode1174 (-t) = decode1174 t :=
  (ϕ_of_t_eq_ϕ_of_neg_t t
    s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_isPrimePow
    q1174_mod_four
  ).symm

/-- Theorem 3 for Curve1174: `t` and `-t` are the only preimages of `φ t`. -/
theorem decode1174_preimages (t : F1174) :
  ¬ ∃ p : {n : F1174 // n ≠ t ∧ n ≠ -t}, decode1174 p.val = decode1174 t :=
    ϕ_preimages t s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_isPrimePow q1174_mod_four

/-! ### The string encoding for Curve1174 -/

/-- Curve1174 encodes field elements as strings of `b = ⌊log₂ q⌋ = 250` bits. -/
@[blueprint "lemma:b1174"
  (title := "Curve1174 encodes to 250-bit strings")
  (statement := /--
  For Curve1174 the string length of Theorem 4 is $b = \lfloor \log_2 q \rfloor = 250$.
  -/)]
theorem b1174 : b q1174 = 250 := by
  rw [b, q1174]
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_ <;> norm_num

/-- Theorem 4 for Curve1174: there are `(q + 1)/2` admissible bit strings. -/
theorem S1174_card : (@S q1174).card = (q1174 + 1) / 2 := S_card q1174_mod_four

/-- Theorem 4 for Curve1174: the string encoding `ι : S → E(F_q)` is injective. -/
theorem encode1174_injective : Function.Injective fun τ : @S q1174 =>
  ι τ s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_isPrimePow q1174_mod_four :=
    ι_injective s1174_ne_zero s1174_sq_ne_pm_two card_F1174 prime_q1174.prime q1174_mod_four

/-- Theorem 4 for Curve1174: the string encoding is a bijection from `S` onto `φ(F_q)`. -/
@[blueprint "thm:encode1174"
  (title := "Theorem 4 for Curve1174")
  (statement := /--
  For Curve1174 the string encoding $\iota$ is a bijection from $S$ onto
  $\varphi(\mathbb{F}_q)$.
  -/)]
theorem encode1174_bijective :
  Function.Bijective (ιToϕOverF s1174_ne_zero s1174_sq_ne_pm_two card_F1174
    q1174_isPrimePow q1174_mod_four) :=
    ιToϕOverF_bijective s1174_ne_zero s1174_sq_ne_pm_two card_F1174 prime_q1174.prime q1174_mod_four

/-! ### The base point -/

/-- The `V`-coordinate of the base point of Section 4.1 on the Montgomery model
`(4/1175) V^2 = U^3 + (4/1175 - 2) U^2 + U`, at `U = 4`. -/
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
`(4/1175) V^2 = U^3 + (4/1175 - 2) U^2 + U` to which Curve1174 is birationally equivalent. -/
@[blueprint "lemma:basePointMontgomery"
  (title := "The Montgomery base point")
  (statement := /--
  The point $(U, V) = (4, V)$ lies on the Montgomery curve
  $$
  (4/1175) V^2 = U^3 + (4/1175 - 2) U^2 + U .
  $$
  -/)]
theorem basePointV_montgomery :
  (4 / 1175 : F1174) * basePointV ^ 2 = 4 ^ 3 + (4 / 1175 - 2) * 4 ^ 2 + 4 := by
    have h : (1175 : F1174) ≠ 0 := by decide
    have key : (4 / 1175 : F1174)
      =  3276669759268734891773391703437338669039342119261743620691033760223924732356 := by
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
  rw [TwistedEdwardsCurve.affinePoints, Set.mem_setOf_eq, curve1174_equation]
  decide

end Elligator.Elligator1.Curve1174
