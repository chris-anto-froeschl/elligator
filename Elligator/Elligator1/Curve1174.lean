/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Primitives.ECC.Curves.Curve1174
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.DecodingFunction
public import Elligator.Elligator1.InvertedMap
public import Elligator.Elligator1.StringEncoding
public meta import Mathlib.Data.ZMod.Defs

/-!
# Elligator 1 for Curve1174

This file instantiates the general Elligator 1 development at the concrete curve of
[Bernstein2013a], Section 4: Curve1174, the complete Edwards curve

$$ x ^ 2 + y ^ 2 = 1 - 1174 x ^ 2 y ^ 2 $$

over the prime field $\mathbb{F}_q$ with $q = 2^{251} - 9$.

The curve itself (its base field, its Edwards model, the non-squareness of its coefficient and its
base point) is developed independently of Elligator in
`Elligator.ECCPrimitives.Curves.Curve1174`. What is done here is the Elligator 1 side: following
the paper, the curve is not given by its coefficient but produced by the Elligator 1 construction
from the parameter

$$ s = 1806494121122717992522804053500797229648438766985538871240722010849934886421, $$

and the resulting coefficient `d s` is shown to be exactly `-1174`, so that the Elligator 1 curve
for `(q, s)` is Curve1174. The Elligator 1 maps for Curve1174 are then obtained by specializing the
general theorems at `s`.

All numerical statements are checked by kernel computation; field elements of `F1174` are `Fin`
residues, so `decide` evaluates ring operations directly.

## Main results

* `s1174_ne_zero`, `s1174_sq_ne_pm_two`: the parameter `s` satisfies the hypotheses of Theorem 1.
* `c1174_eq`, `r1174_eq`: the values of the derived parameters `c = 2/s ^ 2` and `r = c + 1/c`.
* `d1174_eq`: `d = -(c + 1) ^ 2/(c - 1) ^ 2 = -1174`, i.e. the Elligator 1 curve for `(q, s)` is
  Curve1174, `curve_s1174_eq`.
* `chi_d1174_eq_neg_one`, `d1174_not_isSquare`: the Elligator 1 coefficient is a non-square.
* `decode1174_mem_affinePoints`, `decode1174_equation`: Theorem 1 and Definition 2 for Curve1174.
* `decode1174_neg`, `decode1174_preimages`: Theorem 3 for Curve1174.
* `b1174`, `S1174_card`, `encode1174_injective`, `encode1174_bijective`: Theorem 4 for Curve1174.

## References

See [Bernstein2013a], Section 4.
-/

@[expose] public section

namespace Elligator.Elligator1.Curve1174

open Elligator.LegendreSymbol
open Elligator.Primitives.ECC
open Elligator.Primitives.PrimalityCertificate
open Elligator.Primitives.ECC.Curves.Curve1174

set_option maxRecDepth 20000

/-! ### The Elligator 1 parameter `s` and the derived parameters `c`, `r`, `d` -/

/-- The Elligator 1 parameter `s` chosen for Curve1174 in [Bernstein2013a], Section 4.1. -/
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
lemma s1174_ne_zero : s1174 ≠ 0 := by trivial

/-- The parameter `s` satisfies `(s ^ 2 - 2)(s ^ 2 + 2) ≠ 0`. -/
@[blueprint "lemma:s1174-hypotheses"
  (title := "$s$ satisfies the hypotheses of Theorem 1")
  (statement := /--
  The element $s$ is nonzero and satisfies $(s ^ 2 - 2)(s ^ 2 + 2) \neq 0$.
  -/)]
lemma s1174_sq_ne_pm_two : (s1174 ^ 2 - 2) * (s1174 ^ 2 + 2) ≠ 0 := by decide

/-- The value of the curve parameter `c = 2/s ^ 2` for Curve1174. -/
@[blueprint "lemma:c1174"
  (title := "The value of $c$ for Curve1174")
  (statement := /--
  With $s$ as above, $c = 2/s ^ 2$ equals
  $$
  2179648967284864129978754827181620133949030013113193603783078030367640144353 .
  $$
  -/)]
lemma c1174_eq :
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
lemma r1174_eq :
    r s1174 = 169665518650159600071835149602457239235130252467237612483220564802728637315 := by
  have h : c s1174 ≠ 0 := by
    rw [c1174_eq]
    decide
  have key :
    (1 : F1174) / (c s1174)
    = 169665518650159600071835149602457239235130252467237612483220564802728637315 - (c s1174) := by
    rw [div_eq_iff h, c1174_eq]
    decide
  change c s1174 + 1 / c s1174 = _
  rw [key]
  ring

/-- The Edwards coefficient produced by Elligator 1 from `(q, s)` is `-1174`: the curve of
lemma 1 and Definition 2 for this choice of parameters is exactly Curve1174. -/
@[blueprint "thm:d1174"
  (title := "The Elligator 1 curve for $(q, s)$ is Curve1174")
  (statement := /--
  With $c = 2/s ^ 2$ as above,
  $$
  d = -(c + 1) ^ 2/(c - 1) ^ 2 = -1174 ,
  $$
  so the complete Edwards curve of Theorem 1 and Definition 2 for this choice of $(q, s)$ is
  exactly Curve1174, $x ^ 2 + y ^ 2 = 1 - 1174 x ^ 2 y ^ 2$.
  -/)]
lemma d1174_eq : d s1174 = -1174 := by
  have h : ((c s1174 : F1174) - 1) ^ 2 ≠ 0 := by
    rw [c1174_eq]
    decide
  change -(c s1174 + 1) ^ 2 / (c s1174 - 1) ^ 2 = -1174
  rw [div_eq_iff h, c1174_eq]
  decide

/-- The quadratic character of the Elligator 1 coefficient for `(q, s)` is `-1`. -/
lemma chi_d1174_eq_neg_one : χ (d s1174) = -1 := by
  rw [d1174_eq]
  exact chi_neg1174_eq_neg_one

/-- The Elligator 1 coefficient for `(q, s)` is not a square in `F1174`. -/
lemma d1174_not_isSquare : ¬IsSquare (d s1174) := by
  rw [d1174_eq]
  exact neg1174_not_isSquare

/-! ### The curve -/

/-- The Edwards curve selected by the Elligator 1 parameter `s` is Curve1174. -/
lemma curve_s1174_eq : curve s1174 = curve1174 := by
  unfold curve curve1174
  rw [d1174_eq]

/-- Curve1174 is a valid (nonsingular) Edwards model, seen through the Elligator 1 hypotheses. -/
lemma curve_s1174_isValid : (curve s1174).IsValid :=
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
  DecodingFunction t s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_mod_four

/-- Theorem 1 for Curve1174: every decoded value is a point of the curve. -/
lemma decode1174_mem_affinePoints (t : F1174) : decode1174 t ∈ curve1174.affinePoints :=
  curve_s1174_eq ▸ (ϕ t s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_mod_four).prop

/-- Theorem 1 for Curve1174, in coordinates. -/
@[blueprint "thm:decode1174"
  (title := "Theorem 1 for Curve1174")
  (statement := /--
  For every $t \in \mathbb{F}_q$ the point $\varphi(t)$ lies on Curve1174.
  -/)]
lemma decode1174_equation (t : F1174) :
    let x := (decode1174 t).1
    let y := (decode1174 t).2
    x ^ 2 + y ^ 2 = 1 - 1174 * x ^ 2 * y ^ 2 :=
  (curve1174_equation _ _).1 (decode1174_mem_affinePoints t)

/-- Theorem 3 for Curve1174: `φ` identifies `t` and `-t`. -/
lemma decode1174_neg (t : F1174) : decode1174 (-t) = decode1174 t :=
  (ϕ_of_t_eq_ϕ_of_neg_t t
    s1174_ne_zero s1174_sq_ne_pm_two card_F1174
    q1174_mod_four
  ).symm

/-- Theorem 3 for Curve1174: `t` and `-t` are the only preimages of `φ t`. -/
lemma decode1174_preimages (t : F1174) :
    ¬∃ p : {n : F1174 // n ≠ t ∧ n ≠ -t}, decode1174 p.val = decode1174 t :=
  ϕ_preimages t s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_mod_four

/-! ### The string encoding for Curve1174 -/

/-- Curve1174 encodes field elements as strings of `b = ⌊log₂ q⌋ = 250` bits. -/
@[blueprint "lemma:b1174"
  (title := "Curve1174 encodes to 250-bit strings")
  (statement := /--
  For Curve1174 the string length of Theorem 4 is $b = \lfloor \log_2 q \rfloor = 250$.
  -/)]
lemma b1174 : b q1174 = 250 := by
  rw [b, q1174]
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_ <;> norm_num

/-- Theorem 4 for Curve1174: there are `(q + 1)/2` admissible bit strings. -/
lemma S1174_card : (@S q1174).card = (q1174 + 1) / 2 := S_card q1174_mod_four

/-- Theorem 4 for Curve1174: the string encoding `ι : S → E(F_q)` is injective. -/
lemma encode1174_injective : Function.Injective fun τ : @S q1174 =>
    ι τ s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_mod_four :=
  ι_injective s1174_ne_zero s1174_sq_ne_pm_two card_F1174 prime_q1174.prime q1174_mod_four

/-- Theorem 4 for Curve1174: the string encoding is a bijection from `S` onto `φ(F_q)`. -/
@[blueprint "thm:encode1174"
  (title := "Theorem 4 for Curve1174")
  (statement := /--
  For Curve1174 the string encoding $\iota$ is a bijection from $S$ onto
  $\varphi(\mathbb{F}_q)$.
  -/)]
lemma encode1174_bijective :
    Function.Bijective (ιToϕOverF s1174_ne_zero s1174_sq_ne_pm_two card_F1174 q1174_mod_four) :=
  ιToϕOverF_bijective s1174_ne_zero s1174_sq_ne_pm_two card_F1174 prime_q1174.prime q1174_mod_four

end Elligator.Elligator1.Curve1174
