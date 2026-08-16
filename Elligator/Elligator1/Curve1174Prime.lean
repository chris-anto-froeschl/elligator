/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.PrimalityCertificate
public import Mathlib.Tactic.NormNum.Prime

/-!
# Primality of the Curve1174 characteristic

Curve1174 of [bernstein2013a], Section 4, is defined over the prime field `F_q` with
`q = 2 ^ 251 - 9`. This file establishes `Nat.Prime q`.

The proof runs the Pratt certificate machinery of `Elligator.PrimalityCertificate`: the
factorisation

```
q - 1 = 2 * 19 * 3121 * p_6
```

is completed by recursively certifying the large prime factors `p_1, …, p_6`, each of which is
again handled by `Elligator.PrimalityCertificate.prime_of_pratt`. All modular exponentiations are
carried out with `powMod`, so the numerical side conditions are closed by `decide` and are
checked by the Lean kernel.

## Main results

* `q1174_prime`: `2 ^ 251 - 9` is prime.

## References

See [bernstein2013a], Section 4.1.
-/

@[expose] public section

namespace Elligator.Elligator1.Curve1174

open Elligator.PrimalityCertificate

set_option maxRecDepth 20000

/-- An auxiliary prime occurring in the Pratt certificate for `q`,
verified by the Pratt certificate with base `7`. -/
theorem prime_2032236244151 : Nat.Prime 2032236244151 := by
  refine prime_of_pratt 7 256
    [2, 5, 5, 7, 5113, 1135613]
    (by norm_num) ?_ (by norm_num) (by decide) ?_
  · intro r hr
    fin_cases hr <;> norm_num
  · intro r hr
    fin_cases hr <;> decide

/-- An auxiliary prime occurring in the Pratt certificate for `q`,
verified by the Pratt certificate with base `5`. -/
theorem prime_20387630040577 : Nat.Prime 20387630040577 := by
  refine prime_of_pratt 5 256
    [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 17, 401, 1947073]
    (by norm_num) ?_ (by norm_num) (by decide) ?_
  · intro r hr
    fin_cases hr <;> norm_num
  · intro r hr
    fin_cases hr <;> decide

/-- An auxiliary prime occurring in the Pratt certificate for `q`,
verified by the Pratt certificate with base `5`. -/
theorem prime_297581916939273464475253 : Nat.Prime 297581916939273464475253 := by
  refine prime_of_pratt 5 256
    [2, 2, 3, 11, 1109324011, 2032236244151]
    (by norm_num) ?_ (by norm_num) (by decide) ?_
  · intro r hr
    fin_cases hr <;> first | exact prime_2032236244151 | norm_num
  · intro r hr
    fin_cases hr <;> decide

/-- An auxiliary prime occurring in the Pratt certificate for `q`,
verified by the Pratt certificate with base `2`. -/
theorem prime_2151858718037429125511251 : Nat.Prime 2151858718037429125511251 := by
  refine prime_of_pratt 2 256
    [2, 3, 5, 5, 5, 5, 28145939, 20387630040577]
    (by norm_num) ?_ (by norm_num) (by decide) ?_
  · intro r hr
    fin_cases hr <;> first | exact prime_20387630040577 | norm_num
  · intro r hr
    fin_cases hr <;> decide

/-- An auxiliary prime occurring in the Pratt certificate for `q`,
verified by the Pratt certificate with base `2`. -/
theorem prime_22645347980446549950250344634517843 :
  Nat.Prime 22645347980446549950250344634517843 := by
    refine prime_of_pratt 2 256
      [2, 7, 13, 53, 7889059, 297581916939273464475253]
      (by norm_num) ?_ (by norm_num) (by decide) ?_
    · intro r hr
      fin_cases hr <;> first | exact prime_297581916939273464475253 | norm_num
    · intro r hr
      fin_cases hr <;> decide

/-- An auxiliary prime occurring in the Pratt certificate for `q`,
verified by the Pratt certificate with base `6`. -/
theorem prime_30510656070643106182115999270826633842178510774222732476374386585332681 :
    Nat.Prime 30510656070643106182115999270826633842178510774222732476374386585332681 := by
  refine prime_of_pratt 6 256
    [2, 2, 2, 5, 31, 11783, 42853, 2151858718037429125511251,
    22645347980446549950250344634517843]
    (by norm_num) ?_ (by norm_num) (by decide) ?_
  · intro r hr
    have h0 := prime_2151858718037429125511251
    have h1 := prime_22645347980446549950250344634517843
    fin_cases hr <;> first | assumption | norm_num
  · intro r hr
    fin_cases hr <;> decide

/-- The characteristic `q = 2 ^ 251 - 9` of the Curve1174 base field is prime,
verified by the Pratt certificate with base `7`. -/
theorem q1174_prime :
    Nat.Prime 3618502788666131106986593281521497120414687020801267626233049500247285301239 := by
  refine prime_of_pratt 7 256
    [2, 19, 3121,
    30510656070643106182115999270826633842178510774222732476374386585332681]
    (by norm_num) ?_ (by norm_num) (by decide) ?_
  · intro r hr
    have h0 := prime_30510656070643106182115999270826633842178510774222732476374386585332681
    fin_cases hr <;> first | assumption | norm_num
  · intro r hr
    fin_cases hr <;> decide

end Elligator.Elligator1.Curve1174
