/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Basic
public import Mathlib.NumberTheory.LucasPrimality

/-!
# Primality certificates

Elligator 1 is instantiated over concrete finite fields whose cardinality is a large prime, for
instance `q = 2 ^ 251 - 9` for Curve1174 (see [Bernstein2013a], Section 4). Such a primality
statement is far out of reach for the decision procedures that evaluate a `Nat.Prime` goal by
trial division, so this file provides the infrastructure needed to check a *Pratt certificate*
inside Lean.

Two ingredients are required:

* `powMod`, a binary modular exponentiation that the kernel can evaluate on numerals of
  several hundred bits, together with its correctness statement `powMod_eq`.
* `prime_of_pratt`, a repackaging of Mathlib's `lucas_primality` in which the prime divisors of
  `p - 1` are supplied as an explicit list and all modular exponentiations are phrased through
  `powMod`, so that every side condition of the certificate is closed by `decide`.

## Main results

* `powMod_eq`: `powMod m f b e = b ^ e % m` whenever the `fuel` bounds the bit length
  of the exponent, i.e. `e < 2 ^ f`.
* `prime_of_pratt`: the Pratt/Lucas primality criterion in a form suited to kernel evaluation.
-/

@[expose] public section

namespace Elligator.Primitives.PrimalityCertificate

/-- `powMod m f b e` computes `b ^ e % m` by binary exponentiation, with `fuel` parameter
that has to bound the bit length of `e`; see `powMod_eq`.

Unlike `b ^ e % m` this is evaluated by the kernel in time linear in `f`, which makes it usable
inside `decide` for exponents with hundreds of bits. -/
@[blueprint "def:powMod"
  (title := "Binary modular exponentiation")
  (statement := /--
  For a modulus $m$, a fuel bound $fuel$, a base $b$ and an exponent $e$
  define $\operatorname{powMod}$ by binary exponentiation, so that
  $\operatorname{powMod}(m, fuel, b, e) = b ^ e \bmod m$ whenever $e < 2^{fuel}$.
  -/)]
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | fuel + 1, b, e =>
      if e = 0 then 1 % m
      else
        let h := powMod m fuel (b * b % m) (e / 2)
        if e % 2 = 1 then h * b % m else h

/-- Correctness of binary modular exponentiation: as soon as the fuel bounds the bit length of
the exponent, `powMod` computes the modular power. -/
lemma powMod_eq (m : ℕ) : ∀ fuel b e : ℕ, e < 2 ^ fuel → powMod m fuel b e = b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e he
    have he : e = 0 := by simp_all
    simp [he, powMod]
   | succ fuel ih =>
    intro b e he
    rw [powMod]
    by_cases he0 : e = 0
    · -- `e = 0`: both sides are `1 % m` by definition.
      simp [he0]
    · rw [ite_eq_right he0]
      -- The recursive call consumes one unit of fuel to handle `e / 2` (one bit shorter);
      -- since we had enough fuel for `e`, we have enough for `e / 2`.
      have h_fuel_suffices : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he
        omega
      -- By the induction hypothesis, the recursive call really computes the modular power.
      have h_recursive_call : powMod m fuel (b * b % m) (e / 2) = (b * b) ^ (e / 2) % m := by
        rw [ih _ _ h_fuel_suffices, ← Nat.pow_mod]
      -- `(b*b) ^ (e/2) = b ^ (2*(e/2))`: squaring the base while halving the exponent is exactly
      -- one step of binary exponentiation.
      have h_square_base : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by rw [← pow_two, ← pow_mul]
      simp only [h_recursive_call, h_square_base]
      -- If `e` is even, `2*(e/2) = e` and we're done. If `e` is odd, `powMod` multiplies by
      -- one extra `b`, matching `2*(e/2) + 1 = e`.
      rcases Nat.mod_two_eq_zero_or_one e with he_even | he_odd
      · have h_e_eq : 2 * (e / 2) = e := by omega
        rw [ite_eq_right (by omega), h_e_eq]
      · have h_e_eq : 2 * (e / 2) + 1 = e := by omega
        rw [ite_eq_left he_odd, Nat.mod_mul_mod, ← pow_succ, h_e_eq]

/-- Modular powers inside `ZMod m` computed through `powMod`: if the binary exponentiation
of `a ^ e` modulo `m` returns `b % m`, then `(a : ZMod m) ^ e = b`. This transports a kernel
computation with numerals into an equation between residues. -/
lemma natCast_pow_eq_natCast {m : ℕ}
    (a e b fuel : ℕ) (hfuel : e < 2 ^ fuel) (h : powMod m fuel a e = b % m) :
    ((a : ZMod m)) ^ e = (b : ZMod m) := by
  rw [← Nat.cast_pow]
  rw [ZMod.natCast_eq_natCast_iff', ← powMod_eq m fuel a e hfuel, h]

/-- The Pratt (Lucas) primality criterion, phrased for kernel evaluation.

If `L` is a list of primes whose product is `p - 1` and if the base `a` has order exactly `p - 1`
modulo `p`, witnessed by `a ^ (p - 1) ≡ 1` and `a ^ ((p - 1) / r) ≢ 1` for every `r ∈ L`, then `p`
is prime. All modular powers are written through `powMod`, so the hypotheses are decidable by
computation once `p`, `a`, `F` and `L` are numerals. -/
@[blueprint "thm:pratt"
  (title := "The Pratt primality criterion")
  (statement := /--
  Let $p$ be a natural number and let $L$ be a list of primes with $\prod_{r \in L} r = p - 1$.
  If there is an $a$ with $a^{p-1} \equiv 1 \pmod p$ and $a^{(p-1)/r} \not\equiv 1 \pmod p$ for
  every $r \in L$, then $p$ is prime.
  -/)]
lemma prime_of_pratt {p : ℕ}
    (a fuel : ℕ) (L : List ℕ) (hfuel : p - 1 < 2 ^ fuel)
    (hL : ∀ r ∈ L, Nat.Prime r) (hprod : p - 1 = L.prod)
    (ha : powMod p fuel a (p - 1) = 1 % p)
    (hchk : ∀ r ∈ L, powMod p fuel a ((p - 1) / r) ≠ 1 % p) :
    Nat.Prime p := by
    -- Lucas' criterion needs exactly two facts about `a` in `ZMod p`:
  -- (1) `a ^ (p-1) = 1`, and (2) for every *prime* `r ∣ (p-1)`, `a ^ ((p-1)/r) ≠ 1`.
  apply lucas_primality p (a : ZMod p)
  · -- Fact (1): exactly what `ha` says, transported from `ℕ` into `ZMod p`.
    have h1 : (a : ZMod p) ^ (p - 1) = ((1 : ℕ) : ZMod p) :=
      natCast_pow_eq_natCast a (p - 1) 1 fuel hfuel ha
    simp_all
  · -- Fact (2): let `r` be an arbitrary prime dividing `p - 1`.
    intro r hr_prime hr_dvd
    have h_fuel_suffices : (p - 1) / r < 2 ^ fuel :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hfuel
    -- `hprod` says `p - 1 = L.prod`, and `L` consists of primes. A prime `r` dividing a
    -- product of primes must actually *equal* one of the factors (unique factorization).
    obtain ⟨x, hx_mem, hr_dvd_x⟩ := (Prime.dvd_prod_iff hr_prime.prime).1 (hprod ▸ hr_dvd)
    obtain rfl : r = x := (Nat.prime_dvd_prime_iff_eq hr_prime (hL x hx_mem)).1 hr_dvd_x
    -- So `r ∈ L`, and `hchk` directly rules out `a ^ ((p-1)/r) = 1` - we just need to unwind
    -- that into the `ZMod p` statement Lucas' criterion wants.
    intro hcon_zmod
    apply hchk r hx_mem
    have h_nat : a ^ ((p - 1) / r) % p = 1 % p :=
      (ZMod.natCast_eq_natCast_iff' (a ^ ((p - 1) / r)) 1 p).1 (by simp_all)
    rw [powMod_eq p fuel a _ h_fuel_suffices]
    exact h_nat

end Elligator.Primitives.PrimalityCertificate
