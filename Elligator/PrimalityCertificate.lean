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
instance `q = 2^251 - 9` for Curve1174 (see [bernstein2013a], Section 4). Such a primality
statement is far out of reach for the decision procedures that evaluate a `Nat.Prime` goal by
trial division, so this file provides the infrastructure needed to check a *Pratt certificate*
inside Lean.

Two ingredients are required.

* `powMod`, a binary modular exponentiation that the kernel can evaluate on numerals of
  several hundred bits, together with its correctness statement `powMod_eq`.
* `prime_of_pratt`, a repackaging of Mathlib's `lucas_primality` in which the prime divisors of
  `p - 1` are supplied as an explicit list and all modular exponentiations are phrased through
  `powMod`, so that every side condition of the certificate is closed by `decide`.

## Main results

* `powMod_eq`: `powMod m f b e = b ^ e % m` whenever the fuel `f` bounds the bit length
  of the exponent, i.e. `e < 2 ^ f`.
* `prime_of_pratt`: the Pratt/Lucas primality criterion in a form suited to kernel evaluation.
-/

@[expose] public section

namespace Elligator.PrimalityCertificate

/-- `powMod m f b e` computes `b ^ e % m` by binary exponentiation, where `f` is a fuel
parameter that has to bound the bit length of `e`; see `powMod_eq`.

Unlike `b ^ e % m` this is evaluated by the kernel in time linear in `f`, which makes it usable
inside `decide` for exponents with hundreds of bits. -/
@[blueprint "def:powMod"
  (title := "Binary modular exponentiation")
  (statement := /--
  For a modulus $m$, a fuel bound $f$, a base $b$ and an exponent $e$ define $\operatorname{powMod}$
  by binary exponentiation, so that $\operatorname{powMod}(m, f, b, e) = b^e \bmod m$ whenever
  $e < 2^f$.
  -/)]
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | f + 1, b, e =>
      if e = 0 then 1 % m
      else
        let h := powMod m f (b * b % m) (e / 2)
        if e % 2 = 1 then h * b % m else h

/-- Correctness of binary modular exponentiation: as soon as the fuel bounds the bit length of
the exponent, `powMod` computes the modular power. -/
theorem powMod_eq (m : ℕ) : ∀ f b e : ℕ, e < 2^f → powMod m f b e = b^e % m := by
  intro f
  induction f with
  | zero =>
    intro b e he
    have he : e = 0 := by simpa using he
    subst he
    simp [powMod]
  | succ f ih =>
    intro b e he
    rw [powMod]
    by_cases h0 : e = 0
    · simp [h0]
    · rw [if_neg h0]
      have hlt : e / 2 < 2^f := by
        rw [pow_succ] at he
        omega
      have hh : powMod m f (b * b % m) (e / 2) = (b * b)^(e / 2) % m := by
        rw [ih _ _ hlt, ← Nat.pow_mod]
      have hb : (b * b)^(e / 2) = b^(2 * (e / 2)) := by rw [← pow_two, ← pow_mul]
      simp only [hh, hb]
      rcases Nat.mod_two_eq_zero_or_one e with h2 | h2
      · have h2' : 2 * (e / 2) = e := by omega
        rw [if_neg (by omega), h2']
      · have h2' : 2 * (e / 2) + 1 = e := by omega
        rw [if_pos h2, Nat.mod_mul_mod, ← pow_succ, h2']

/-- Modular powers inside `ZMod m` computed through `powMod`: if the binary exponentiation
of `a^e` modulo `m` returns `b % m`, then `(a : ZMod m)^e = b`. This transports a kernel
computation with numerals into an equation between residues. -/
theorem natCast_pow_eq_natCast {m : ℕ} (a e b F : ℕ) (hfuel : e < 2 ^ F)
  (h : powMod m F a e = b % m) : ((a : ZMod m))^e = (b : ZMod m) := by
    rw [← Nat.cast_pow]
    refine (ZMod.natCast_eq_natCast_iff' _ _ _).2 ?_
    rw [← powMod_eq m F a e hfuel, h]

/-- The Pratt (Lucas) primality criterion, phrased for kernel evaluation.

If `L` is a list of primes whose product is `p - 1` and if the base `a` has order exactly `p - 1`
modulo `p`, witnessed by `a^(p - 1) ≡ 1` and `a^((p - 1) / r) ≢ 1` for every `r ∈ L`, then `p`
is prime. All modular powers are written through `powMod`, so the hypotheses are decidable by
computation once `p`, `a`, `F` and `L` are numerals. -/
@[blueprint "thm:pratt"
  (title := "The Pratt primality criterion")
  (statement := /--
  Let $p$ be a natural number and let $L$ be a list of primes with $\prod_{r \in L} r = p - 1$.
  If there is an $a$ with $a^{p-1} \equiv 1 \pmod p$ and $a^{(p-1)/r} \not\equiv 1 \pmod p$ for
  every $r \in L$, then $p$ is prime.
  -/)]
theorem prime_of_pratt {p : ℕ} (a F : ℕ) (L : List ℕ) (hfuel : p - 1 < 2 ^ F)
  (hL : ∀ r ∈ L, Nat.Prime r) (hprod : p - 1 = L.prod)
  (ha : powMod p F a (p - 1) = 1 % p)
  (hchk : ∀ r ∈ L, powMod p F a ((p - 1) / r) ≠ 1 % p) :
  Nat.Prime p := by
    refine lucas_primality p (a : ZMod p) ?_ ?_
    · simpa using natCast_pow_eq_natCast a (p - 1) 1 F hfuel ha
    · intro r hr hdvd
      have hlt : (p - 1) / r < 2 ^ F := lt_of_le_of_lt (Nat.div_le_self _ _) hfuel
      obtain ⟨x, hx, hrx⟩ := (Prime.dvd_prod_iff hr.prime).1 (hprod ▸ hdvd)
      obtain rfl : r = x := (Nat.prime_dvd_prime_iff_eq hr (hL x hx)).1 hrx
      intro hcon
      apply hchk r hx
      have h := (ZMod.natCast_eq_natCast_iff' (a ^ ((p-1)/r)) 1 p).1 (by simpa using hcon)
      rw [powMod_eq p F a _ hlt]
      exact h

end Elligator.PrimalityCertificate
