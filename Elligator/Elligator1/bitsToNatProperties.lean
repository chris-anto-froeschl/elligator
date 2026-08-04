/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.bProperties

/-!
# bitsToNat Properties

This file establishes that binary evaluation identifies length-`n` bit-vectors
with the natural numbers below `2 ^ n`.  It also records consequences used by
the Elligator string encoding.

## Main results

- `bitsToNat_lt_two_pow_n`: the value of an `n`-bit vector is below `2 ^ n`.
- `bitsToNat_injective`: binary evaluation is injective.
- `bitsToFin_bijective`: binary evaluation, with its range encoded in the codomain, is a bijection
- `bitsToNat_surj`: every natural number below `2 ^ n` is represented by an `n`-bit vector.
- `σ_injective`: casting binary values into a prime field is injective on `b`-bit vectors.
- `exists_σ_preimage_or_neg`: every field element, up to sign, is represented by a bit-vector
  in `S`.

## References

See [bernstein2013a], Section 3.4, Theorem 4.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

lemma bitsToNat_le_full_range {n : ℕ} (τ : Fin n → Bool)
  : bitsToNat τ ≤ ∑ i ∈ Finset.range n, 2^i := by
    rw [Finset.sum_range]
    exact Finset.sum_le_sum fun i _ => by aesop

/-- Every bit-vector of length `n` has binary value less than `2^n`. -/
lemma bitsToNat_lt_two_pow_n {n : ℕ} (τ : Fin n → Bool) : bitsToNat τ < 2 ^ n := by
  let h := bitsToNat_le_full_range τ
  have h' : ∑ i ∈ Finset.range n, 2 ^ i < 2 ^ n := Nat.geomSum_lt (by trivial) (by grind)
  apply lt_of_le_of_lt h h'


lemma bitsToNat_le_q_sub_one_over_two (τ : (@S q)) : bitsToNat τ.1 ≤ (q - 1) / 2 := by
  exact Finset.mem_filter.mp τ.2 |>.2

/-- Splitting off the least significant bit gives the standard binary recurrence. -/
lemma bitsToNat_succ {n : ℕ} (τ : Fin (n + 1) → Bool) :
  bitsToNat τ = 2 * bitsToNat (fun i => τ i.succ) + if τ 0 then 1 else 0 := by
    unfold bitsToNat
    simp +decide [Fin.sum_univ_succ, pow_succ']
    ring_nf
    rw [Finset.sum_mul]
    grind

/-- Prefixing a zero bit doubles the value of the remaining bits. -/
@[simp]
lemma bitsToNat_cons_false {n : ℕ} (τ : Fin n → Bool) :
  bitsToNat (Fin.cons false τ) = 2 * bitsToNat τ := by simp [bitsToNat_succ]

/-- Prefixing a one bit doubles the value of the remaining bits and adds one. -/
@[simp]
lemma bitsToNat_cons_true {n : ℕ} (τ : Fin n → Bool) :
  bitsToNat (Fin.cons true τ) = 2 * bitsToNat τ + 1 := by simp [bitsToNat_succ]

/-- `bitsToNat` is injective: distinct bit-vectors give distinct natural numbers. -/
@[blueprint "lemma:bitsToNat_injective"
  (title := "Binary evaluation is injective")
  (statement := /--
  Distinct bit strings of length $n$ have distinct binary values $\sum_i \tau_i 2^i$.
  -/)]
lemma bitsToNat_injective {n : ℕ} : Function.Injective (bitsToNat : (Fin n → Bool) → ℕ) := by
  induction n with
  | zero => decide
  | succ n ih =>
    intro τ τ' h
    have h_tail : bitsToNat (fun i => τ i.succ) = bitsToNat (fun i => τ' i.succ) := by
      rw [bitsToNat_succ τ, bitsToNat_succ τ'] at h
      grind +ring
    have h_tail_fun := ih h_tail
    funext i
    refine Fin.induction ?_ (fun j => ?_) i
    · rw [bitsToNat_succ τ, bitsToNat_succ τ'] at h
      grind +ring
    · intro h
      exact congr_fun h_tail_fun j

/-- Every natural number less than `2^n` is the binary value of some bit-vector. -/
-- TODO use Function.surjective possible, i.e. have to get hm into ∀ m value somehow
@[blueprint "lemma:bitsToNat_surj"
  (title := "Binary evaluation is onto $\\{0, \\ldots, 2^n - 1\\}$")
  (statement := /--
  Every integer $m$ with $0 \leq m < 2^n$ is the binary value of some bit string of length $n$.
  -/)]
lemma bitsToNat_surj (n : ℕ) (m : ℕ) (hm : m < 2 ^ n) :
  ∃ τ : Fin n → Bool, bitsToNat τ = m := by
    induction n generalizing m with
    | zero =>
      rw [pow_zero] at hm
      unfold bitsToNat
      rw [Finset.univ_eq_empty]
      have hm_zero : m = 0 := by omega
      simp only [Finset.sum_empty, exists_const]
      exact hm_zero.symm
    | succ n ih =>
      rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
      · obtain ⟨τ, hτ⟩ := ih k (by
          simp only [pow_succ'] at hm
          omega
        )
        exact ⟨Fin.cons false τ, by simp [hτ]⟩
      · obtain ⟨τ, hτ⟩ := ih k (by
        simp only [pow_succ'] at hm
        omega)
        exact ⟨Fin.cons true τ, by simp [hτ]⟩

lemma natCast_injective_of_prime_card
  {q : ℕ}
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  (a b : ℕ) (ha : a < q) (hb : b < q) (h : (a : F) = (b : F))
  : a = b := by
    have hchar := ringChar_of_F_eq_q q_h1 q_prime
    have hmod : a % ringChar F = b % ringChar F := (CharP.cast_eq_iff_mod_eq F (ringChar F)).mp h
    rw [hchar, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
    exact hmod

@[blueprint "lemma:lower_half_neg_eq"
  (title := "The lower half contains no pair of negatives")
  (statement := /--
  Let $q$ be prime and let $a, b \in \{0, 1, \ldots, (q-1)/2\}$ with $a = -b$ in $\mathbb{F}_q$.
  Then $a = b$. This is the step of Theorem 4 that removes the sign ambiguity of $\varphi$.
  -/)]
lemma lower_half_neg_eq
  (q_h1 : Fintype.card F = q) (hq : Prime q)
  {a b : ℕ} (ha : a ≤ (q - 1) / 2) (hb : b ≤ (q - 1) / 2)
  (heq : (a : F) = -(b : F))
  : a = b := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a + b = k * q := by
      have h_div : q ∣ (a + b : ℕ) := by
        rw [← ringChar_of_F_eq_q q_h1 hq, ← CharP.cast_eq_zero_iff F]
        simp_all
      exact exists_eq_mul_left_of_dvd h_div
    rcases k <;> grind

@[blueprint "lemma:σ_injective"
  (title := "$\\sigma$ is injective")
  (statement := /--
  Since $2^b \leq q$, the integers $0, 1, \ldots, 2^b - 1$ are distinct in $\mathbb{F}_q$;
  hence $\sigma$ is injective.
  -/)]
lemma σ_injective
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  (q_h3 : q % 4 = 3)
  : Function.Injective (@σ F _ q) := by
    intro a b h_eq
    apply bitsToNat_injective
    have h1 : bitsToNat a < q := lt_of_lt_of_le (bitsToNat_lt_two_pow_n a) (two_pow_b_le_q q_h3)
    have h2 : bitsToNat b < q := lt_of_lt_of_le (bitsToNat_lt_two_pow_n b) (two_pow_b_le_q q_h3)
    exact natCast_injective_of_prime_card q_h1 q_prime _ _ h1 h2 h_eq

@[blueprint "lemma:exists_S_elem_of_le"
  (title := "Preimages under $\\sigma$ of the lower half")
  (statement := /--
  Since $2^b > q/2$, the set $\{0, 1, \ldots, (q-1)/2\}$ is a subset of
  $\{0, 1, \ldots, 2^b - 1\}$; hence each of $0, 1, \ldots, (q-1)/2$ has a preimage under
  $\sigma$, lying in $S$.
  -/)]
lemma exists_S_elem_of_le (q_h3 : q % 4 = 3) (n : ℕ) (hle : n ≤ (q - 1) / 2)
  : ∃ (τ : (@S q)), bitsToNat τ.1 = n := by
    have hn_pow : n < 2 ^ (@b q) := by
      have h_log : q ≤ 2 ^ Nat.log 2 q * 2 := by
        rw [← pow_succ]
        exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
      unfold b
      omega
    obtain ⟨τ, hτ⟩ := bitsToNat_surj (@b q) n hn_pow
    exact ⟨⟨τ, by simp [S, hle, hτ]⟩, hτ⟩

/-- Every field element has a representative in `S` up to sign.
For prime `q` with `q ≡ 3 (mod 4)` and any `t : F`, there is a string `τ ∈ S` such that
`σ τ = t` or `σ τ = -t`. This is the lower-half representative argument used to prove that the
string encoding covers all of `ϕ(F)` in Theorem 4. -/
@[blueprint "lemma:exists_σ_preimage_or_neg"
  (title := "Every field element is $\\pm\\sigma(\\tau)$ for some $\\tau \\in S$")
  (statement := /--
  For every $t \in \mathbb{F}_q$, at least one of $t, -t$ lies in
  $\{0, 1, \ldots, (q-1)/2\} = \sigma(S)$; that is, there is $\tau \in S$ with
  $\sigma(\tau) = t$ or $\sigma(\tau) = -t$.
  -/)]
lemma exists_σ_preimage_or_neg
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  (q_h3 : q % 4 = 3)
  (t : F)
  : ∃ (τ : (@S q)), (@σ F _ q τ.1) = t ∨ (@σ F _ q τ.1) = -t := by
  obtain ⟨ n, hn, rfl ⟩ := FiniteFieldBasic.exists_nat_cast_eq q_h1 q_prime t;
  by_cases h : n ≤ ( q - 1 ) / 2;
  · obtain ⟨ τ, hτ ⟩ := exists_S_elem_of_le q_h3 n h;
    unfold σ; aesop;
  · obtain ⟨τ, hτ⟩ : ∃ τ : @S q, bitsToNat τ.1 = q - n :=
      exists_S_elem_of_le q_h3 (q - n) (by omega)
    use τ
    simp_all +decide only [not_le, σ, Nat.cast_sub hn.le ]
    aesop

end Elligator.Elligator1
