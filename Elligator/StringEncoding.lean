/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Context
public import Elligator.FiniteFieldBasic

/-!
# Encoding field elements as strings

Both Elligator 1 ([Bernstein2013a], Theorem 4) and Elligator 2 ([Bernstein2013a], Theorem 8)
encode a curve point by a bit string: a string of `b = floor (log 2 q)` bits is read as the
integer `sigma(tau) = sum tau_i 2 ^ i` and the admissible strings are those whose value lies in
the lower half `{0, 1, ..., (q - 1) / 2}` of the field.

Nothing in this construction depends on the particular decoding map, so this file collects the
common material, previously developed inside the Elligator 1 namespace, for `q` an arbitrary
odd prime. Theorem 8 is then proved exactly as Theorem 4, as the paper says: "The rest of the
proof is identical to the proof of Theorem 4 with phi replaced by psi".

## Main results

* `b`, `bitsToNat`, `sigma` (written `σ`), `S`: the string length, the binary value of a bit
  string, the resulting map to the field, and the admissible strings.
* `σ_injective`: for prime `q` the map `σ` is injective.
* `exists_σ_preimage_or_neg`: every field element is `± σ(τ)` for some admissible `τ`.
* `S_card_eq_q_add_one_div_two`: for odd `q` the admissible set has `(q + 1) / 2` elements.

## References

See [Bernstein2013a], Sections 3.4 and 5.4.
-/

@[expose] public section

namespace Elligator.StringEncoding

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {q : ℕ}

section b

/-- `b q` is `⌊log₂ q⌋`, the number of bits needed.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
@[blueprint "def:b"
  (title := "The string length $b$")
  (statement := /--
  For a prime $q$, define the length of the encoded bit strings as
  $$
  b = \lfloor \log_2 q \rfloor .
  $$
  -/)]
def b (q : ℕ) : ℕ := Nat.log 2 q

@[blueprint "lemma:two_pow_b_le_q"
  (title := "$2 ^ b \\leq q$")
  (statement := /--
  With $b = \lfloor \log_2 q \rfloor$ we have $2 ^ b \leq q$; hence the integers
  $0, 1, \ldots, 2 ^ b - 1$ are distinct in $\mathbb{F}_q$.
  -/)]
lemma two_pow_b_le_q (hq : q ≠ 0) : 2 ^ (@b q) ≤ q := Nat.pow_log_le_self 2 hq

lemma q_lt_two_pow_b_succ : q < 2 ^ ((@b q) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

lemma two_pow_b_gt_q_div_two : 2 ^ (@b q) > q / 2 := by
  have h_lt : q < 2 ^ ((@b q) + 1) := q_lt_two_pow_b_succ
  have h_double : 2 ^ ((@b q) + 1) = 2 * 2 ^ (@b q) := pow_succ' 2 _
  omega

lemma half_q_lt_two_pow_b : (q - 1) / 2 < 2 ^ (@b q) := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num), mul_comm]
  rw [← pow_succ']
  apply lt_of_le_of_lt (Nat.sub_le _ _)
  exact Nat.lt_pow_succ_log_self (by norm_num) q

end b

section σ

/-- Convert a bit vector (τ₀, τ₁, ..., τ_{b-1}) to a natural number via binary
expansion: bitsToNat(τ) = Σᵢ τᵢ · 2 ^ i.
-/
@[blueprint "def:bitsToNat"
  (title := "Binary value of a bit string")
  (statement := /--
  A bit string $(\tau_0, \tau_1, \ldots, \tau_{n-1}) \in \{0,1\}^n$ has binary value
  $$
  \sum_i \tau_i 2 ^ i \in \mathbb{Z}_{\geq 0} .
  $$
  -/)]
def bitsToNat {n : ℕ} (τ : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if τ i then 2 ^ (i : ℕ) else 0

/-- `σ` interprets a bit vector `(τ₀, τ₁, ..., τ_{b−1})` as the field element
`∑ᵢ τᵢ · 2ⁱ ∈ Fq`. This is the standard binary-to-integer conversion followed by casting into `F`.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
@[blueprint "def:σ"
  (title := "The string-to-field map $\\sigma$")
  (statement := /--
  Define $\sigma : \{0,1\}^b \to \mathbb{F}_q$ by
  $$
  \sigma(\tau_0, \tau_1, \ldots, \tau_{b-1}) = \sum_i \tau_i 2 ^ i .
  $$
  -/)]
def σ {q : ℕ} (τ : Fin (@b q) → Bool) : F := (bitsToNat τ : F)

/-- S = σ⁻¹({0, 1, 2, ..., (q-1)/2}), the set of bit vectors whose binary value
falls in the lower half {0, 1, ..., (q-1)/2} of F_q.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
@[blueprint "def:S"
  (title := "The admissible string set $S$")
  (statement := /--
  Define the set of admissible bit strings as
  $$
  S = \sigma^{-1}(\{0, 1, 2, \ldots, (q-1)/2\}) ,
  $$
  i.e. the strings whose binary value lies in the lower half of $\mathbb{F}_q$.
  -/)]
def S {q : ℕ} : Finset (Fin (@b q) → Bool) :=
  Finset.univ.filter (fun τ => (bitsToNat τ) ≤ (q - 1) / 2)

lemma bitsToNat_le_full_range {n : ℕ} (τ : Fin n → Bool)
    : bitsToNat τ ≤ ∑ i ∈ Finset.range n, 2 ^ i := by
  rw [Finset.sum_range]
  exact Finset.sum_le_sum fun i _ => by aesop

/-- Every bit-vector of length `n` has binary value less than `2 ^ n`. -/
lemma bitsToNat_lt_two_pow_n {n : ℕ} (τ : Fin n → Bool) : bitsToNat τ < 2 ^ n := by
  have h := bitsToNat_le_full_range τ
  have h' : ∑ i ∈ Finset.range n, 2 ^ i < 2 ^ n := Nat.geomSum_lt (by trivial) (by grind)
  apply lt_of_le_of_lt h h'

lemma bitsToNat_le_q_sub_one_div_two (τ : (@S q)) : bitsToNat τ.1 ≤ (q - 1) / 2 :=
  (Finset.mem_filter.mp τ.2).2

/-- Splitting off the least significant bit gives the standard binary recurrence. -/
lemma bitsToNat_succ {n : ℕ} (τ : Fin (n + 1) → Bool) :
    bitsToNat τ = 2 * bitsToNat (fun i => τ i.succ) + if τ 0 then 1 else 0 := by
  unfold bitsToNat
  -- Peel off the i = 0 term; the rest of the sum reindexes over `Fin n` via `.succ`.
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  -- `2 ^ (i.succ) = 2 * 2 ^ i`, so the two sums match up term by term after simplifying powers.
  simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ']
  have hsum :
        ∑ i : Fin n, (if τ i.succ then 2 * 2 ^ (i : ℕ) else 0)
      = ∑ i : Fin n, 2 * if τ i.succ then 2 ^ (i : ℕ) else 0 :=
    Finset.sum_congr rfl fun i _ => by split <;> ring
  rw [hsum]
  ring

/-- Prefixing a zero bit doubles the value of the remaining bits. -/
@[simp]
lemma bitsToNat_cons_false {n : ℕ} (τ : Fin n → Bool) :
    bitsToNat (Fin.cons false τ) = 2 * bitsToNat τ := by
  simp [bitsToNat_succ]

/-- Prefixing a one bit doubles the value of the remaining bits and adds one. -/
@[simp]
lemma bitsToNat_cons_true {n : ℕ} (τ : Fin n → Bool) :
    bitsToNat (Fin.cons true τ) = 2 * bitsToNat τ + 1 := by
  simp [bitsToNat_succ]

/-- `bitsToNat` is injective: distinct bit-vectors give distinct natural numbers. -/
@[blueprint "lemma:bitsToNat_injective"
  (title := "Binary evaluation is injective")
  (statement := /--
  Distinct bit strings of length $n$ have distinct binary values $\sum_i \tau_i 2 ^ i$.
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

/-- Every natural number less than `2 ^ n` is the binary value of some bit-vector.

This statement doesn't use Function.surjective since it is not viable to get hm into the ∀ m value.
-/
@[blueprint "lemma:bitsToNat_surj"
  (title := "Binary evaluation is onto $\\{0, \\ldots, 2 ^ n - 1\\}$")
  (statement := /--
  Every integer $m$ with $0 \leq m < 2 ^ n$ is the binary value of some bit string of length $n$.
  -/)]
lemma bitsToNat_surj (n : ℕ) (m : ℕ) (hm : m < 2 ^ n) :
    ∃ τ : Fin n → Bool, bitsToNat τ = m := by
  induction n generalizing m with
  | zero =>
    -- `Fin 0 → Bool` has exactly one element, and `m < 2 ^ 0 = 1` forces `m = 0`.
    have hm0 : m = 0 := by simp at hm; omega
    exact ⟨Fin.elim0, by simp [bitsToNat, hm0]⟩
  | succ n ih =>
    -- Recurse on `m / 2` (needs only `n` bits since `m < 2 ^ (n+1)`), then prepend the
    -- low bit `m % 2` - the standard "peel off the last binary digit" step.
    obtain ⟨τ, hτ⟩ := ih (m / 2) (by rw [pow_succ'] at hm; omega)
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · exact ⟨Fin.cons false τ, by simp [hτ]; omega⟩
    · exact ⟨Fin.cons true τ, by simp [hτ]; omega⟩

omit [DecidableEq F] in
lemma natCast_injective_of_prime_card [IsPrimeCard F]
    (a b : ℕ) (ha : a < Fintype.card F) (hb : b < Fintype.card F) (h : (a : F) = (b : F)) :
    a = b := by
  have hchar := ringChar_of_F_eq_q (card_prime (F := F))
  have hmod : a % ringChar F = b % ringChar F := (CharP.cast_eq_iff_mod_eq F (ringChar F)).mp h
  rw [hchar, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  exact hmod

omit [DecidableEq F] in
@[blueprint "lemma:lower_half_neg_eq"
  (title := "The lower half contains no pair of negatives")
  (statement := /--
  Let $q$ be prime and let $a, b \in \{0, 1, \ldots, (q-1)/2\}$ with $a = -b$ in $\mathbb{F}_q$.
  Then $a = b$. This is the step of Theorem 4 that removes the sign ambiguity of $\varphi$.
  -/)]
lemma lower_half_neg_eq [IsPrimeCard F] {a b : ℕ}
    (ha : a ≤ (Fintype.card F - 1) / 2) (hb : b ≤ (Fintype.card F - 1) / 2)
    (heq : (a : F) = -(b : F)) :
    a = b := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a + b = k * Fintype.card F := by
    have h_div : Fintype.card F ∣ (a + b : ℕ) := by
      rw [← ringChar_of_F_eq_q (card_prime (F := F)), ← CharP.cast_eq_zero_iff F]
      simp_all
    exact exists_eq_mul_left_of_dvd h_div
  rcases k <;> grind

omit [DecidableEq F] in
@[blueprint "lemma:σ_injective"
  (title := "$\\sigma$ is injective")
  (statement := /--
  Since $2 ^ b \leq q$, the integers $0, 1, \ldots, 2 ^ b - 1$ are distinct in $\mathbb{F}_q$;
  hence $\sigma$ is injective.
  -/)]
lemma σ_injective [IsPrimeCard F] :
    Function.Injective (@σ F _ (Fintype.card F)) := by
  intro a b h_eq
  apply bitsToNat_injective
  have h1 : bitsToNat a < Fintype.card F :=
    lt_of_lt_of_le (bitsToNat_lt_two_pow_n a) (two_pow_b_le_q Fintype.card_ne_zero)
  have h2 : bitsToNat b < Fintype.card F :=
    lt_of_lt_of_le (bitsToNat_lt_two_pow_n b) (two_pow_b_le_q Fintype.card_ne_zero)
  exact natCast_injective_of_prime_card _ _ h1 h2 h_eq

@[blueprint "lemma:exists_S_elem_of_le"
  (title := "Preimages under $\\sigma$ of the lower half")
  (statement := /--
  Since $2 ^ b > q/2$, the set $\{0, 1, \ldots, (q-1)/2\}$ is a subset of
  $\{0, 1, \ldots, 2 ^ b - 1\}$; hence each of $0, 1, \ldots, (q-1)/2$ has a preimage under
  $\sigma$, lying in $S$.
  -/)]
lemma exists_S_elem_of_le (n : ℕ) (hle : n ≤ (q - 1) / 2) :
    ∃ (τ : (@S q)), bitsToNat τ.1 = n := by
  have hn_pow : n < 2 ^ (@b q) := by
    have h_log : q ≤ 2 ^ Nat.log 2 q * 2 := by
      rw [← pow_succ]
      exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
    have h_pos : 0 < 2 ^ Nat.log 2 q := Nat.two_pow_pos _
    unfold b
    omega
  obtain ⟨τ, hτ⟩ := bitsToNat_surj (@b q) n hn_pow
  exact ⟨⟨τ, by simp [S, hle, hτ]⟩, hτ⟩

omit [DecidableEq F] in
/-- Every field element has a representative in `S` up to sign.
For an odd prime `q` and any `t : F`, there is a string `τ ∈ S` such that
`σ τ = t` or `σ τ = -t`. This is the lower-half representative argument used to prove that the
string encoding covers all of `ϕ(F)` in Theorem 4. -/
@[blueprint "lemma:exists_σ_preimage_or_neg"
  (title := "Every field element is $\\pm\\sigma(\\tau)$ for some $\\tau \\in S$")
  (statement := /--
  For every $t \in \mathbb{F}_q$, at least one of $t, -t$ lies in
  $\{0, 1, \ldots, (q-1)/2\} = \sigma(S)$; that is, there is $\tau \in S$ with
  $\sigma(\tau) = t$ or $\sigma(\tau) = -t$.
  -/)]
lemma exists_σ_preimage_or_neg [IsPrimeCard F] [IsOddCard F] (t : F) :
    ∃ (τ : (@S (Fintype.card F))),
      (@σ F _ (Fintype.card F) τ.1) = t ∨ (@σ F _ (Fintype.card F) τ.1) = -t := by
  have hcard := card_odd (F := F)
  obtain ⟨n, hn, rfl⟩ := exists_nat_cast_eq (card_prime (F := F)) t
  by_cases h : n ≤ (Fintype.card F - 1) / 2
  · obtain ⟨τ, hτ⟩ := exists_S_elem_of_le (q := Fintype.card F) n h
    unfold σ
    aesop
  · obtain ⟨τ, hτ⟩ :=
      exists_S_elem_of_le (q := Fintype.card F) (Fintype.card F - n) (by omega)
    use τ
    simp_all +decide only [not_le, σ, Nat.cast_sub hn.le]
    aesop

/-- Binary evaluation maps the admissible strings `S` onto exactly the natural-number interval
from `0` through `(q - 1) / 2`, as required by the definition of `S` in Theorem 4. -/
@[blueprint "lemma:bitsToNat_image_S"
  (title := "Binary values of the admissible strings")
  (statement := /--
  Since $2 ^ b \leq q$ and $2 ^ b > q/2$, each of $0, 1, \ldots, (q-1)/2$ has a preimage under
  $\sigma$, and the binary values of the strings in $S$ are exactly
  $$
  \{0, 1, \ldots, (q-1)/2\} .
  $$
  -/)]
lemma bitsToNat_image_S : Finset.image bitsToNat (@S q) = Finset.Icc 0 ((q - 1) / 2) := by
  unfold S bitsToNat
  ext m
  constructor
  · grind
  · intro h
    have h' : m < 2 ^ (@b q) := by grind [half_q_lt_two_pow_b]
    obtain ⟨τ, hτ⟩ := bitsToNat_surj (@b q ) m h'
    rw [Finset.mem_image]
    use τ
    aesop

@[blueprint "lemma:S_card_eq_Icc_card"
  (title := "$\\#S$ equals the size of the lower half")
  (statement := /--
  Binary evaluation is injective, hence
  $$
  \#S = \#\{0, 1, \ldots, (q-1)/2\} .
  $$
  -/)]
lemma S_card_eq_Icc_card : (@S q).card = (Finset.Icc 0 ((q - 1) / 2)).card := by
  rw [← bitsToNat_image_S]
  rw [Finset.card_image_of_injective _ bitsToNat_injective]

/-- The lower-half string set `S` has `(q + 1) / 2` elements when `q ≡ 3 (mod 4)`.
This is the cardinality computation used in Theorem 4 of the paper. -/
@[blueprint "lemma:S_card_eq_q_add_one_div_two"
  (title := "$\\#S = (q + 1)/2$")
  (statement := /--
  For odd $q$, the set $S$ has exactly
  $$
  \#S = (q + 1)/2
  $$
  elements.
  -/)]
lemma S_card_eq_q_add_one_div_two (hq_odd : q % 2 = 1) : (@S q).card = (q + 1) / 2 := by
    rw [S_card_eq_Icc_card, Nat.card_Icc]
    grind

end σ
omit [DecidableEq F] in
/-- Lower-half representatives resolve the sign ambiguity of the decoding maps.

If two strings in `S` represent equal or opposite field elements, then they in fact represent the
same field element: two distinct integers in `[0, (q - 1) / 2]` cannot be negatives modulo `q`. -/
lemma σ_eq_of_eq_or_eq_neg [IsPrimeCard F] (τ τ' : @S (Fintype.card F))
    (h : (@σ F _ (Fintype.card F) τ.1) = (@σ F _ (Fintype.card F) τ'.1) ∨
      (@σ F _ (Fintype.card F) τ.1) = -(@σ F _ (Fintype.card F) τ'.1)) :
    (@σ F _ (Fintype.card F) τ.1) = (@σ F _ (Fintype.card F) τ'.1) := by
  rcases h with h | h
  · exact h
  · unfold σ at h
    unfold σ
    rw [lower_half_neg_eq (bitsToNat_le_q_sub_one_div_two τ)
      (bitsToNat_le_q_sub_one_div_two τ') h]

end Elligator.StringEncoding
