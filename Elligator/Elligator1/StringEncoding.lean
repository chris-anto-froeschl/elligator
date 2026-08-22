/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.InvertedMap

/-!
# String Encoding

This file formalizes Theorem 4 of the Elligator paper. A bit string in `S` is interpreted as a
lower-half field representative by `σ`, then mapped to the Edwards curve by `ϕ`. Restricting to
the lower half removes the sign ambiguity `ϕ t = ϕ (-t)`.

## Main results

* `ι`: the paper's encoding `ι(τ) = ϕ(σ(τ))` from admissible bit strings to curve points.
* `S_card`: the admissible set has `(q + 1) / 2` elements.
* `ι_injective`: `ι` is injective, so encoded strings have distinct curve images.
* `ϕOverF_eq_ιOverS`: the image of `ι` is exactly the image of the Elligator map `ϕ`.

Together, the last two results formalize the paper's conclusion that `ι` is a bijection from `S`
onto `ϕ(F)`.

## References

See [Bernstein2013a], Section 3.4, theorem 4.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Primitives.ECC
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates
open Elligator.Elligator1.ReconstructionCoordinates
open Elligator.Elligator1.XbarConsequences
open Elligator.Elligator1.PhiOverFCharacterization

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
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
lemma two_pow_b_le_q (hq_mod : q % 4 = 3) : 2 ^ (@b q) ≤ q := by
  apply Nat.pow_log_le_self
  intro hqzero
  rw [hqzero] at hq_mod
  contradiction

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

/-- `σ` interprets a bit vector `(τ₀, τ₁, …, τ_{b−1})` as the field element
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

lemma natCast_injective_of_prime_card {q : ℕ}
    (hq_card : Fintype.card F = q) (q_prime : Prime q)
    (a b : ℕ) (ha : a < q) (hb : b < q) (h : (a : F) = (b : F))
    : a = b := by
  have hchar := ringChar_of_F_eq_q hq_card q_prime
  have hmod : a % ringChar F = b % ringChar F := (CharP.cast_eq_iff_mod_eq F (ringChar F)).mp h
  rw [hchar, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  exact hmod

@[blueprint "lemma:lower_half_neg_eq"
  (title := "The lower half contains no pair of negatives")
  (statement := /--
  Let $q$ be prime and let $a, b \in \{0, 1, \ldots, (q-1)/2\}$ with $a = -b$ in $\mathbb{F}_q$.
  Then $a = b$. This is the step of Theorem 4 that removes the sign ambiguity of $\varphi$.
  -/)]
lemma lower_half_neg_eq {a b : ℕ}
    (hq_card : Fintype.card F = q) (hq : Prime q)
    (ha : a ≤ (q - 1) / 2) (hb : b ≤ (q - 1) / 2) (heq : (a : F) = -(b : F)) :
    a = b := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a + b = k * q := by
    have h_div : q ∣ (a + b : ℕ) := by
      rw [← ringChar_of_F_eq_q hq_card hq, ← CharP.cast_eq_zero_iff F]
      simp_all
    exact exists_eq_mul_left_of_dvd h_div
  rcases k <;> grind

@[blueprint "lemma:σ_injective"
  (title := "$\\sigma$ is injective")
  (statement := /--
  Since $2 ^ b \leq q$, the integers $0, 1, \ldots, 2 ^ b - 1$ are distinct in $\mathbb{F}_q$;
  hence $\sigma$ is injective.
  -/)]
lemma σ_injective (hq_card : Fintype.card F = q) (q_prime : Prime q) (hq_mod : q % 4 = 3) :
    Function.Injective (@σ F _ q) := by
  intro a b h_eq
  apply bitsToNat_injective
  have h1 : bitsToNat a < q := lt_of_lt_of_le (bitsToNat_lt_two_pow_n a) (two_pow_b_le_q hq_mod)
  have h2 : bitsToNat b < q := lt_of_lt_of_le (bitsToNat_lt_two_pow_n b) (two_pow_b_le_q hq_mod)
  exact natCast_injective_of_prime_card hq_card q_prime _ _ h1 h2 h_eq

@[blueprint "lemma:exists_S_elem_of_le"
  (title := "Preimages under $\\sigma$ of the lower half")
  (statement := /--
  Since $2 ^ b > q/2$, the set $\{0, 1, \ldots, (q-1)/2\}$ is a subset of
  $\{0, 1, \ldots, 2 ^ b - 1\}$; hence each of $0, 1, \ldots, (q-1)/2$ has a preimage under
  $\sigma$, lying in $S$.
  -/)]
lemma exists_S_elem_of_le (hq_mod : q % 4 = 3)
    (n : ℕ) (hle : n ≤ (q - 1) / 2) :
    ∃ (τ : (@S q)), bitsToNat τ.1 = n := by
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
    (hq_card : Fintype.card F = q) (q_prime : Prime q) (hq_mod : q % 4 = 3) (t : F)
    : ∃ (τ : (@S q)), (@σ F _ q τ.1) = t ∨ (@σ F _ q τ.1) = -t := by
  obtain ⟨n, hn, rfl⟩ := exists_nat_cast_eq hq_card q_prime t
  by_cases h : n ≤ ( q - 1 ) / 2
  · obtain ⟨ τ, hτ ⟩ := exists_S_elem_of_le hq_mod n h
    unfold σ
    aesop
  · obtain ⟨τ, hτ⟩ := exists_S_elem_of_le hq_mod (q - n) (by omega)
    use τ
    simp_all +decide only [not_le, σ, Nat.cast_sub hn.le ]
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
  For $q \equiv 3 \pmod 4$, the set $S$ has exactly
  $$
  \#S = (q + 1)/2
  $$
  elements.
  -/)]
lemma S_card_eq_q_add_one_div_two (hq_mod : q % 4 = 3) : (@S q).card = (q + 1) / 2 := by
    rw [S_card_eq_Icc_card, Nat.card_Icc]
    grind

end σ

section ι

/-- The Elligator string encoding from Theorem 4 of the paper.
For an admissible `b`-bit string `τ ∈ S`, `ι τ` is the curve point `ϕ (σ τ)`. The return subtype
records that this point lies on the Edwards curve. -/
@[blueprint "def:ι"
  (title := "The string encoding $\\iota$")
  (statement := /--
  In the situation of Definition 2, assume that $q$ is prime, and let $b$, $\sigma$ and $S$ be
  as above. Define
  $$
    \iota : S \to E(\mathbb{F}_q)
  $$
  by $\iota(\tau) = \varphi(\sigma(\tau))$.
  -/)]
def ι (τ : (@S q))
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    {P : F × F // P ∈ EOverF sq_ne_pm_two hq_card hq_mod} :=
  ϕ (σ τ.1) hs_ne_zero sq_ne_pm_two hq_card hq_mod

/-- The admissible string set `S` has `(q + 1) / 2` elements.
This is the cardinality assertion in Theorem 4. Here `S` consists of the `b`-bit strings whose
binary values lie in the integer interval from `0` through `(q - 1) / 2`. -/
@[blueprint
  (title := "Theorem 4.1: cardinality of $S$")
  (statement := /--
  In the situation of Theorem 4, the set of admissible strings satisfies
  $$
  \#S = (q + 1)/2 .
  $$
  -/)]
theorem S_card (hq_mod : q % 4 = 3) : (@S q).card = (q + 1) / 2 :=
  S_card_eq_q_add_one_div_two hq_mod

/-- Lower-half representatives resolve the sign ambiguity of `ϕ`.

If two strings in `S` represent equal or opposite field elements, then they in fact represent the
same field element: two distinct integers in `[0, (q - 1) / 2]` cannot be negatives modulo `q`. -/
lemma σ_eq_of_eq_or_eq_neg (hq_card : Fintype.card F = q) (q_prime : Prime q)
    (τ τ' : @S q) (h : (@σ F _ q τ.1) = (@σ F _ q τ'.1) ∨ (@σ F _ q τ.1) = -(@σ F _ q τ'.1)) :
    (@σ F _ q τ.1) = (@σ F _ q τ'.1) := by
  rcases h with h | h
  · exact h
  · unfold σ at h
    unfold σ
    rw [lower_half_neg_eq hq_card q_prime
      (bitsToNat_le_q_sub_one_div_two τ) (bitsToNat_le_q_sub_one_div_two τ') h]

/-- The Elligator string encoding `ι : S → E(F)` is injective.

Following Theorem 4 of the paper, equality of encoded points first gives equality of their field
representatives up to sign by Theorem 3. Membership in the lower-half set `S` eliminates the
negative case, and injectivity of binary evaluation then identifies the original strings. -/
@[blueprint "thm:thm4-2"
  (title := "Theorem 4.2: injectivity of $\\iota$")
  (statement := /--
  In the situation of Theorem 4, $\iota$ is an injective map from $S$ to $E(\mathbb{F}_q)$.
  -/)]
theorem ι_injective (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (q_prime : Prime q) (hq_mod : q % 4 = 3) :
    Function.Injective (fun τ : S => ι τ hs_ne_zero sq_ne_pm_two hq_card hq_mod) := by
  intro τ τ' h
  apply Subtype.ext
  apply σ_injective hq_card q_prime hq_mod
  apply σ_eq_of_eq_or_eq_neg hq_card q_prime
  exact eq_or_eq_neg_of_ϕ_eq _ _ hs_ne_zero sq_ne_pm_two hq_card hq_mod h

/-- The set of curve points produced by the string encoding `ι`.
This is the range `ι(S)` appearing in Theorem 4 of the paper. -/
@[blueprint "def:ιOverS"
  (title := "The image $\\iota(S)$")
  (statement := /--
  The set of curve points produced by the string encoding,
  $$
  \iota(S) = \{\varphi(\sigma(\tau)) : \tau \in S\} \subseteq E(\mathbb{F}_q) .
  $$
  -/)]
def ιOverS (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    Set (F × F) :=
  Set.range (fun τ : S => ι τ hs_ne_zero sq_ne_pm_two hq_card hq_mod)

/-- The string encoding and the Elligator map have exactly the same image: `ι(S) = ϕ(F)`.
For each `t : F`, one of `t` and `-t` has a lower-half representative `σ τ` with `τ ∈ S`; since
`ϕ t = ϕ (-t)`, this proves that every point in `ϕ(F)` is encoded by `ι`. The reverse inclusion is
immediate from the definition `ι τ = ϕ (σ τ)`. This is the surjectivity-onto-`ϕ(F)` part of
Theorem 4. -/
@[blueprint "thm:thm4-3"
  (title := "Theorem 4.3: $\\iota(S) = \\varphi(\\mathbb{F}_q)$")
  (statement := /--
  In the situation of Theorem 4, $\iota(S) = \varphi(\mathbb{F}_q)$.
  -/)]
theorem ϕOverF_eq_ιOverS (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (q_prime : Prime q) (hq_mod : q % 4 = 3) :
    let ϕOverF := ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let ιOverS := ιOverS hs_ne_zero sq_ne_pm_two hq_card hq_mod
    ϕOverF = ιOverS := by
  dsimp only
  unfold PhiOverFCharacterization.ϕOverF ιOverS ι
  ext P
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨τ, hτ | hτ⟩ := exists_σ_preimage_or_neg hq_card q_prime hq_mod t
    · refine ⟨τ, ?_⟩
      dsimp
      rw [hτ]
    · refine ⟨τ, ?_⟩
      dsimp
      rw [hτ]
      exact (ϕ_of_t_eq_ϕ_of_neg_t t hs_ne_zero sq_ne_pm_two hq_card hq_mod).symm
  · rintro ⟨τ, rfl⟩
    exact ⟨σ τ.1, rfl⟩

/-- The encoding `ι`, with its codomain restricted to the image `ϕ(F)`.

Unlike `ι`, whose codomain is the full Edwards curve, this map records in its result type the
stronger fact that every encoded point belongs to the image of `ϕ`. -/
@[blueprint "def:ιToϕOverF"
  (title := "The encoding $\\iota$ as a map onto $\\varphi(\\mathbb{F}_q)$")
  (statement := /--
  The string encoding of Theorem 4, viewed as a map
  $$
  \iota : S \to \varphi(\mathbb{F}_q)
  $$
  with codomain the image of $\varphi$ rather than all of $E(\mathbb{F}_q)$.
  -/)]
def ιToϕOverF (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (τ : @S q) : {P : F × F // P ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod} :=
  ⟨(ι τ hs_ne_zero sq_ne_pm_two hq_card hq_mod).val, ⟨σ τ.1, rfl⟩⟩

/-- The encoding `ι` is a bijection from `S` onto `ϕ(F)`.
The codomain restriction in `ιToϕOverF` makes “onto `ϕ(F)`” literal in the type. Injectivity is
`ι_injective`, while surjectivity is the image equality `ϕOverF_eq_ιOverS`. -/
@[blueprint "thm:ι-bijective"
  (title := "$\\iota$ is a bijection from $S$ onto $\\varphi(\\mathbb{F}_q)$")
  (statement := /--
  Combining the injectivity of $\iota$ with $\iota(S) = \varphi(\mathbb{F}_q)$: the map
  $$
  \iota : S \to \varphi(\mathbb{F}_q)
  $$
  is a bijection.
  -/)]
theorem ιToϕOverF_bijective (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (q_prime : Prime q) (hq_mod : q % 4 = 3) :
    Function.Bijective (ιToϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod) := by
  constructor
  · intro τ τ' h
    apply ι_injective hs_ne_zero sq_ne_pm_two hq_card q_prime hq_mod
    apply Subtype.ext
    simpa [ιToϕOverF] using congr_arg Subtype.val h
  · intro P
    have hP : P.val ∈ ιOverS hs_ne_zero sq_ne_pm_two hq_card hq_mod := by
      rw [← ϕOverF_eq_ιOverS hs_ne_zero sq_ne_pm_two hq_card q_prime hq_mod]
      exact P.prop
    rcases hP with ⟨τ, hτ⟩
    refine ⟨τ, Subtype.ext ?_⟩
    exact hτ

end ι

end Elligator.Elligator1
