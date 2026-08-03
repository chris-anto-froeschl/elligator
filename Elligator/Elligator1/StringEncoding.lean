/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.phiProperties
public import Elligator.Elligator1.InvertedMap
public import Elligator.Elligator1.bProperties
public import Elligator.Elligator1.bitsToNatProperties
public import Elligator.Elligator1.SProperties

/-!
# String Encoding

This file formalizes Theorem 4 of the Elligator paper. A bit string in `S` is interpreted as a
lower-half field representative by `σ`, then mapped to the Edwards curve by `ϕ`. Restricting to
the lower half removes the sign ambiguity `ϕ t = ϕ (-t)`.

## Main results

- `ι`: the paper's encoding `ι(τ) = ϕ(σ(τ))` from admissible bit strings to curve points.
- `S_card`: the admissible set has `(q + 1) / 2` elements.
- `ι_injective`: `ι` is injective, so encoded strings have distinct curve images.
- `ϕOverF_eq_ιOverS`: the image of `ι` is exactly the image of the Elligator map `ϕ`.

Together, the last two results formalize the paper's conclusion that `ι` is a bijection from `S`
onto `ϕ(F)`.

## References

See [bernstein2013a] chapter 3.4, theorem 4.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {s : F} (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
variable {q : ℕ} (q_h1 : Fintype.card F = q) (q_h2 : IsPrimePow q) (q_h3 : q % 4 = 3)

/-- The Elligator string encoding from Theorem 4 of the paper.
For an admissible `b`-bit string `τ ∈ S`, `ι τ` is the curve point `ϕ (σ τ)`.
The return subtype records that this point lies on the Edwards curve. -/
@[blueprint
  (title := "The Encoding Function")
  (statement := /--
  In the situation of Definition 2, assume that $q$ is prime, and
  define $b = \lfloor \log_2 q \rfloor$. Define $\sigma : \{0, 1\}^b \to \mathbb{F}_q$ by
  $$
  \sigma(\tau_0, \tau_1, \ldots, \tau_{b-1}) = \sum_i \tau_i 2^i.
  $$

  Define
  $$
  S = \sigma^{-1}(\{0, 1, 2, \ldots, (q - 1)/2\}).
  $$

  Define $\iota : S \to E(\mathbb{F}_q)$ as follows:
  $$
  \iota(\tau) = \varphi(\sigma(\tau)).
  $$

  Original: Chapter "3.4 Encoding as strings": Theorem 4
  -/)]
noncomputable def ι
  (τ : (@S q))
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : {P : F × F // P ∈ EOverF s_h2 q_h1 q_h3} := ϕ (σ τ.1) s_h1 s_h2 q_h1 q_h2 q_h3

/-- The admissible string set `S` has `(q + 1) / 2` elements.
This is the cardinality assertion in Theorem 4. Here `S` consists of the `b`-bit strings whose
binary values lie in the integer interval from `0` through `(q - 1) / 2`. -/
@[blueprint
  (title := "Cardinality of S")
  (statement := /--
  With $S$ as above, $\#S = (q + 1)/2$.
  -/)]
theorem S_card (q_h3 : q % 4 = 3) : (@S q).card = (q + 1) / 2 := S_card_eq_q_add_one_over_two q_h3

/-- Lower-half representatives resolve the sign ambiguity of `ϕ`.

If two strings in `S` represent equal or opposite field elements, then they in fact represent the
same field element: two distinct integers in `[0, (q - 1) / 2]` cannot be negatives modulo `q`. -/
lemma σ_eq_of_eq_or_eq_neg
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  (τ τ' : @S q)
  (h : (@σ F _ q τ.1) = (@σ F _ q τ'.1) ∨ (@σ F _ q τ.1) = -(@σ F _ q τ'.1)) :
  (@σ F _ q τ.1) = (@σ F _ q τ'.1) := by
    rcases h with h | h
    · exact h
    · unfold σ at h
      unfold σ
      rw [lower_half_neg_eq q_h1 q_prime
        (bitsToNat_le_q_sub_one_over_two τ) (bitsToNat_le_q_sub_one_over_two τ') h]

/-- The Elligator string encoding `ι : S → E(F)` is injective.

Following Theorem 4 of the paper, equality of encoded points first gives equality of their field
representatives up to sign by Theorem 3. Membership in the lower-half set `S` eliminates the
negative case, and injectivity of binary evaluation then identifies the original strings. -/
@[blueprint
  (title := "Injectivity of the Encoding Function")
  (statement := /--
  The map $\iota : S \to E(\mathbb F_q)$ is injective.
  -/)]
theorem ι_injective
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  (q_h3 : q % 4 = 3) :
  let q_h2 := by grind
  Function.Injective (fun τ : S => ι τ s_h1 s_h2 q_h1 q_h2 q_h3) := by
    intro q_h2 τ τ' h
    apply Subtype.ext
    apply σ_injective q_h1 q_prime q_h3
    apply σ_eq_of_eq_or_eq_neg q_h1 q_prime
    exact eq_or_eq_neg_of_ϕ_eq _ _ s_h1 s_h2 q_h1 q_h2 q_h3 h

/-- The set of curve points produced by the string encoding `ι`.
This is the range `ι(S)` appearing in Theorem 4 of the paper. -/
@[blueprint "def:ιOverS"]
noncomputable def ιOverS
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : Set (F × F) := Set.range (fun τ : S => ι τ s_h1 s_h2 q_h1 q_h2 q_h3)

/-- The string encoding and the Elligator map have exactly the same image: `ι(S) = ϕ(F)`.
For each `t : F`, one of `t` and `-t` has a lower-half representative `σ τ` with `τ ∈ S`; since
`ϕ t = ϕ (-t)`, this proves that every point in `ϕ(F)` is encoded by `ι`. The reverse inclusion is
immediate from the definition `ι τ = ϕ (σ τ)`. This is the surjectivity-onto-`ϕ(F)` part of
Theorem 4. -/
@[blueprint "thm:thm4-3"]
theorem ϕOverF_eq_ιOverS
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_prime : Prime q)
  (q_h3 : q % 4 = 3)
  :
  let ϕOverF := ϕOverF s_h1 s_h2 q_h1 q_prime.isPrimePow q_h3
  let ιOverS := ιOverS s_h1 s_h2 q_h1 q_prime.isPrimePow q_h3
  ϕOverF = ιOverS := by
    dsimp only
    unfold Elligator1.ϕOverF ιOverS ι
    ext P
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨τ, hτ | hτ⟩ := exists_σ_preimage_or_neg q_h1 q_prime q_h3 t
      · refine ⟨τ, ?_⟩
        change (ϕ (σ τ.1) s_h1 s_h2 q_h1 q_prime.isPrimePow q_h3).val =
          (ϕ t s_h1 s_h2 q_h1 q_prime.isPrimePow q_h3).val
        rw [hτ]
      · refine ⟨τ, ?_⟩
        change (ϕ (σ τ.1) s_h1 s_h2 q_h1 q_prime.isPrimePow q_h3).val =
          (ϕ t s_h1 s_h2 q_h1 q_prime.isPrimePow q_h3).val
        rw [hτ]
        exact (ϕ_of_t_eq_ϕ_of_neg_t t s_h1 s_h2 q_h1 q_prime.isPrimePow q_h3).symm
    · rintro ⟨τ, rfl⟩
      exact ⟨σ τ.1, rfl⟩

end Elligator.Elligator1
