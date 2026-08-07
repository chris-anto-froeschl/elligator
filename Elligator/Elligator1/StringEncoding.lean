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

* `ι`: the paper's encoding `ι(τ) = ϕ(σ(τ))` from admissible bit strings to curve points.
* `S_card`: the admissible set has `(q + 1) / 2` elements.
* `ι_injective`: `ι` is injective, so encoded strings have distinct curve images.
* `ϕOverF_eq_ιOverS`: the image of `ι` is exactly the image of the Elligator map `ϕ`.

Together, the last two results formalize the paper's conclusion that `ι` is a bijection from `S`
onto `ϕ(F)`.

## References

See [bernstein2013a], Section 3.4, theorem 4.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

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
def ι
  (τ : (@S q))
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : {P : F × F // P ∈ EOverF sq_ne_pm_two hq_card hq_mod} :=
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

omit [DecidableEq F] in
/-- Lower-half representatives resolve the sign ambiguity of `ϕ`.

If two strings in `S` represent equal or opposite field elements, then they in fact represent the
same field element: two distinct integers in `[0, (q - 1) / 2]` cannot be negatives modulo `q`. -/
lemma σ_eq_of_eq_or_eq_neg
  (hq_card : Fintype.card F = q)
  (q_prime : Prime q)
  (τ τ' : @S q)
  (h : (@σ F _ q τ.1) = (@σ F _ q τ'.1) ∨ (@σ F _ q τ.1) = -(@σ F _ q τ'.1)) :
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
theorem ι_injective
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (q_prime : Prime q)
  (hq_mod : q % 4 = 3) :
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
def ιOverS
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : Set (F × F) := Set.range (fun τ : S => ι τ hs_ne_zero sq_ne_pm_two hq_card hq_mod)

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
theorem ϕOverF_eq_ιOverS
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (q_prime : Prime q)
  (hq_mod : q % 4 = 3)
  :
  let ϕOverF := ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod
  let ιOverS := ιOverS hs_ne_zero sq_ne_pm_two hq_card hq_mod
  ϕOverF = ιOverS := by
    dsimp only
    unfold Elligator1.ϕOverF ιOverS ι
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
        exact
          (ϕ_of_t_eq_ϕ_of_neg_t t hs_ne_zero sq_ne_pm_two hq_card hq_mod).symm
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
def ιToϕOverF
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (τ : @S q) :
  {P : F × F // P ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod} :=
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
theorem ιToϕOverF_bijective
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (q_prime : Prime q)
  (hq_mod : q % 4 = 3) :
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

end Elligator.Elligator1
