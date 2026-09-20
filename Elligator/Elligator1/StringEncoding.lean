/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.InvertedMap
public import Elligator.StringEncoding

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
open Elligator.StringEncoding
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


section ι

variable (D : ParamData F)
variable [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F]

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
def ι (τ : (@S (Fintype.card F))) : {P : F × F // P ∈ D.EOverF} :=
  D.ϕ (σ τ.1)

omit [Field F] [DecidableEq F] [IsNonzeroParam D.s] [IsRegularParam D.s] in
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
theorem S_card : (@S (Fintype.card F)).card = (Fintype.card F + 1) / 2 :=
  S_card_eq_q_add_one_div_two (by have := card_mod_four (F := F); omega)

/-- The Elligator string encoding `ι : S → E(F)` is injective.

Following Theorem 4 of the paper, equality of encoded points first gives equality of their field
representatives up to sign by Theorem 3. Membership in the lower-half set `S` eliminates the
negative case, and injectivity of binary evaluation then identifies the original strings. -/
@[blueprint "thm:thm4-2"
  (title := "Theorem 4.2: injectivity of $\\iota$")
  (statement := /--
  In the situation of Theorem 4, $\iota$ is an injective map from $S$ to $E(\mathbb{F}_q)$.
  -/)]
theorem ι_injective [IsPrimeCard F] :
    Function.Injective (fun τ : (@S (Fintype.card F)) => ι D τ) := by
  intro τ τ' h
  apply Subtype.ext
  apply σ_injective (F := F)
  apply σ_eq_of_eq_or_eq_neg
  exact eq_or_eq_neg_of_ϕ_eq D _ _ h

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
def ιOverS : Set (F × F) :=
  Set.range (fun τ : (@S (Fintype.card F)) => (ι D τ).val)

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
theorem ϕOverF_eq_ιOverS [IsPrimeCard F] : D.ϕOverF = ιOverS D := by
  ext P
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨τ, hτ | hτ⟩ := exists_σ_preimage_or_neg (F := F) t
    · refine ⟨τ, ?_⟩
      change (D.ϕ (σ τ.1)).val = (D.ϕ t).val
      rw [hτ]
    · refine ⟨τ, ?_⟩
      change (D.ϕ (σ τ.1)).val = (D.ϕ t).val
      rw [hτ]
      exact (ϕ_of_t_eq_ϕ_of_neg_t D t).symm
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
def ιToϕOverF (τ : @S (Fintype.card F)) : {P : F × F // P ∈ D.ϕOverF} :=
  ⟨(ι D τ).val, ⟨σ τ.1, rfl⟩⟩

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
theorem ιToϕOverF_bijective [IsPrimeCard F] : Function.Bijective (ιToϕOverF D) := by
  constructor
  · intro τ τ' h
    apply ι_injective D
    apply Subtype.ext
    simpa [ιToϕOverF] using congr_arg Subtype.val h
  · intro P
    have hP : P.val ∈ ιOverS D := by
      rw [← ϕOverF_eq_ιOverS D]
      exact P.prop
    rcases hP with ⟨τ, hτ⟩
    exact ⟨τ, Subtype.ext hτ⟩

end ι

end Elligator.Elligator1
