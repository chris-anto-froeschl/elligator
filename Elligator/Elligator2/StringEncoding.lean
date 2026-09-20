/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator2.InvertedMap
public import Elligator.StringEncoding

/-!
# String encoding for Elligator 2

This file formalizes Theorem 8 of [Bernstein2013a]: for a prime `q ≡ 1 (mod 4)` with `A ^ 2 - 4B`
a non-square, the map `ψ` is defined on all of `F_q` by Theorem 5, and composing it with the
lower-half string interpretation `σ` of Section 3.4 gives an injective encoding `ι` of the
admissible strings `S` onto `ψ(F_q)`.

As the paper puts it, "The rest of the proof is identical to the proof of Theorem 4 with `φ`
replaced by `ψ`, `τ` replaced by `ρ`, Theorem 1 replaced by Theorem 5, and Theorem 3 replaced by
Theorem 7". Accordingly this file reuses the generic material of `Elligator.StringEncoding`, the
same file that the Elligator 1 proof of Theorem 4 uses, and only supplies the two Elligator 2
inputs: `ψ(-r) = ψ(r)` and the description of the preimages from Theorem 7.

## Main results

* `mem_R_of_nonsquare_disc`: under the hypotheses of Theorem 8 every element of `F_q` is
  admissible, so `ψ` is total.
* `ι`: the encoding `ι(ρ) = ψ(σ(ρ))`.
* `S_card`: the admissible set has `(q + 1) / 2` elements.
* `ι_injective`: `ι` is injective.
* `ψOverR_eq_ιOverS`: the image of `ι` is exactly `ψ(F_q)`.
* `ιToψOverR_bijective`: `ι` is a bijection from `S` onto `ψ(F_q)`.

## References

See [Bernstein2013a], Section 5.4, Theorem 8.
-/

@[expose] public section

namespace Elligator.Elligator2

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.StringEncoding
open Elligator.Primitives.ECC
open Elligator.Elligator2.CurveParameters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (P : ParamData F)
variable [IsCardOneModFour F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u]
  [IsSqrtFun P.sqrt] [IsNonsquareDisc P.A P.B]

omit [DecidableEq F] [IsSqrtFun P.sqrt] in
/-- Under the hypotheses of Theorem 8 the admissible set is all of `F_q`, by Theorem 5. -/
lemma mem_R_of_nonsquare_disc (r : F) : r ∈ P.R := by
  rw [R_eq_univ P]
  exact Set.mem_univ r

/-- The Elligator 2 string encoding of Theorem 8: `ι(ρ) = ψ(σ(ρ))`. -/
@[blueprint "def:iota2"
  (title := "The string encoding $\\iota$ of Elligator 2")
  (statement := /--
  In the situation of Definition 6, assume that $q$ is prime, that $q \equiv 1 \pmod 4$, and that
  $A ^ 2 - 4B$ is not a square in $\mathbb{F}_q$. With $b$, $\sigma$ and $S$ as in Theorem 4,
  define
  $$
  \iota : S \to E(\mathbb{F}_q)
  $$
  by $\iota(\rho) = \psi(\sigma(\rho))$.
  -/)]
def ι (ρ : (@S (Fintype.card F))) : {Q : F × F // Q ∈ P.EOverF} :=
  ψPoint P (σ ρ.1) (mem_R_of_nonsquare_disc P _)

lemma ι_val (ρ : (@S (Fintype.card F))) : (ι P ρ).val = P.ψ (σ ρ.1) := rfl

omit [Field F] [DecidableEq F] [IsRegularABParam P.A P.B] [IsNonsquareParam P.u]
  [IsSqrtFun P.sqrt] [IsNonsquareDisc P.A P.B] in
/-- Part 1 of Theorem 8: the admissible string set `S` has `(q + 1) / 2` elements. -/
@[blueprint "thm:thm8-1"
  (title := "Theorem 8.1: cardinality of $S$")
  (statement := /--
  In the situation of Theorem 8, the set of admissible strings satisfies
  $$
  \#S = (q + 1)/2 .
  $$
  -/)]
theorem S_card : (@S (Fintype.card F)).card = (Fintype.card F + 1) / 2 :=
  S_card_eq_q_add_one_div_two (by have := card_mod_four_eq_one (F := F); omega)

/-- Part 2 of Theorem 8: the encoding `ι` is injective.

Exactly as in Theorem 4: equality of the encoded points gives equality of the field
representatives up to sign by Theorem 7, and membership in the lower half `S` removes the sign. -/
@[blueprint "thm:thm8-2"
  (title := "Theorem 8.2: injectivity of $\\iota$")
  (statement := /--
  In the situation of Theorem 8, $\iota$ is an injective map from $S$ to $E(\mathbb{F}_q)$.
  -/)]
theorem ι_injective [IsPrimeCard F] :
    Function.Injective (fun ρ : (@S (Fintype.card F)) => ι P ρ) := by
  intro ρ ρ' h
  apply Subtype.ext
  apply σ_injective (F := F)
  refine σ_eq_of_eq_or_eq_neg ρ ρ' ?_
  have h' : P.ψ (σ ρ.1) = P.ψ (σ ρ'.1) := congrArg Subtype.val h
  exact eq_or_eq_neg_of_ψ_eq P (mem_R_of_nonsquare_disc P _) (mem_R_of_nonsquare_disc P _) h'

/-- The set of curve points produced by the string encoding `ι`. -/
@[blueprint "def:iota2OverS"
  (title := "The image $\\iota(S)$")
  (statement := /--
  The set of curve points produced by the string encoding,
  $$
  \iota(S) = \{\psi(\sigma(\rho)) : \rho \in S\} \subseteq E(\mathbb{F}_q) .
  $$
  -/)]
def ιOverS : Set (F × F) :=
  Set.range (fun ρ : (@S (Fintype.card F)) => (ι P ρ).val)

/-- Part 3 of Theorem 8: the image of the string encoding is exactly `ψ(F_q)`.

For each `t : F` one of `t` and `-t` has a lower-half representative `σ ρ` with `ρ ∈ S`, and
`ψ t = ψ (-t)`. -/
@[blueprint "thm:thm8-3"
  (title := "Theorem 8.3: $\\iota(S) = \\psi(\\mathbb{F}_q)$")
  (statement := /--
  In the situation of Theorem 8, $\iota(S) = \psi(\mathbb{F}_q)$.
  -/)]
theorem ψOverR_eq_ιOverS [IsPrimeCard F] : P.ψOverR = ιOverS P := by
  ext Q
  constructor
  · rintro ⟨r, -, rfl⟩
    obtain ⟨ρ, hρ | hρ⟩ := exists_σ_preimage_or_neg (F := F) r
    · refine ⟨ρ, ?_⟩
      change P.ψ (σ ρ.1) = P.ψ r
      rw [hρ]
    · refine ⟨ρ, ?_⟩
      change P.ψ (σ ρ.1) = P.ψ r
      rw [hρ, ψ_neg P r]
  · rintro ⟨ρ, rfl⟩
    exact ⟨σ ρ.1, mem_R_of_nonsquare_disc P _, rfl⟩

/-- The encoding `ι`, with its codomain restricted to the image `ψ(F_q)`. -/
def ιToψOverR (ρ : @S (Fintype.card F)) : {Q : F × F // Q ∈ P.ψOverR} :=
  ⟨(ι P ρ).val, ⟨σ ρ.1, mem_R_of_nonsquare_disc P _, rfl⟩⟩

/-- Combining the last two parts of Theorem 8: `ι` is a bijection from `S` onto `ψ(F_q)`. -/
@[blueprint "thm:iota2-bijective"
  (title := "$\\iota$ is a bijection from $S$ onto $\\psi(\\mathbb{F}_q)$")
  (statement := /--
  Combining the injectivity of $\iota$ with $\iota(S) = \psi(\mathbb{F}_q)$: the map
  $$
  \iota : S \to \psi(\mathbb{F}_q)
  $$
  is a bijection.
  -/)]
theorem ιToψOverR_bijective [IsPrimeCard F] : Function.Bijective (ιToψOverR P) := by
  constructor
  · intro ρ ρ' h
    apply ι_injective P
    apply Subtype.ext
    simpa [ιToψOverR] using congrArg Subtype.val h
  · intro Q
    have hQ : Q.val ∈ ιOverS P := by
      rw [← ψOverR_eq_ιOverS P]
      exact Q.prop
    obtain ⟨ρ, hρ⟩ := hQ
    exact ⟨ρ, Subtype.ext hρ⟩

end Elligator.Elligator2
