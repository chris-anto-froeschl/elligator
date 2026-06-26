/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Architect
public import Elligator.FiniteFieldBasic
public import Elligator.LegendreSymbol
public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.phiProperties
public import Elligator.Elligator1.InvertedMap
public import Elligator.Elligator1.bProperties
public import Elligator.Elligator1.bitsToNatProperties
public import Elligator.Elligator1.SProperties

@[expose] public section

/-!
# String Encoding

In this file we collect the main results regarding the string encoding logic of Elligator 1.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3 theorem 4.
-/

namespace Elligator.Elligator1

-- Original-Reference: Theorem 4
section StringEncoding

variable {F : Type*} [Field F] [Fintype F]
variable {s : F} (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

/-- Original: Chapter "3.4 Encoding as strings": Theorem 4 -/
@[blueprint
  (title := "The Encoding Function")
  (statement := /--
  In the situation of Definition 2, assume that $q$ is prime, and define $b = \lfloor \log_2 q \rfloor$. Define $\sigma : \{0, 1\}^b \to \mathbb{F}_q$ by
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
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (τ : (@S q))
  : {P : F × F // P ∈ EOverF s_h2 field_cardinality q_prime_power q_mod_4_congruent_3}
  := ϕ (σ τ.1) s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3

@[blueprint
  (title := "Cardinality of S")
  (statement := /--
  In the situation of Definition 2, assume that $q$ is prime, and define $b = \lfloor \log_2 q \rfloor$. Define $\sigma : \{0, 1\}^b \to \mathbb{F}_q$ by
  $$
  \sigma(\tau_0, \tau_1, \ldots, \tau_{b-1}) = \sum_i \tau_i 2^i.
  $$

  Define
  $$
  S = \sigma^{-1}(\{0, 1, 2, \ldots, (q - 1)/2\}).
  $$

  Then $\#S = (q + 1)/2$;

  Original: Chapter "3.4 Encoding as strings": 1. statement of Theorem 4
  -/)]
theorem S_card (q_mod_4_congruent_3 : q % 4 = 3)
  : (@S q).card = (q + 1) / 2 := by
    exact S_card_eq_q_add_one_over_two q_mod_4_congruent_3

@[blueprint
  (title := "Cardinality of S")
  (statement := /--
  In the situation of Definition 2, assume that $q$ is prime, and define $b = \lfloor \log_2 q \rfloor$. Define $\sigma : \{0, 1\}^b \to \mathbb{F}_q$ by
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

  Then $\#S = (q + 1)/2$;

  Original: Chapter "3.4 Encoding as strings": 1. statement of Theorem 4
  -/)]
theorem ι_injective
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have q_prime_power := by grind
  let ι := ι s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
  Function.Injective ι := by
    unfold Function.Injective
    intro q_prime_power ι τ τ' h1
    unfold ι Elligator1.ι at h1
    let σ_injective := σ_injective field_cardinality q_prime q_mod_4_congruent_3
    let ϕ_of_τ := ϕ (σ τ.1) s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
    let ϕ_of_τ' := ϕ (σ τ'.1) s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
    let ϕ_of_neg_τ := ϕ (-σ τ.1) s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
    change ϕ_of_τ = ϕ_of_τ' at h1
    have h2 : ϕ_of_τ = ϕ_of_neg_τ  := by
      unfold ϕ_of_τ ϕ_of_neg_τ
      let h2_1 := ϕ_of_t_eq_ϕ_of_neg_t (σ τ.1) s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
      grind
    have h3 : ϕ_of_neg_τ = ϕ_of_τ' := by grind
    have h4 : ¬ (∃ (p : { n : F // n ≠ (σ τ.1) ∧ n ≠ -(σ τ.1)}), ϕ p.val s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ_of_τ) := by
        let h4_1 := (ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages (σ τ.1) s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3).mp
        unfold ϕ_of_τ ϕ_of_neg_τ at h2
        convert h4_1 ( congr_arg Subtype.val h2 ) using 1
        simp +decide [ Subtype.ext_iff ]
        rfl
    have h5 : (@σ F _ q τ.1) = (@σ F _ q τ'.1) ∨ (@σ F _ q τ.1) = -(@σ F _ q τ'.1) := by
      simp_all
      grind
    -- Since τ and τ ∈ {0, ..., (q-1)/2}
    have h6 : (@σ F _ q τ.1) = (@σ F _ q τ'.1) := by
      cases' h5 with h6_1 h6_1 <;> simp_all +decide [ σ ];
      have h6_2 : bitsToNat τ.val = bitsToNat τ'.val := by
        have h6_2_1 : bitsToNat τ.val ≤ (q - 1) / 2 ∧ bitsToNat τ'.val ≤ (q - 1) / 2 := by exact ⟨bitsToNat_le_q_sub_one_over_two τ , bitsToNat_le_q_sub_one_over_two τ'⟩
        have h6_2_2 : (bitsToNat τ.val : F) = -((bitsToNat τ'.val) : F) := by grind
        let h6_2_3 := lower_half_neg_eq field_cardinality q_prime h6_2_1.1 h6_2_1.2 h6_2_2
        grind
      grind
    grind

-- TODO remove this since prime version is better
/-- `ιOverS` is the set of points produced by `ι`.

Original: Chapter "3.4 Encoding as strings": Theorem 4
-/
noncomputable def ιOverS
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Set (F × F) :=
  { P | ∃ (τ : (@S q)), P = ι s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3 τ }

/-- `ιOverS` is the set of points produced by `ι`.

Original: Chapter "3.4 Encoding as strings": Theorem 4
-/
noncomputable def ιOverS'
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  -- TODO if range works out do this with φ_of_F aswell
  := Set.range (ι s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3)

@[blueprint "thm:thm4-3"]
theorem ϕOverF_eq_ιOverS'
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕOverF := ϕOverF s_h1 s_h2 field_cardinality q_prime.isPrimePow q_mod_4_congruent_3
  let ιOverS := ιOverS' s_h1 s_h2 field_cardinality q_prime.isPrimePow q_mod_4_congruent_3
  ϕOverF = ιOverS := by
    --intro ϕOverF ιOverS
    --unfold ϕOverF Elligator1.ϕOverF ιOverS ιOverS' Set.range
    --apply Set.Subset.antisymm
    refine' Set.ext fun x => ⟨ _, _ ⟩;
    · rintro ⟨ t, rfl ⟩;
      obtain ⟨ τ, hτ ⟩ := exists_σ_preimage_or_neg field_cardinality q_prime q_mod_4_congruent_3 t;
      cases' hτ with hτ hτ;
      · exact ⟨ _, ⟨ τ, rfl ⟩, by aesop ⟩;
      · refine' ⟨ _, ⟨ τ, rfl ⟩, _ ⟩;
        unfold ι;
        rw [ hτ, ϕ_of_t_eq_ϕ_of_neg_t ];
        norm_num +zetaDelta at *;
    · rintro ⟨ y, ⟨ τ, rfl ⟩, rfl ⟩; exact ⟨ _, rfl ⟩;
