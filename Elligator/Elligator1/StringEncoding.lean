/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
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
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

/-- `ι` maps an element of `S` to `E_over_F` via `ι(τ) = ϕ(σ(τ))`.

Original: Chapter "3.4 Encoding as strings": Theorem 4
-/
noncomputable def ι
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (τ : (@S q))
  : {P : F × F // P ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3}
  :=
  ϕ (σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- 1. statement of Theorem 4:
-- Then #S = (q + 1) / 2;
theorem S_card (q_mod_4_congruent_3 : q % 4 = 3)
  : (@S q).card = (q + 1) / 2 := by
    exact S_card_eq_q_add_one_over_two q_mod_4_congruent_3

theorem ι_injective
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have q_prime_power := by grind
  let ι := ι s s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
  Function.Injective ι := by
    unfold Function.Injective
    intro q_prime_power ι τ τ' h1
    unfold ι Elligator1.ι at h1
    let σ_injective := σ_injective field_cardinality q_prime q_mod_4_congruent_3
    let ϕ_of_τ := ϕ (σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let ϕ_of_τ' := ϕ (σ τ'.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let ϕ_of_neg_τ := ϕ (-σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change ϕ_of_τ = ϕ_of_τ' at h1
    have h2 : ϕ_of_τ = ϕ_of_neg_τ  := by
      unfold ϕ_of_τ ϕ_of_neg_τ
      let h2_1 := ϕ_of_t_eq_ϕ_of_neg_t (σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      grind
    have h3 : ϕ_of_neg_τ = ϕ_of_τ' := by grind
    have h4 : ¬ (∃ (p : { n : F // n ≠ (σ τ.1) ∧ n ≠ -(σ τ.1)}), ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ_of_τ) := by
        let h4_1 := (ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages (σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).mp
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
/-- `ι_over_S` is the set of points produced by `ι`.

Original: Chapter "3.4 Encoding as strings": Theorem 4
-/
noncomputable def ι_over_S
  {s : F}
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Set (F × F) :=
  { P | ∃ (τ : (@S q)), P = ι s s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3 τ }

/-- `ι_over_S` is the set of points produced by `ι`.

Original: Chapter "3.4 Encoding as strings": Theorem 4
-/
noncomputable def ι_over_S'
  {s : F}
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  -- TODO if range works out do this with φ_of_F aswell
  := Set.range (ι s s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3)

theorem ϕ_over_F_eq_ι_over_S'
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime.isPrimePow q_mod_4_congruent_3
  let ι_over_S := ι_over_S' s_h1 s_h2 q field_cardinality q_prime.isPrimePow q_mod_4_congruent_3
  ϕ_over_F = ι_over_S := by
    --intro ϕ_over_F ι_over_S
    --unfold ϕ_over_F Elligator1.ϕ_over_F ι_over_S ι_over_S' Set.range
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
    · rintro ⟨ y, ⟨ τ, rfl ⟩, rfl ⟩ ; exact ⟨ _, rfl ⟩ ;
