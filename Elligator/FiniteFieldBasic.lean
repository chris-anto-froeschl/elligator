/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl, Matthias Güdemann
-/
module

public import Elligator.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Finite Field Basic

In this file we introduce some generally helpful lemmas for the finite field `F` with
`q` fulfilling `IsPrimePow`/`Prime`, `Fintype.card F = q` and `q % 4 = 3`.

The assumption `IsPrimePow q` of [bernstein2013a] never has to be stated: by
`card_isPrimePow` it is a consequence of `Fintype.card F = q`, so `q` ranges over exactly the
prime powers congruent to `3` modulo `4`. Conversely, `prime_of_natCast_surjective` shows that
representing field elements by the naturals `0, 1, …, q - 1`, as the string encoding of
Section 3.4 does, is possible only when `q` is prime.

## References

See [bernstein2013a] for the original account on this specifc finite field.
-/

@[expose] public section

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ}

namespace Elligator.FiniteFieldBasic

/-- The cardinality of a finite field is always a prime power.

This is why no statement of this development has to assume `IsPrimePow q`: the hypothesis
`Fintype.card F = q` already forces `q` to be a prime power, so all results proved for a finite
field `F` with `Fintype.card F = q` and `q % 4 = 3` are exactly the results of [bernstein2013a]
for an arbitrary prime power `q ≡ 3 (mod 4)`. -/
lemma card_isPrimePow (hq_card : Fintype.card F = q) : IsPrimePow q := by
  rw [← hq_card]
  exact FiniteField.isPrimePow_card F

omit [Field F] in
lemma q_odd (hq_mod : q % 4 = 3) : Odd q := by
  rw [Nat.odd_iff]
  omega

omit [Field F] in
lemma q_sub_one_div_two_odd (hq_mod : q % 4 = 3) : Odd ((q - 1) / 2) := by
  rw [Nat.odd_iff]
  omega

omit [Field F] in
lemma q_sub_one_even (hq_mod : q % 4 = 3) : Even (q - 1) := by
  rw [Nat.even_iff]
  omega

omit [Fintype F] in
lemma one_ne_zero : (1 : F) ≠ 0 := by grind

lemma q_add_one_div_four_ne_zero (hq_mod : q % 4 = 3) : (1 + q) / 4 ≠ 0 := by grind

lemma q_add_one_div_two_ne_zero (hq_mod : q % 4 = 3) : (1 + q) / 2 ≠ 0 := by grind

lemma two_ne_zero {F : Type*} [Field F] [Fintype F] {q : ℕ}
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (2 : F) ≠ 0 := by
  intro h
  -- turn `(2 : F) = 0` into a divisibility statement about the characteristic
  have hdvd : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F (ringChar F) 2).mp h
  -- ringChar F ∣ 2 and ringChar F ≠ 1 (F is nontrivial) forces ringChar F = 2
  have hp : ringChar F = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 (CharP.char_ne_one F (ringChar F))
    · exact h1
  haveI : CharP F 2 := by
    rw [← hp]
    exact ringChar.charP F
  -- a finite field of characteristic 2 has cardinality a power of 2
  obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
  have hqeq : q = 2^(n : ℕ) := by rw [← hq_card, hcard]
  have hdvd2 : (2 : ℕ) ∣ q := by
    rw [hqeq]
    exact dvd_pow_self 2 n.pos.ne'
  -- 2 ∣ q contradicts q % 4 = 3
  omega

lemma four_ne_zero
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (4 : F) ≠ 0 := by
    have h1 : (4 : F) = 2 * 2 := by norm_num
    rw [h1]
    apply mul_ne_zero
    · exact (two_ne_zero hq_card hq_mod)
    · exact (two_ne_zero hq_card hq_mod)

lemma ringChar_ne_two (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : ringChar F ≠ 2 := by
    intro h
    refine two_ne_zero hq_card hq_mod ?_
    have h' : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).mpr (by rw [h])
    exact h'

omit [Fintype F] in
lemma neg_one_ne_zero : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero

lemma neg_one_non_square (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : ¬IsSquare (-1 : F) := by grind [FiniteField.isSquare_neg_one_iff]

omit [Fintype F] in
lemma one_sub_t_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : (1 : F) - t.val ≠ 0 :=
  sub_ne_zero.mpr t.property.1.symm

omit [Fintype F] in
lemma one_add_t_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : (1 : F) + t.val ≠ 0 := by
  intro h
  rw [add_comm] at h
  exact t.property.2 (eq_neg_of_add_eq_zero_left h)

omit [Fintype F] in
lemma neg_t_ne_one_and_neg_t_ne_neg_one (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
  -t.val ≠ 1 ∧ -t.val ≠ -1 :=
    ⟨fun h => t.property.2 (neg_eq_iff_eq_neg.mp h), fun h => t.property.1 (neg_inj.mp h)⟩

omit [Field F] in
lemma one_add_q_div_four_mul_two_eq_one_add_q_div_two (hq_mod : q % 4 = 3)
  : ((1 + q) / 4 * 2) = (1 + q) / 2 := by omega

lemma ringChar_of_F_eq_q (hq_card : Fintype.card F = q) (q_prime : Prime q) : ringChar F = q := by
  have := FiniteField.card F (ringChar F)
  aesop

lemma fin_to_finfield_injective (hq_card : Fintype.card F = q) (q_prime : Prime q)
  : Function.Injective (fun n : Fin q => (n : F)) := by
    have h : CharP F q := by
      rw [← ringChar_of_F_eq_q hq_card q_prime]
      exact ringChar.charP F
    intro a b hab
    exact Fin.ext (CharP.natCast_injOn_Iio F q a.isLt b.isLt hab)

/-- Every element of `F` is the cast of some `n : Fin q`: the cast `Fin q → F` is injective
and `Fin q` and `F` have the same cardinality, so it is bijective. -/
lemma exists_fin_cast_eq (hq_card : Fintype.card F = q) (q_prime : Prime q) (t : F)
  : ∃ n : Fin q, (n : F) = t := by
    -- `Fin q` and `F` have matching cardinalities.
    have hcard : Fintype.card (Fin q) = Fintype.card F := by rw [Fintype.card_fin, hq_card]
    -- An injective map between finite types of equal cardinality is automatically bijective.
    have h : Function.Bijective (fun n : Fin q => (n : F)) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fin_to_finfield_injective hq_card q_prime, hcard⟩
    exact h.surjective t

/- Every element of F can be written as (n : F) for some n < q because Fintype.card F = q and
the natural cast n ↦ (n : F) has period equal to ringChar F = q (since q is prime),
so {(0 : F), (1 : F), ..., (q-1 : F)} gives all q distinct elements.  -/
lemma exists_nat_cast_eq
  (hq_card : Fintype.card F = q)
  (q_prime : Prime q)
  (t : F)
  : ∃ (n : ℕ), n < q ∧ (n : F) = t := by
    obtain ⟨n, hn⟩ : ∃ n : Fin q, (n : F) = t := exists_fin_cast_eq hq_card q_prime t
    exact ⟨n.val, n.isLt, hn⟩


/-- A natural number `q` is the cardinality of some finite field if and only if it is a prime
power. Together with `Elligator.FiniteFieldBasic.card_isPrimePow` this says that the standing
hypotheses `Fintype.card F = q`, `q % 4 = 3` of this development describe exactly the setting of
[bernstein2013a], Section 3.1: an arbitrary prime power `q ≡ 3 (mod 4)`. -/
theorem exists_field_card_eq_iff_isPrimePow (q : ℕ) :
    (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = q) ↔ IsPrimePow q := by
  constructor
  · rintro ⟨F, _, _, hcard⟩
    exact card_isPrimePow hcard
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hp' : Nat.Prime p := Nat.prime_iff.mpr (by exact_mod_cast hp)
    haveI : Fact (Nat.Prime p) := ⟨hp'⟩
    have hk0 : k ≠ 0 := hk.ne'
    classical
    haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
    refine ⟨GaloisField p k, inferInstance, inferInstance, ?_⟩
    have := GaloisField.card p k hk0
    rw [Nat.card_eq_fintype_card] at this
    exact this

/-- If every element of `F` is the image of a natural number under the canonical cast, then the
cardinality of `F` is *prime*, not merely a *prime power*.

This is the precise reason why the string encoding `ι` of [bernstein2013a], Section 3.4, is
formalized for prime `q` only: it represents field elements by the naturals
`0, 1, ..., q - 1`, which requires the natural casts to exhaust `F`. The `ϕ` part of the
development makes no such assumption and therefore covers all *prime powers*. -/
lemma prime_of_natCast_surjective
  (hq_card : Fintype.card F = q)
  (hsurj : ∀ t : F, ∃ n : ℕ, (n : F) = t)
  : q.Prime := by
    have hpp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
    have hfin : Function.Surjective (fun n : Fin (ringChar F) => ((n : ℕ) : F)) := by
      intro t
      obtain ⟨n, hn⟩ := hsurj t
      exact ⟨⟨n % ringChar F, Nat.mod_lt _ hpp.pos⟩,
        by simpa [CharP.cast_eq_mod F (ringChar F) n] using hn⟩
    have hle : Fintype.card F ≤ ringChar F := by
      simpa using Fintype.card_le_of_surjective _ hfin
    have hge : ringChar F ≤ Fintype.card F := by
      have hinj : Function.Injective (fun n : Fin (ringChar F) => ((n : ℕ) : F)) := fun a b hab =>
        Fin.ext (CharP.natCast_injOn_Iio F (ringChar F) a.isLt b.isLt hab)
      simpa using Fintype.card_le_of_injective _ hinj
    have hq : q = ringChar F := by omega
    rw [hq]
    exact hpp

end Elligator.FiniteFieldBasic
