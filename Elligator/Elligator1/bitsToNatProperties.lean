/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Elligator.FiniteFieldBasic
public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.bProperties

@[expose] public section

/-!
# bitsToNat Properties

In this file we introduce some generally helpful lemmas for `bitsToNat `.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/


namespace Elligator.Elligator1

section bitsToNatProperties

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

lemma bitsToNat_le_full_range {n : ℕ} (τ : Fin n → Bool) : bitsToNat τ ≤ ∑ i ∈ Finset.range n, 2^i := by
  rw [ Finset.sum_range ];
  exact Finset.sum_le_sum fun i _ => by aesop;

/-- Every bit-vector of length `n` has binary value less than `2^n`. -/
lemma bitsToNat_lt_two_pow_n {n : ℕ} (τ : Fin n → Bool) : bitsToNat τ < 2 ^ n := by
  let h1 := bitsToNat_le_full_range τ
  exact lt_of_le_of_lt h1 (Nat.geomSum_lt (by norm_num) (by norm_num))

lemma bitsToNat_le_q_sub_one_over_two (τ : (@S q)) : bitsToNat τ.1 ≤ (q - 1) / 2 := by
    exact Finset.mem_filter.mp τ.2 |>.2

/-- `bitsToNat` is injective: distinct bit-vectors give distinct natural numbers. -/
lemma bitsToNat_injective {n : ℕ} : Function.Injective (bitsToNat : (Fin n → Bool) → ℕ) := by
  induction' n with n ih;
  · decide
  · intro τ τ' h1;
    have h_bitsToNat_succ : ∀ (τ : Fin (n + 1) → Bool), bitsToNat τ = 2 * bitsToNat (fun i => τ (Fin.succ i)) + if τ 0 then 1 else 0 := by
      intro τ; unfold bitsToNat; simp +decide [ Fin.sum_univ_succ, pow_succ' ] ; ring;
      rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; aesop;
    have h_bitsToNat_succ_eq : bitsToNat (fun i => τ (Fin.succ i)) = bitsToNat (fun i => τ' (Fin.succ i)) := by
      grind +ring;
    ext i; induction i using Fin.inductionOn <;> simp_all +singlePass ;
    · grind +ring;
    · exact ih h_bitsToNat_succ_eq |> fun h => by simpa using congr_fun h _;

/-- Every natural number less than `2^n` is the binary value of some bit-vector. -/
-- TODO use Function.surjective possible, i.e. have to get hm into ∀ m value somehow
lemma bitsToNat_surj (n : ℕ) (m : ℕ) (hm : m < 2^n) :
  ∃ τ : Fin n → Bool, bitsToNat τ = m := by
    induction' n with n ih generalizing m <;> simp_all +decide [ pow_succ' ];
    rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩;
    · obtain ⟨ τ, hτ ⟩ := ih k ( by linarith );
      use Fin.cons false τ;
      simp +decide [ ← hτ, Fin.sum_univ_succ, bitsToNat ] ; ring_nf;
      rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; aesop;
    · obtain ⟨ τ, hτ ⟩ := ih k ( by linarith ) ; use Fin.cons true τ; simp +decide [ *, bitsToNat ] ; ring;
      simp +decide [ ← hτ, Fin.sum_univ_succ ] ; ring_nf;
      simp +decide [ bitsToNat, Finset.sum_mul _ _ _ ]

lemma natCast_injective_of_prime_card
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (a b : ℕ) (ha : a < q) (hb : b < q) (h : (a : F) = (b : F))
  : a = b := by
    let h1 := FiniteFieldBasic.ringChar_of_F_eq_q field_cardinality q_prime
    have h2 := ringChar.spec F;
    have h3 := h2 ( a - b |> Int.natAbs )
    simp_all
    cases abs_cases ( a - b : ℤ ) <;> simp_all
    · exact le_antisymm ( le_of_not_gt fun h => by have := Nat.le_of_dvd ( by omega ) h3; omega ) ‹_›;
    · exact absurd h3 ( Nat.not_dvd_of_pos_of_lt ( by omega ) ( by omega ) )

lemma lower_half_neg_eq
  (field_cardinality : Fintype.card F = q) (hq : Prime q)
  {a b : ℕ} (ha : a ≤ (q - 1) / 2) (hb : b ≤ (q - 1) / 2)
  (heq : (a : F) = -(b : F))
  : a = b := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a + b = k * q := by
      have h_div : q ∣ (a + b : ℕ) := by
        have h_char : ringChar F = q :=
          FiniteFieldBasic.ringChar_of_F_eq_q field_cardinality hq
        rw [← h_char, ← CharP.cast_eq_zero_iff F]; aesop
      exact exists_eq_mul_left_of_dvd h_div
    rcases k with (_ | _ | k) <;> norm_num at hk <;>
      nlinarith [Nat.div_mul_le_self (q - 1) 2, Nat.sub_add_cancel hq.nat_prime.pos]

lemma σ_injective
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Function.Injective (@σ F _ q) := by
    intro a b h_eq
    apply bitsToNat_injective
    have h1 : bitsToNat a < q :=
      lt_of_lt_of_le (bitsToNat_lt_two_pow_n a) (two_pow_b_le_q q_mod_4_congruent_3)
    have h2 : bitsToNat b < q :=
      lt_of_lt_of_le (bitsToNat_lt_two_pow_n b) (two_pow_b_le_q q_mod_4_congruent_3)
    exact natCast_injective_of_prime_card q field_cardinality q_prime _ _ h1 h2 h_eq

/-
PROBLEM
If `n < q` and `n ≤ (q-1)/2`, there exists a bit-vector `τ ∈ S` with
`bitsToNat τ = n`.
-/
lemma exists_S_elem_of_le
  (q_mod_4_congruent_3 : q % 4 = 3)
  (n : ℕ) (hn : n < q) (hle : n ≤ (q - 1) / 2)
  : ∃ (τ : (@S q)), bitsToNat τ.1 = n := by
  -- By `bitsToNat_surj`, there exists a bit-vector `τ` such that `bitsToNat τ = n`.
  have h_surj : ∃ τ : Fin (@b q) → Bool, bitsToNat τ = n := by
    apply bitsToNat_surj;
    have h_log : q ≤ 2 ^ (Nat.log 2 q) * 2 := by
      rw [ ← pow_succ ] ; exact Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ );
    unfold b; omega;
  unfold S; aesop;

/-
For any `t ∈ F_q` (with `q` prime, `q ≡ 3 mod 4`), there exists `τ ∈ S` such
that `σ(τ) = t` or `σ(τ) = -t`. This is the key encoding lemma: at least one of
`{t, -t}` lies in the image of `σ` restricted to `S`.
-/
lemma exists_σ_preimage_or_neg
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : F)
  : ∃ (τ : (@S q)), (@σ F _ q τ.1) = t ∨ (@σ F _ q τ.1) = -t := by
  obtain ⟨ n, hn, rfl ⟩ := FiniteFieldBasic.exists_nat_cast_eq field_cardinality q_prime t;
  by_cases h : n ≤ ( q - 1 ) / 2;
  · obtain ⟨ τ, hτ ⟩ := exists_S_elem_of_le q_mod_4_congruent_3 n hn h;
    unfold σ; aesop;
  · -- Since $q - n \leq (q - 1) / 2$, we can find a $\tau \in S$ such that $\sigma(\tau) = q - n$.
    obtain ⟨τ, hτ⟩ : ∃ τ : @S q, bitsToNat τ.1 = q - n := by
      apply exists_S_elem_of_le q_mod_4_congruent_3 (q - n) (by
      omega) (by
      omega);
    use τ; simp_all +decide [ σ ] ;
    rw [ Nat.cast_sub hn.le ] ; aesop
