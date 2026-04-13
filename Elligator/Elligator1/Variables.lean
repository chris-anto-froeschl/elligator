/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Mathlib
public import Elligator.FiniteFieldBasic
public import Elligator.LegendreSymbol

@[expose] public section

/-!
# Elligator 1 Variables

In this file we introduce all the independent variables introduced in the definition of
Elligator 1.

## Main results

- TODO

## References

See [bernstein2013a] chapter 3.
-/

namespace Elligator.Elligator1

section Variables

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

/-- c(s) is a function defined in the paper.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def c (s : F) : F := 2 / s^2

/-- r(s) is a function defined in the paper.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def r (s : F) : F :=
  let c := c s;
  c + 1 / c

/-- d(s) is a function defined in the paper.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def d (s : F) : F :=
  let c := c s;
  -(c + 1)^2 / (c - 1)^2

/-- u(t) is a function defined in the paper.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def u (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : F :=
  let t := t.val;
  (1 - t) / (1 + t)

/-- v(t, s) is a function defined in the paper.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def v (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
  let u := u t
  let r := r s
  u^5 + (r^2 - 2) * u^3 + u

/-- X(t, s) is a function defined in the paper.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def X
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let u_of_t := u t
  let v_of_t := v t s
  let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_v_of_t * u_of_t

/-- Y(t, s) is a function defined in the paper.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def Y
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let u_of_t := u t
  let c_of_s := c s
  let v_of_t := v t s
  let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_sum := LegendreSymbol.χ ((u_of_t)^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3
  (χ_of_v_of_t * v_of_t)^((q + 1) / 4) * χ_of_v_of_t * χ_of_sum

/-- x(t, s) is a function defined in the paper. It is the x-coordinate of the point on the curve.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def x
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let c_of_s := c s
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (c_of_s - 1) * s * X_of_t * (1 + X_of_t) / Y_of_t

/-- y(t, s) is a function defined in the paper. It is the y-coordinate of the point on the curve.

Original: Chapter "3.2 The map": Theorem 1
-/
noncomputable def y
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let r_of_s := r s
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (r_of_s * X_of_t - (1 + X_of_t)^2) / (r_of_s * X_of_t + (1 + X_of_t)^2)

/-- η(s, q, point) is a function defined in the paper.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
noncomputable def η
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : F :=
  let y := point.snd
  (y - 1) / (2 * (y + 1))

/-- X2 is a function defined in the paper.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
noncomputable def X2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  -- TODO decide if defs should already require everything to guarantee well definedness
  -- PRO: always well defined; CON: hard calling convention, not as general
  --(point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  --(h : point.val ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
  : F :=
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r_of_s := r s
  (-(1 + η_of_point * r_of_s) + ((1 + η_of_point * r_of_s)^2 - 1)^((q + 1) / 4))

/-- z is a function defined in the paper.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
noncomputable def z
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : F
  :=
  let x := point.fst
  let c_of_s := c s
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let a := (c_of_s - 1) * s * X2_of_point * (1 + X2_of_point) * x * (X2_of_point^2 + 1 / c_of_s^2)
  LegendreSymbol.χ a q field_cardinality q_prime_power q_mod_4_congruent_3

/-- u2 is a function defined in the paper.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
noncomputable def u2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : F
  :=
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  z_of_point * X2_of_point

/-- t2 is a function defined in the paper.

Original: Chapter "3.3 Inverting the map": Theorem 3
-/
noncomputable def t2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : F
  :=
  let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  (1 - u2_of_point) / (1 + u2_of_point)

/-- `b q` is `⌊log₂ q⌋`, the number of bits needed.

Original: Chapter "3.4 Encoding as strings": Theorem 4
-/
noncomputable def b : ℕ := Nat.log 2 q

/-- Convert a bit vector (τ₀, τ₁, ..., τ_{b-1}) to a natural number via binary
expansion: bitsToNat(τ) = Σᵢ τᵢ · 2^i.
-/
def bitsToNat {n : ℕ} (τ : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if τ i then 2^(i : ℕ) else 0

/-- `σ` interprets a bit vector `(τ₀, τ₁, …, τ_{b−1})` as the field element
`∑ᵢ τᵢ · 2ⁱ ∈ Fq`. This is the standard binary-to-integer conversion followed by casting into `F`.

Original: Chapter "3.4 Encoding as strings": Theorem 4
-/
noncomputable def σ (τ : Fin (@b q) → Bool) : F := (bitsToNat τ : F)

/-- S = σ⁻¹({0, 1, 2, ..., (q-1)/2}), the set of bit vectors whose binary value
falls in the lower half {0, 1, ..., (q-1)/2} of F_q.

Original: Chapter "3.4 Encoding as strings": Theorem 4
-/
noncomputable def S : Finset (Fin (@b q) → Bool) :=
  Finset.univ.filter (fun τ => (bitsToNat τ) ≤ (q - 1) / 2)
