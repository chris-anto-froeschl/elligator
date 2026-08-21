/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Reconstruction Coordinates

TODO

## Main Results

* TODO

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.ReconstructionCoordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates

section η

/-- η(s, q, point) is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:η"
  (title := "The inversion quantity $\\eta$")
  (statement := /--
  For a point $(x, y)$ of $E(\mathbb{F}_q)$ with $y + 1 \neq 0$, define
  $$
  \eta = \frac{y - 1}{2(y + 1)} .
  $$
  -/)]
def η (P : F × F) : F :=
    let y := P.snd
    (y - 1) / (2 * (y + 1))

----------------------------------------- TODO MOVE to better intermediate place (was MapProperties)

-- Used in Theorem 3 Proof B part as implication for P_in_ϕOverF_with_prop2_main_case
-- argument.
lemma y_h1 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let y := y t s
    let r := r s
    let X := X t s
    X ^ 2 + (2 + r * (y - 1) / (y + 1)) * X + 1 = 0 := by
  intro y r X
  rw [← mul_left_inj' (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
  change (X ^ 2 + (2 + r * (y - 1) / (y + 1)) * X + 1) * (y + 1) = 0 * (y + 1)
  repeat rw [add_mul]
  rw [zero_mul]
  have h1 : (2 * X * (y + 1) + r * (y - 1) / (y + 1) * X * (y + 1))
      = (2 * (y + 1) + r * (y - 1)) * X := by
    rw [add_mul _ _ X, ← div_left_inj' (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
    change (2 * X * (y + 1) + r * (y - 1) / (y + 1) * X * (y + 1)) / (y + 1)
      = (2 * (y + 1) * X + r * (y - 1) * X) / (y + 1)
    repeat rw [add_div, mul_div_assoc, div_self (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
    rw [mul_comm (2 * (y + 1)) X, ← mul_assoc]
    nth_rw 2 [mul_div_assoc]
    rw [div_self (y_add_one_ne_zero hs_ne_zero hq_card hq_mod t)]
    ring
  have h2 : (2 * (y + 1) + r * (y - 1)) = (y * r - r + 2 * y + 2) := by ring_nf
  rw [h1, h2, mul_add, add_mul]
  ring_nf
  rw [← add_right_inj (r * X - 1 - 2 * X - X ^ 2)]
  ring_nf
  rw [mul_comm (X ^ 2) y, mul_comm X y, mul_assoc, mul_assoc]
  nth_rw 4 [← mul_one y]
  rw [add_assoc, ← mul_add y]
  rw [add_assoc, ← mul_add y, add_comm (X ^ 2) 1, ← add_assoc, add_comm (X * 2) 1]
  rw [mul_comm X 2]
  have h3 : 1 + 2 * X + X ^ 2 = (1 + X) ^ 2 := by ring_nf
  have h4 : -1 + r * X - 2 * X - X ^ 2 = r * X - (1 + 2 * X + X ^ 2) := by ring_nf
  rw [h4, h3]
  rw [← mul_assoc, mul_comm, ← mul_add]
  rw [← div_left_inj' (y_divisor_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t)]
  change (y * (r * X + (1 + X) ^ 2)) / (r * X + (1 + X) ^ 2) = y
  rw [mul_div_assoc]
  rw [div_self (y_divisor_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t), mul_one]

-- Implicated by y_h1. Saved for further proof arguments in Theorem 3 Proof B
lemma y_h2 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let r := r s
    let X := X t s
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let η := η P
    X ^ 2 + 2 * (1 + η * r) * X + 1 = 0 := by
  intro r X P η
  let y := y t s
  calc
    X ^ 2 + 2 * (1 + η * r) * X + 1
    = X ^ 2 + 2 * (1 + 1 / 2 * ((y - 1) / (y + 1)) * r) * X + 1 := by
      -- Unfold until reaching the y which is equivalent to y for comparison
      unfold η ReconstructionCoordinates.η P ϕ
      simp only [Subtype.coe_eta, dite_eq_ite, one_div]
      rw [ite_eq_left t.prop]
      change X ^ 2 + 2 * (1 + (y - 1) / (2 * (y + 1)) * r) * X + 1
        = X ^ 2 + 2 * (1 + 2⁻¹ * ((y - 1) / (y + 1)) * r) * X + 1
      rw [inv_eq_one_div, ← mul_div_mul_comm]
      ring
    _ = X ^ 2 + (2 + r * (y - 1) / (y + 1)) * X + 1 := by
      rw [mul_add 2]
      rw [div_eq_mul_inv 1 2, mul_one, one_mul, mul_assoc, ← mul_assoc]
      rw [mul_inv_cancel₀ (two_ne_zero hq_card hq_mod)]
      ring
    _ = 0 := by rw [y_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod]

-- Implicated by y_h2.
lemma y_h3 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let r := r s
    let X := X t s
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let η := η P
    X + 1 / X = -2 * (1 + η * r) := by
  intro r X P η
  rw [← add_right_inj (2 * (1 + η * r))]
  rw [← mul_left_inj' (X_ne_zero hs_ne_zero hq_card hq_mod t)]
  change (2 * (1 + η * r) + (X + 1 / X)) * X = (2 * (1 + η * r) + -2 * (1 + η * r)) * X
  have h1 : (2 * (1 + η * r) + -2 * (1 + η * r)) * X = 0 := by ring_nf
  rw [h1, ← y_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  change (2 * (1 + η * r) + (X + 1 / X)) * X = X ^ 2 + 2 * (1 + η * r) * X + 1
  ring_nf
  rw [mul_inv_cancel₀ (X_ne_zero hs_ne_zero hq_card hq_mod t)]
  ring_nf

lemma X_comparison_implication (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Xbar := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let η := η P
    let r := r s
    X1 + Xbar = -2 * (1 + η * r) := by
  intro t1 t2 X1 Xbar P η r
  unfold Xbar
  rw [X_comparison t]
  exact (y_h3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod)

lemma X_comparison_implication2 (t : { t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Xbar := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    Xbar * X1 = 1 := by
  intro t1 t2 X1 Xbar
  unfold Xbar
  rw [X_comparison t]
  rw [← inv_eq_one_div, inv_mul_cancel₀ (X_ne_zero hs_ne_zero hq_card hq_mod t)]

lemma χ_IsSquare_h1 (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let v := v t s
    IsSquare (((χ v) * v) ^ ((q + 1) / 4)) := by
  intro v
  have hv_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
  have hχ_a_mul_a_IsSquare := χ_a_mul_a_IsSquare hv_ne_zero hq_card hq_mod
  unfold IsSquare at hχ_a_mul_a_IsSquare
  rcases hχ_a_mul_a_IsSquare with ⟨r, hr⟩
  rw [hr, ← pow_two, ← pow_mul, mul_comm, pow_mul]
  apply IsSquare.sq

lemma y_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let y1 := y t s
    let y2 := y ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    y2 = y1 := by
  intro t1 t2 y1 y2
  let c := c s
  let r := r s
  let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let X1 := X t s
  let Xbar := X ⟨t2, t_h⟩ s
  calc
    y2 = (r * Xbar - (1 + Xbar) ^ 2) / (r * Xbar + (1 + Xbar) ^ 2) := by rfl
    _ = (r * (1 / X1) - (1 + (1 / X1)) ^ 2) / (r * (1 / X1) + (1 + (1 / X1)) ^ 2) := by
      unfold Xbar
      rw [X_comparison t]
    _ = (r * X1 - (X1 + 1) ^ 2) / (r * X1 + (X1 + 1) ^ 2) := by grind
    _ = y1 := by
      rw [add_comm]
      rfl

lemma P_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    have t_h : (t2 ≠ 1 ∧ t2 ≠ -1) := neg_t_ne_one_and_neg_t_ne_neg_one t
    let y1 := y t s
    let y2 := y ⟨t2, t_h⟩ s
    let x1 := x t s q
    let x2 := x ⟨t2, t_h⟩ s q
    (x1, y1) = (x2, y2) := by
  intro t1 t2 t_h y1 y2 x1 x2
  unfold x2 y2
  rw [x_comparison t hs_ne_zero hq_card hq_mod]
  rw [y_comparison]

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h1 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hηr :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let r := r s
      let η := η P
      η * r = -2) :
    let X := X t s
    (X - 1) ^ 2 = 0 := by
  intro X
  let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
  let r := r s
  let η := η P.val
  have h : X + 1 / X = -2 * (1 + η * r) := y_h3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  rw [hηr] at h
  ring_nf at h
  rw [← mul_left_inj' (X_ne_zero hs_ne_zero hq_card hq_mod t), add_mul] at h
  change X * X + X⁻¹ * X = 2 * X at h
  rw [← add_left_inj (2 * X)]
  ring_nf
  rw [inv_mul_cancel₀ (X_ne_zero hs_ne_zero hq_card hq_mod t)] at h
  rw [pow_two, add_comm]
  nth_rw 2 [mul_comm]
  exact h

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h2 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hηr :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let r := r s
      let η := η P.val
      η * r = -2) :
    let X := X t s
    X = 1 := by
  intro X
  have hXpow : (X - 1) ^ 2 = 0 := X_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod hηr
  grind

-- Used in the main case of Theorem 3 Proof part B
lemma u_η_h1 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hηr :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let r := r s
      let η := η P
      η * r = -2) :
    let u := u t;
    u = 1 := by
  intro u
  let X := X t s
  let v := v t s
  let χ_of_v := χ v
  have v_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
  have h1 : X = χ_of_v * u := by rfl
  unfold X at h1
  rw [X_η_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod hηr] at h1
  rcases χ_values (a := v)
  · rename_i h2
    change χ_of_v = 0 at h2
    have h3 := a_eq_zero_of_χ_of_a_eq_zero (a := v)
    have h4 : v = 0 := by apply h3 h2
    contradiction
  · rename_i h2
    rcases h2
    · rename_i h2
      change χ_of_v = -1 at h2
      rw [h2] at h1
      unfold u AuxiliaryCoordinates.u at h1
      have two_ne_zero := two_ne_zero hq_card hq_mod
      have h3 : (2 : F) = 0 := by grind
      contradiction
    · rename_i h2
      exact (eq_one_iff_eq_one_of_mul_eq_one (id (Eq.symm h1))).mp h2

-- Used in the main case of Theorem 3 Proof part B
lemma t_η_h1 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hηr :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let r := r s
      let η := η P
      η * r = -2) :
  t.val = 0 := by
  let u := u t
  have h1 : u = 1 := u_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod hηr
  unfold u AuxiliaryCoordinates.u at h1
  have h4_1 : 1 + t.val ≠ 0 := one_add_t_ne_zero t
  rw [← mul_right_inj' h4_1, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self h4_1] at h1
  rw [← add_left_inj (t.val - 1)] at h1
  ring_nf at h1
  symm at h1
  rw [← div_left_inj' (two_ne_zero hq_card hq_mod)] at h1
  ring_nf at h1
  rw [mul_assoc, inv_mul_cancel₀ (two_ne_zero hq_card hq_mod), mul_one] at h1
  exact h1

-- Used in the main case of Theorem 3 Proof part B
lemma v_η_h1 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hηr :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let r := r s
      let η := η P
      η * r = -2) :
    let v := v t s
    let r := r s
    v = r ^ 2 := by
  intro v r
  unfold v AuxiliaryCoordinates.v
  rw [u_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod hηr]
  ring

-- Used in the main case of Theorem 3 Proof part B
lemma Y_η_h1 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hηr :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let r := r s
      let η := η P
      η * r = -2) :
    let Y := Y t s q
    let c := c s
    let r := r s
    Y = r * (χ c) := by
  intro Y c r
  have c_ne_zero := c_ne_zero hs_ne_zero hq_card hq_mod
  calc
    Y = (r ^ 2) ^ ((q + 1) / 4) * χ (1 + 1 / c ^ 2) := by
      unfold Y AuxiliaryCoordinates.Y
      rw [v_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod hηr]
      rw [u_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod hηr]
      change (χ (r ^ 2) * r ^ 2) ^ ((q + 1) / 4) * χ (r ^ 2) * (χ (1 ^ 2 + 1 / c ^ 2))
        = (r ^ 2) ^ ((q + 1) / 4) * χ (1 + 1 / c ^ 2)
      have h1 : r ^ 2 ≠ 0 := pow_ne_zero 2 (r_ne_zero hs_ne_zero hq_card hq_mod)
      have h2 : IsSquare (r ^ 2) := IsSquare.sq r
      rw [χ_a_eq_one h1 h2]
      nth_rw 2 [pow_two]
      rw [mul_one, one_mul, mul_one]
    _ = (χ r) * r * χ (r / c) := by
      have h : 1 + 1 / c ^ 2 = (c + 1 / c) / c := by grind
      rw [h]
      change (r ^ 2) ^ ((q + 1) / 4) * χ (r / c) = (χ r) * r * χ (r / c)
      rw [b_pow_q_add_one_div_four_eq_χ_of_a_mul_a hq_card hq_mod]
    _ = r * (χ c) := by
      have r_ne_zero := r_ne_zero hs_ne_zero hq_card hq_mod
      let χ_of_one_div_c := χ (1 / c)
      calc
        (χ r) * r * χ (r / c) = r * (χ r) * (χ r) * χ_of_one_div_c := by
          grind [χ_mul]
        _ = r * 1 * χ_of_one_div_c := by
          rw [mul_assoc r, ← χ_mul]
          rw [← pow_two, χ_sq r_ne_zero]
        _ = r * (χ c) := by
          unfold χ_of_one_div_c
          rw [← χ_inv, mul_one]

-- Implicated by main case of Theorem 3 proof part B.
lemma y_η_h1 (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hηr :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let r := r s
      let η := η P
      η * r = -2) :
    let r := r s
    let y := y t s
    y = (r - 4) / (r + 4) := by
  intro r y
  unfold y OutputCoordinates.y
  let X := X t s
  change (r * X - (1 + X) ^ 2) / (r * X + (1 + X) ^ 2) = (r - 4) / (r + 4)
  unfold X
  rw [X_η_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod hηr]
  ring

lemma y_of_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let y := y ⟨(0 : F), by simp⟩ s
    let r := r s
    y = (r - 4) / (r + 4) := by
  intro y r
  unfold y OutputCoordinates.y
  rw [X_of_zero hs_ne_zero hq_card hq_mod]
  change (r * 1 - (1 + 1) ^ 2) / (r * 1 + (1 + 1) ^ 2) = (r - 4) / (r + 4)
  ring

lemma ϕ_of_t_eq_zero_one (t : { n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    ϕ.val = (0, 1) := by
  intro ϕ
  unfold ϕ Elligator1.ϕ
  rcases t.prop with h | h <;> simp [h]

-----------------------------------------

lemma η_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    (η P) = 0 := by
  intro P
  unfold η
  let y := P.2
  change (y - 1) / (2 * (y + 1)) = 0
  unfold y P
  rw [ϕ_of_t_eq_zero_one t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  rw [sub_self, zero_div]

end η

---------------------------------------------
lemma y_add_one_eq_two (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let y := P.2
    y + 1 = 2 := by
  intro P y
  unfold y P
  rw [ϕ_of_t_eq_zero_one t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  ring_nf

/-- `ϕOverFProp1` is the first property fulfilled by Ps in `EOverF`.
This property does not have to consider a dedicated field `F` with `q`.
This restriction is defined during the context evolution.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp1"
  (title := "Image condition 1: $y + 1 \\neq 0$")
  (statement := /--
  The first of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies
  $$
  y + 1 \neq 0 .
  $$
  -/)]
def ϕOverFProp1 (P : F × F) : Prop :=
    let y := P.snd
    y + 1 ≠ 0

/-- `ϕOverFProp2` is the second property fulfilled by Ps in `EOverF`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp2"
  (title := "Image condition 2: $(1 + \\eta r) ^ 2 - 1$ is a square")
  (statement := /--
  The second of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies that
  $$
  (1 + \eta r) ^ 2 - 1
  $$
  is a square, where $\eta = (y - 1)/(2(y + 1))$.
  -/)]
def ϕOverFProp2 (s : F) (P : F × F) : Prop :=
    let r := r s
    let η := η P
    IsSquare ((1 + η * r) ^ 2 - 1)

/-- `ϕOverFProp3` is the third property fulfilled by Ps in `EOverF`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProp3"
  (title := "Image condition 3: the exceptional case $\\eta r = -2$")
  (statement := /--
  The third of the three conditions characterizing $\varphi(\mathbb{F}_q)$ inside
  $E(\mathbb{F}_q)$ in Theorem 3: a point $(x, y)$ satisfies that if $\eta r = -2$ then
  $$
  x = 2s(c - 1)\chi(c)/r .
  $$
  -/)]
def ϕOverFProp3 (s : F) (P : F × F) : Prop :=
    let x := P.fst
    let c := c s
    let r := r s
    let η := η P
    η * r = -2 → x = 2 * s * (c - 1) * (χ c) / r

/-- `ϕOverFProps` combines the previously defined properties which are fulfilled by Ps
in `EOverF`, i.e. `ϕOverFProp1`, `ϕOverFProp2` and `ϕOverFProp3`.

Original: Section "3.3 Inverting the map", Theorem 3
-/
@[blueprint "def:ϕOverFProps"
  (title := "The image conditions of Theorem 3")
  (statement := /--
  The conjunction of the three conditions of Theorem 3 for a point $(x, y) \in E(\mathbb{F}_q)$:
  $y + 1 \neq 0$; $(1 + \eta r) ^ 2 - 1$ is a square, where $\eta = (y - 1)/(2(y + 1))$; and if
  $\eta r = -2$ then $x = 2s(c - 1)\chi(c)/r$.
  -/)]
def ϕOverFProps (s : F) (P : F × F) : Prop := ϕOverFProp1 P ∧ ϕOverFProp2 s P ∧ ϕOverFProp3 s P

/-- `ϕOverF` is the set of Ps produced by `ϕ`.

Original: Section "3.2 The map", Definition 2
-/
@[blueprint "def:ϕOverF"
  (title := "The image $\\varphi(\\mathbb{F}_q)$")
  (statement := /--
  The image of the decoding function of Definition 2,
  $$
  \varphi(\mathbb{F}_q) = \{\varphi(t) : t \in \mathbb{F}_q\} \subseteq E(\mathbb{F}_q) .
  $$
  -/)]
def ϕOverF (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) : Set (F × F) :=
    Set.range (fun t : F => ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod)

lemma P_in_ϕOverF_with_prop1_base_case (t : {n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕOverFProp1 P := by
  intro P
  unfold ϕOverFProp1
  intro y
  unfold y P ϕ
  let two_ne_zero := two_ne_zero hq_card hq_mod
  simp only [not_t_ne_one_and_t_ne_neg_one]
  norm_num
  exact two_ne_zero

lemma P_in_ϕOverF_with_prop1_main_case (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    ϕOverFProp1 P := by
  intro P
  unfold ϕOverFProp1
  intro y
  unfold y P ϕ
  dsimp
  rw [dite_eq_left t.prop]
  exact y_add_one_ne_zero hs_ne_zero hq_card hq_mod t

-- Original: Theorem 3.2 Proof B prop 1 argumentation
lemma P_in_ϕOverF_with_prop1 (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    ϕOverFProp1 P := by
  intro P
  unfold ϕOverFProp1
  intro y
  by_cases h1 : t ≠ 1 ∧ t ≠ -1
  · exact P_in_ϕOverF_with_prop1_main_case ⟨t, h1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · have h1_1 : (t = 1 ∨ t = -1) := by
      rw [ne_eq, ne_eq, ← not_or, not_not] at h1
      exact h1
    exact P_in_ϕOverF_with_prop1_base_case ⟨t, h1_1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod

lemma P_in_ϕOverF_with_prop2_base_case (t : {n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    ϕOverFProp2 s P := by
  intro P
  unfold ϕOverFProp2
  intro r η
  unfold η ReconstructionCoordinates.η P ϕ
  simp_all [not_t_ne_one_and_t_ne_neg_one]

lemma P_in_ϕOverF_with_prop2_main_case (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    ϕOverFProp2 s P := by
  intro P
  unfold ϕOverFProp2
  let r := r s
  let X := X t s
  let y := y t s
  let c := c s
  let η := η P
  have h1 : X ^ 2 + 2 * (1 + η * r) * X + 1 = 0 := y_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  have h2 : NeZero (2 : F) := by
    rw [neZero_iff]
    exact two_ne_zero hq_card hq_mod
  rw [pow_two] at h1
  nth_rw 1 [← one_mul X, mul_assoc] at h1
  change IsSquare ((1 + η * r) ^ 2 - 1)
  rw [@quadratic_eq_zero_iff_discrim_eq_sq
    F _ 1 (2 * (1 + η * r)) 1 h2 _ (one_ne_zero' F) X] at h1
  unfold discrim at h1
  rw [mul_pow 2 _ 2] at h1
  have h3 : 2 ^ 2 = (4 : F) := by norm_num
  rw [mul_one, h3, ← mul_sub, mul_comm] at h1
  rw [← div_left_inj' (four_ne_zero hq_card hq_mod)] at h1
  rw [mul_div_assoc, div_self (four_ne_zero hq_card hq_mod)] at h1
  rw [mul_one, ← h3, ← div_pow _ _ 2] at h1
  rw [h1]
  apply IsSquare.sq

-- Original: Theorem 3.2 Proof B prop 2 argumentation
lemma P_in_ϕOverF_with_prop2 (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    ϕOverFProp2 s P := by
  intro P
  unfold ϕOverFProp2
  intro y
  by_cases h1 : t ≠ 1 ∧ t ≠ -1
  · exact P_in_ϕOverF_with_prop2_main_case ⟨t, h1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · have h1_1 : (t = 1 ∨ t = -1) := by
      rw [ne_eq, ne_eq] at h1
      rw [← not_or, not_not] at h1
      exact h1
    exact P_in_ϕOverF_with_prop2_base_case ⟨t, h1_1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod

lemma P_in_ϕOverF_with_prop3_base_case (t : {n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    ϕOverFProp3 s P := by
  intro P
  unfold ϕOverFProp3
  intro x c r η h
  have h' : ¬(t.val ≠ 1 ∧ t.val ≠ -1) := by simp [not_t_ne_one_and_t_ne_neg_one]
  simp only [η, ReconstructionCoordinates.η, P, ϕ, ne_eq] at h
  rw [dite_eq_right h'] at h
  ring_nf at h
  have htwo_ne_zero := two_ne_zero hq_card hq_mod
  simp at h
  contradiction

lemma P_in_ϕOverF_with_prop3_main_case (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    ϕOverFProp3 s P := by
  intro P
  unfold ϕOverFProp3
  intro x c r η h1
  let X := X t s
  let Y := Y t s q
  simp only [x, P, ϕ]
  rw [dite_eq_left t.prop]
  unfold OutputCoordinates.x
  change (c - 1) * s * X * (1 + X) / Y = 2 * s * (c - 1) * (χ c) / r
  unfold X Y
  rw [X_η_h2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod h1]
  rw [Y_η_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod h1]
  nth_rw 2 [mul_div_assoc, one_div_χ_of_a_eq_χ_a]
  grind

-- Original: Theorem 3.2 Proof B prop 3 argumentation
lemma P_in_ϕOverF_with_prop3 (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    ϕOverFProp3 s P := by
  intro P
  unfold ϕOverFProp3
  intro y
  by_cases t_h : t ≠ 1 ∧ t ≠ -1
  · exact P_in_ϕOverF_with_prop3_main_case ⟨t, t_h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · have h1_1 : (t = 1 ∨ t = -1) := by
      rw [ne_eq, ne_eq, ← not_or, not_not] at t_h
      exact t_h
    exact P_in_ϕOverF_with_prop3_base_case ⟨t, h1_1⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod

-- Original: Theorem 3.2 Proof B (3.2 forward statement)
@[blueprint "thm:P_props_of_P_in_ϕOverF"
  (title := "Points of $\\varphi(\\mathbb{F}_q)$ satisfy the image conditions")
  (statement := /--
  The forward part of statement 2 of Theorem 3: every $(x, y) \in \varphi(\mathbb{F}_q)$
  satisfies $y + 1 \neq 0$; $(1 + \eta r) ^ 2 - 1$ is a square, where
  $\eta = (y - 1)/(2(y + 1))$; and if $\eta r = -2$ then $x = 2s(c - 1)\chi(c)/r$.
  -/)]
theorem P_props_of_P_in_ϕOverF (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    P ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod → ϕOverFProps s P := by
  intro P h1
  unfold ϕOverFProps
  split_ands
  · exact P_in_ϕOverF_with_prop1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · exact P_in_ϕOverF_with_prop2 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · exact P_in_ϕOverF_with_prop3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod

lemma P_of_ϕ_in_ϕOverF (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    let ϕOverF := ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod
    P ∈ ϕOverF := by
  simp [ϕOverF]

lemma P_of_ϕ_fulfills_ϕOverFProps (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    ϕOverFProps s P := by
  intro P
  let h := P_of_ϕ_in_ϕOverF t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  exact P_props_of_P_in_ϕOverF t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod h

---------------------------------------------

section Xbar

/-- Xbar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:Xbar"
  (title := "The reconstructed coordinate $\\bar X$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\eta$ as above, define
  $$
  \bar X = -(1 + \eta r) + ((1 + \eta r) ^ 2 - 1)^{(q+1)/4} .
  $$
  -/)]
def Xbar (s : F) (P : F × F) (q : ℕ) : F :=
    let η := η P
    let r := r s
    (-(1 + η * r) + ((1 + η * r) ^ 2 - 1) ^ ((q + 1) / 4))

lemma Xbar_eq_neg_one
    (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let Xbar := Xbar s P.1 q
    Xbar = -1 := by
  intro P Xbar
  unfold Xbar ReconstructionCoordinates.Xbar
  let η := η P.1
  change -(1 + η * (r s)) + ((1 + η * (r s)) ^ 2 - 1) ^ ((q + 1) / 4) = -1
  unfold η
  rw [η_eq_zero t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  ring_nf
  rw [zero_pow, add_zero]
  omega

lemma Xbar_h1
  (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P}) :
    let η_of_P := η P.val
    let r := r s
    let Xbar := Xbar s P q
    (1 + η_of_P * r + Xbar) ^ 2 = (1 + η_of_P * r) ^ 2 - 1 := by
  intro η_of_P r Xbar
  unfold Xbar ReconstructionCoordinates.Xbar
  let a := ((1 + η_of_P * r) ^ 2 - 1) ^ ((q + 1) / 4)
  let a_sqr := (1 + η_of_P * r) ^ 2 - 1
  change (1 + η_of_P * r + (-(1 + η_of_P * r) + a)) ^ 2 = a_sqr
  ring_nf
  unfold a a_sqr
  nth_rw 2 [add_comm]
  rw [← pow_mul, one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
  unfold η_of_P
  nth_rw 2 [add_comm]
  rw [a_pow_q_add_one_div_two_eq_a P.prop.2.1 hq_card hq_mod]

lemma Xbar_h2 (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P}) :
    let η := η P.val
    let r := r s
    let Xbar := Xbar s P q
    Xbar ^ 2 + 2 * (1 + η * r) * Xbar + 1 = 0 := by
  intro η r Xbar
  have h := Xbar_h1 hq_card hq_mod P
  grind

lemma Xbar_h3
    (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let X' := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let X := X t s
    let Xbar := Xbar s P.val q
    (Xbar - X) * (Xbar - X') = 0 := by
  intro t1 t2 P X' X Xbar
  let η := η P.val
  let r := r s
  let P_of_ϕ_fulfills_ϕOverFProps :=
    P_of_ϕ_fulfills_ϕOverFProps t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  calc
    (Xbar - X) * (Xbar - X') = Xbar ^ 2 - (X + X') * Xbar + X * X' := by ring
    _ = Xbar ^ 2 + 2 * (1 + η * r) * Xbar + 1 := by
      rw [X_comparison_implication t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
      change Xbar ^ 2 - -2 * (1 + η * r) * Xbar + X * X' = Xbar ^ 2 + 2 * (1 + η * r) * Xbar + 1
      rw [mul_add, mul_comm X _]
      rw [X_comparison_implication2 t hs_ne_zero hq_card hq_mod]
      ring
    _ = 0 := Xbar_h2 hq_card hq_mod ⟨P.val, P_of_ϕ_fulfills_ϕOverFProps⟩

lemma Xbar_h4
    (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let X' := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let X := X t s
    let Xbar := Xbar s P q
    Xbar = X ∨ Xbar = X' := by
  intro t1 t2 P X' X Xbar
  have h := Xbar_h3 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  grind

lemma Xbar_ne_zero
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P}) :
    let Xbar := Xbar s P q
    Xbar ≠ 0 := by
  intro Xbar
  have h := Xbar_h2 hq_card hq_mod P
  let η := η P.val
  let r := r s
  change Xbar ^ 2 + 2 * (1 + η * r) * Xbar + 1 = 0 at h
  intro h'
  rw [h'] at h
  simp at h

lemma y_divisor_ne_zero_with_Xbar_for_X (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P}) :
    let r := r s
    let Xbar := Xbar s P q
    r * Xbar + (1 + Xbar) ^ 2 ≠ 0 := by
  intro r Xbar h1
  let η := η P.val
  have h2 := Xbar_h2 hq_card hq_mod P
  change Xbar ^ 2 + 2 * (1 + η * r) * Xbar + 1 = 0 at h2
  let y := P.val.2
  have h3 : 2 * η = 1 := by
    have hne : r * Xbar ≠ 0 :=
      mul_ne_zero (r_ne_zero hs_ne_zero hq_card hq_mod) (Xbar_ne_zero hq_card hq_mod P)
    rw [← div_left_inj' hne]
    grind
  have h4 : y - 1 = y + 1 := by
    unfold η ReconstructionCoordinates.η at h3
    grind
  have h5 : y - 1 ≠ y + 1 := by grind
  contradiction

lemma Xbar_ne_neg_one (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_eq_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P q
    Xbar ≠ -1 := by
  intro Xbar h1
  let η := η P.val
  let Xbar_equation := Xbar_h2 hq_card hq_mod P
  let r := r s
  let P_prop := P.prop
  let y := P.val.2
  change Xbar ^ 2 + 2 * (1 + η * r) * Xbar + 1 = 0 at Xbar_equation
  rw [h1] at Xbar_equation
  have h2 : η = 0 := by
    ring_nf at Xbar_equation
    let r_ne_zero := r_ne_zero hs_ne_zero hq_card hq_mod
    rw [← div_left_inj' (two_ne_zero hq_card hq_mod)] at Xbar_equation
    rw [← div_left_inj' r_ne_zero] at Xbar_equation
    ring_nf at Xbar_equation
    have h2_1 : -(η * r * 2⁻¹ * r⁻¹ * 2) = -(η * (r * r⁻¹) * (2 * 2⁻¹)) := by grind
    rw [h2_1] at Xbar_equation
    rw [mul_inv_cancel₀ r_ne_zero, mul_inv_cancel₀ (two_ne_zero hq_card hq_mod)] at Xbar_equation
    grind
  have h3 : η ≠ 0 := by
    unfold η ReconstructionCoordinates.η
    have h3_1 : y - 1 ≠ 0 := by grind
    have h3_2 : 2 * (y + 1) ≠ 0 := by
      intro h3_2_1
      let y_add_one_ne_zero := P_prop.1
      unfold ϕOverFProp1 at y_add_one_ne_zero
      rw [← div_left_inj' (two_ne_zero hq_card hq_mod)] at h3_2_1
      ring_nf at h3_2_1
      rw [inv_mul_cancel₀ (two_ne_zero hq_card hq_mod)] at h3_2_1
      grind
    apply div_ne_zero h3_1 h3_2
  contradiction

lemma Xbar_add_one_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_ne_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P q
    Xbar + 1 ≠ 0 := by
  grind [Xbar_ne_neg_one]

lemma y_with_Xbar (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_eq_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P.val q
    let r := r s
    let y := P.val.2
    y = (r * Xbar - (1 + Xbar) ^ 2) / (r * Xbar + (1 + Xbar) ^ 2) := by
  intro Xbar r y
  let Xbar_equation := Xbar_h2 hq_card hq_mod P
  let η := η P.val
  let y_add_one_ne_zero := P.prop.1
  let Xbar_ne_zero := Xbar_ne_zero hq_card hq_mod P
  let two_ne_zero := two_ne_zero hq_card hq_mod
  let r_ne_zero := r_ne_zero hs_ne_zero hq_card hq_mod
  change Xbar ^ 2 + 2 * (1 + η * r) * Xbar + 1 = 0 at Xbar_equation
  have h1 : y = (1 + 2 * η) / (1 - 2 * η) := by
    have h1_1 : η = (y - 1) / (2 * (y + 1)) := by simp [η, ReconstructionCoordinates.η, y]
    have h1_2 : (2 * (y + 1)) ≠ 0 := mul_ne_zero two_ne_zero y_add_one_ne_zero
    grind
  have h2 : 2 * η = - ((1 + Xbar) ^ 2) / (r * Xbar) := by
    have h2_1 : 1 + η * r = - (Xbar ^ 2 + 1) / (2 * Xbar) := by
      have h2_1_1 : 2 * Xbar ≠ 0 := mul_ne_zero two_ne_zero Xbar_ne_zero
      rw [← add_left_inj (-Xbar ^ 2), ← add_left_inj (-1)] at Xbar_equation
      rw [← div_left_inj' h2_1_1] at Xbar_equation
      grind
    have h2_2 : 2 * η = -((1 + Xbar) ^ 2) / (r * Xbar) := by
      have h2_2_1 : η = (-(Xbar ^ 2 + 1) / (2 * Xbar) -1) / r := by grind
      have h2_2_2 : η = -(Xbar + 1) ^ 2 / (2 * r * Xbar) := by
        have h2_2_2_1 : (2 * Xbar) / (2 * Xbar) = 1 := by grind
        rw [← h2_2_2_1] at h2_2_1
        rw [h2_2_1]
        ring_nf
        grind
      rw [← mul_left_inj' two_ne_zero] at h2_2_2
      ring_nf
      grind
    grind
  have h3 : (1 + 2 * η) / (1 - 2 * η)
      = ((r * Xbar - (1 + Xbar) ^ 2)) / ((r * Xbar + (1 + Xbar) ^ 2)) := by
    have h3_1 : 1 = (r * Xbar) / (r * Xbar) := by grind
    rw [h2]
    nth_rw 1 [h3_1]
    nth_rw 2 [h3_1]
    rw [← add_div, ← sub_div, div_div]
    grind
  rw [← h3]
  exact h1

lemma y_with_Xbar_of_Xbar_eq_one (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_eq_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P.val q
    let r := r s
    let y := P.val.2
    Xbar = 1 → y = (r - 4) / (r + 4) := by
  grind [y_with_Xbar]

lemma η_mul_r_eq_neg_two_of_Xbar_eq_one
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P}) :
    let η := η P
    let Xbar := Xbar s P q
    let r := r s
    Xbar = 1 → η * r = -2 := by
  intro η  Xbar r Xbar_h
  let h1 := Xbar_h2 hq_card hq_mod P
  let two_ne_zero := two_ne_zero hq_card hq_mod
  change Xbar ^ 2 + 2 * (1 + η *r) * Xbar + 1 = 0 at h1
  rw [Xbar_h, ← add_left_inj (-4), ← div_left_inj' two_ne_zero] at h1
  ring_nf at h1
  grind

lemma Xbar_observation1_of_Xbar_ne_one (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_eq_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P.val q
    let y := P.val.2
    let r := r s
    Xbar ≠ 1 → (r * Xbar + (1 + Xbar) ^ 2) ^ 2 * (1 - y ^ 2) = 4 * r * Xbar * (1 + Xbar) ^ 2 := by
  intro Xbar y r Xbar_h
  let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod P y_eq_one
  let y_divisor_ne_zero_with_Xbar_for_X :=
    y_divisor_ne_zero_with_Xbar_for_X hs_ne_zero hq_card hq_mod
  change y = (r * Xbar - (1 + Xbar) ^ 2) / (r * Xbar + (1 + Xbar) ^ 2) at y_with_Xbar
  have h1 : (r * Xbar + (1 + Xbar) ^ 2) ^ 2 * (1 - y ^ 2)
    = (r * Xbar + (1 + Xbar) ^ 2) ^ 2 - (r * Xbar - (1 + Xbar) ^ 2) ^ 2 := by
    rw [y_with_Xbar, div_pow, mul_sub, ← mul_div_assoc]
    nth_rw 3 [mul_comm]
    have h1_1 : (r * Xbar + (1 + Xbar) ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (by simp_all; grind)
    rw [mul_div_assoc, div_self h1_1]
    ring_nf
  grind

lemma Xbar_observation2_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_eq_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P.val q
    let y := P.val.2
    let r := r s
    let d := d s;
    Xbar ≠ 1 → (r * Xbar + (1 + Xbar) ^ 2) ^ 2 * (1 - d * y ^ 2)
      = ((2 * r) / (r - 2)) * (Xbar ^ 4 + (r ^ 2 - 2) * Xbar ^ 2 + 1) := by
  intro Xbar y r d Xbar_h
  let neg_d_eq_r_add_two_div_r_sub_two :=
    neg_d_eq_r_add_two_div_r_sub_two hs_ne_zero hq_card hq_mod
  change -d = (r + 2) / (r - 2) at neg_d_eq_r_add_two_div_r_sub_two
  let y_divisor_ne_zero_with_Xbar_for_X :=
    y_divisor_ne_zero_with_Xbar_for_X hs_ne_zero hq_card hq_mod
  let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod P y_eq_one
  change y = (r * Xbar - (1 + Xbar) ^ 2) / (r * Xbar + (1 + Xbar) ^ 2) at y_with_Xbar
  have h1 : (r * Xbar + (1 + Xbar) ^ 2) ^ 2 * (1 - d * y ^ 2)
    = (r * Xbar + (1 + Xbar) ^ 2) ^ 2 + (r + 2) / (r - 2) * ((r * Xbar - (1 + Xbar) ^ 2) ^ 2) := by
    rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← mul_assoc, ← neg_eq_neg_one_mul]
    rw [neg_d_eq_r_add_two_div_r_sub_two, y_with_Xbar, div_pow, mul_add]
    nth_rw 3 [mul_comm]
    have h1_1 : (r * Xbar + (1 + Xbar) ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (by simp_all; grind)
    rw [← mul_div_assoc, div_mul, mul_div_assoc, div_self h1_1]
    grind
  have h2 : (1 + Xbar) ^ 2 = Xbar ^ 2 + 2 * Xbar + 1 := by grind
  rw [h1, h2]
  let A := r * Xbar + (Xbar ^ 2 + 2 * Xbar + 1)
  let B := r * Xbar - (Xbar ^ 2 + 2 * Xbar + 1)
  change A ^ 2 + (r + 2) / (r - 2) * B ^ 2
    = 2 * r / (r - 2) * (Xbar ^ 4 + (r ^ 2 - 2) * Xbar ^ 2 + 1)
  have h3 : A ^ 2 = Xbar^ 4 + 2 * (r + 2) * Xbar ^ 3
      + ((r + 2) ^ 2 + 2) * Xbar ^ 2 + 2 * (r + 2) * Xbar + 1 := by
    ring
  have h4 : B ^ 2 = Xbar^ 4 - 2 * (r - 2) * Xbar ^ 3
      + ((r - 2) ^ 2 + 2) * Xbar ^ 2 - 2 * (r - 2) * Xbar + 1 := by
    ring
  rw [h3, h4]
  let r_sub_two_ne_zero :=
    r_sub_two_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod
  have X_pow_four_term : Xbar ^ 4 + (r + 2) / (r - 2) * Xbar ^ 4
    = Xbar ^ 4 * (2 * r) / (r - 2) := by grind
  have X_pow_three_term : Xbar ^ 3 * 2 * (r + 2)
    + (r + 2) / (r - 2) * (-2 * (r - 2) * Xbar ^ 3) = 0 := by grind
  have X_pow_two_term : Xbar ^ 2 * (r ^ 2+ 4 * r + 6) + (r + 2) / (r - 2) * (r ^ 2 - 4 * r + 6)
    * Xbar ^ 2 = Xbar ^ 2 * (2 * r * (r ^ 2 - 2) / (r - 2)) := by
    nth_rw 3 [mul_comm]
    rw [← mul_add (Xbar ^ 2)]
    have h5 : (r ^ 2 + 4 * r + 6 + (r + 2) / (r - 2) * (r ^ 2 - 4 * r + 6))
      = ((r ^ 2 + 4 * r + 6) * (r - 2) + (r + 2) * (r ^ 2 - 4 * r + 6)) / (r - 2) := by grind
    rw [h5]
    have h6 : (r ^ 2 + 4 * r + 6) * (r - 2) = r ^ 3 + 2 * r ^ 2 - 2 * r - 12 := by ring
    have h7 : (r + 2) * (r ^ 2 - 4 * r + 6) = r ^ 3 - 2 * r ^ 2 - 2 * r + 12 := by ring
    rw [h6, h7]
    have h8 : r ^ 3 + 2 * r ^ 2 - 2 * r - 12 + (r ^ 3 - 2 * r ^ 2 - 2 * r + 12)
        = 2 * r ^ 3 - 4 * r := by
      ring
    ring
  have X_pow_one_term : 2 * (r + 2) * Xbar - 2 * (r + 2) * Xbar = 0 := by ring
  have const_term : 1 + (r + 2) / (r - 2) = (2 * r) / (r - 2) := by grind
  grind

lemma one_sub_d_mul_y_pow_two_ne_zero
    (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P}) :
    let y := P.val.2
    let d := d s;
    1 - d * y ^ 2 ≠ 0 := by
  intro y d h1
  let d_ne_zero := d_ne_zero sq_ne_pm_two hq_card hq_mod
  rw [← add_left_inj (d * y ^ 2)] at h1
  ring_nf at h1
  rw [mul_comm, ← div_left_inj' d_ne_zero, mul_div_assoc, div_self d_ne_zero, mul_one] at h1
  change 1 / d = y ^ 2 at h1
  have h2 : IsSquare (1 / d) := by
    unfold IsSquare
    use y
    grind
  let h3 := one_div_d_nonsquare sq_ne_pm_two hq_card hq_mod
  change ¬IsSquare (1 / d) at h3
  contradiction

lemma x_pow_two_of_Xbar_ne_one_eq1
    (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod})
    (P_props : ϕOverFProps s P) :
    let x := P.val.1
    let y := P.val.2
    let d := d s;
    x ^ 2 = (1 - y ^ 2) / (1 - d*y ^ 2) := by
  intro x y d
  have curve_equation := P.prop;
  rw [mem_EOverF_iff] at curve_equation
  let one_sub_d_mul_y_pow_two_ne_zero :=
    one_sub_d_mul_y_pow_two_ne_zero sq_ne_pm_two hq_card hq_mod ⟨P.val, P_props⟩
  change 1 - d * y ^ 2 ≠ 0 at one_sub_d_mul_y_pow_two_ne_zero
  change x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2  at curve_equation
  rw [← add_left_inj (-d * x ^ 2 * y ^ 2 - y ^ 2)] at curve_equation
  ring_nf at curve_equation
  nth_rw 1 [← mul_one (x ^ 2)] at curve_equation
  rw [mul_assoc, ← mul_sub (x ^ 2)] at curve_equation
  nth_rw 2 [mul_comm] at curve_equation
  rw [← div_left_inj' one_sub_d_mul_y_pow_two_ne_zero] at curve_equation
  simp_all

lemma x_pow_two_of_Xbar_ne_one_eq2_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (y_eq_one : P.val.2 ≠ 1) :
    let x := P.val.1
    let X := Xbar s P q
    let r := r s
    X ≠ 1 → x ^ 2 = (2 * (r -2) * X ^ 2 * (1 + X) ^ 2) / (X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X) := by
  intro x X r Xh
  let y := P.val.2
  let d := d s;
  let x_pow_two_of_Xbar_ne_one_eq1 :=
    x_pow_two_of_Xbar_ne_one_eq1 sq_ne_pm_two hq_card hq_mod P P_props
  change x ^ 2 = (1 - y ^ 2) / (1 - d*y ^ 2) at x_pow_two_of_Xbar_ne_one_eq1
  let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_eq_one
  change y = (r * X - (1 + X) ^ 2) / (r * X + (1 + X) ^ 2) at y_with_Xbar
  let y_divisor_ne_zero_with_Xbar_for_X :=
    y_divisor_ne_zero_with_Xbar_for_X hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
  change r * X + (1 + X) ^ 2 ≠ 0 at y_divisor_ne_zero_with_Xbar_for_X
  have h1 : (r * X + (1 + X) ^ 2) ^ 2 ≠ 0 := by grind
  have h2 : 1 = ((r * X + (1 + X) ^ 2) ^ 2) / ((r * X + (1 + X) ^ 2) ^ 2) := by grind
  let Xbar_observation1_of_Xbar_ne_one :=
    Xbar_observation1_of_Xbar_ne_one hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_eq_one
  change X ≠ 1 →
    (r * X + (1 + X) ^ 2) ^ 2 * (1 - y ^ 2) = 4 * r * X * (1 + X) ^ 2
    at Xbar_observation1_of_Xbar_ne_one
  have h3 : (r * X + (1 + X) ^ 2) ^ 2 * (1 - y ^ 2) = 4 * r * X * (1 + X) ^ 2 := by grind
  let Xbar_observation2_of_Xbar_ne_one := Xbar_observation2_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod ⟨P.val, P_props⟩ y_eq_one
  change X ≠ 1 → (r * X + (1 + X) ^ 2) ^ 2 * (1 - d * y ^ 2)
    = ((2 * r) / (r - 2)) * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1) at Xbar_observation2_of_Xbar_ne_one
  have h4 : (r * X + (1 + X) ^ 2) ^ 2 * (1 - d * y ^ 2)
    = ((2 * r) / (r - 2)) * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1) := by grind
  let X_ne_zero := Xbar_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
  change X ≠ 0 at X_ne_zero
  calc
    x ^ 2 = (1 - y ^ 2) / (1 - d*y ^ 2) := by grind
    _ = (4 * r * X * (1 + X) ^ 2) / ((2 * r) / (r - 2) * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)) := by
      rw [← one_mul (1 - y ^ 2), ← one_mul (1 - d * y ^ 2)]
      nth_rw 1 [h2]
      rw [mul_div_assoc, div_mul_div_comm]
      grind
    _ = (2 * (r - 2) * X * (1 + X) ^ 2) / (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1) := by
      let r_sub_two_ne_zero := r_sub_two_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod
      change r - 2 ≠ 0 at r_sub_two_ne_zero
      have h' : 1 = (r - 2) / (r - 2) := by grind
      rw [← one_mul
        ((4 * r * X * (1 + X) ^ 2) / ((2 * r) / (r - 2) * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)))]
      nth_rw 1 [h']
      rw [div_mul_div_comm]
      nth_rw 2 [← mul_assoc]
      nth_rw 1 [← mul_div_assoc]
      rw [mul_comm (r - 2) (2 * r), mul_div_assoc]
      nth_rw 2 [mul_div_assoc]
      rw [div_self r_sub_two_ne_zero, ← mul_div_assoc]
      have h'' :
        (r - 2) * (4 * r * X * (1 + X) ^ 2) / (2 * r * 1 * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1))
        = (r - 2) * (2 * X * (1 + X) ^ 2) / ((X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)) := by
        have h''' : (4 * r) / (2 * r) = 2 := by
          let two_ne_zero := two_ne_zero hq_card hq_mod
          let r_ne_zero := (r_ne_zero hs_ne_zero hq_card hq_mod)
          rw [← mul_left_inj' two_ne_zero]
          ring_nf
          rw [mul_inv_cancel₀ r_ne_zero]
          grind
        have h'''' :
          (r - 2) * (4 * r * X * (1 + X) ^ 2) / (2 * r * 1 * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1))
          = ((r - 2) * (X * (1 + X) ^ 2)) * (4 * r)
              / ((2 * r) * (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)) := by ring
        rw [h'''', div_mul_eq_div_div, mul_div_assoc, h''']
        ring
      rw [h'']
      ring
    _ = (2 * (r -2) * X ^ 2 * (1 + X) ^ 2) / (X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X) := by
      have h5 : 1 = X / X := by grind
      nth_rw 1 [← one_mul ((2 * (r - 2) * X * (1 + X) ^ 2) / (X ^ 4 + (r ^ 2 - 2) * X ^ 2 + 1)), h5]
      rw [div_mul_div_comm]
      ring

/-- `Y'` is the `Y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def Y' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
    let x := P.val.1
    let c := c s
    let X := Xbar s P q
    -- This is just `def x` with the denominator `Y` replaced by `x` of P
    (c - 1) * s * X * (1 + X) / x

lemma Y'_pow_two_eq_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (y_eq_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let r := r s
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    -- This is just `def x` with the denominator `Y` replaced by `x` of P
    X ≠ 1 → Y ^ 2 = X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X := by
  intro X r Y Xh
  let c := c s
  let x := P.val.1
  let h := x_pow_two_of_Xbar_ne_one_eq2_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_eq_one
  let two_ne_zero := two_ne_zero hq_card hq_mod
  have h' : x ^ 2 = (2 * (r -2) * X ^ 2 * (1 + X) ^ 2) / (X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X) := h Xh
  calc
    Y ^ 2 = (c - 1) ^ 2 * s ^ 2 * X ^ 2 * (1 + X) ^ 2 / (x ^ 2) := by
      unfold Y Y'
      change ((c - 1) * s * X * (1 + X) / x) ^ 2
        = (c - 1) ^ 2 * s ^ 2 * X ^ 2 * (1 + X) ^ 2 / (x ^ 2)
      rw [div_pow]
      repeat rw [← mul_pow]
  _ = 2 * (r - 2) * X ^ 2 * (1 + X) ^ 2 / (x ^ 2) := by
    have h : (c - 1) ^ 2 * s ^ 2 = 2 * (r - 2) := by
      unfold r CurveParameters.r c CurveParameters.c
      field_simp [hs_ne_zero]
      ring
    rw [h]
  _ = X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X := by
    have h'' : (2 * (r - 2) * X ^ 2 * (1 + X) ^ 2) ≠ 0 := by
      let Xbar_add_one_ne_zero :=
        Xbar_add_one_ne_zero hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_eq_one
      let r_sub_two_ne_zero := r_sub_two_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let Xbar_ne_zero := Xbar_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
      rw [add_comm]
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero two_ne_zero r_sub_two_ne_zero
        · apply pow_ne_zero 2 Xbar_ne_zero
      · apply pow_ne_zero 2 Xbar_add_one_ne_zero
    rw [h']
    nth_rw 1 [← div_one (2 * (r - 2) * X ^ 2 * (1 + X) ^ 2)]
    rw [div_div_div_comm, div_self h'']
    simp_all

lemma Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_ne_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P q
    Xbar ≠ 1 → Xbar ≠ 1 ∧ Xbar ≠ -1 :=
  by grind [Xbar_ne_neg_one]

end Xbar

section z

/-- z is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:z"
  (title := "The inversion sign $z$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\bar X$ as above, define
  $$
  z = \chi\bigl((c - 1)s\bar X(1 + \bar X)x(\bar X ^ 2 + 1/c ^ 2)\bigr) .
  $$
  -/)]
def z (s : F) (P : F × F) (q : ℕ) : F :=
    let x := P.fst
    let c := c s
    let Xbar := Xbar s P q
    χ ((c - 1) * s * Xbar * (1 + Xbar) * x * (Xbar ^ 2 + 1 / c ^ 2))

lemma z_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let z := z s P q
    z = 0 := by
  intro P z
  unfold z ReconstructionCoordinates.z
  let c := c s
  repeat rw [Xbar_eq_neg_one t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  simp_all

/-- `z'` is the `z` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def z' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  let X := Xbar s P q
  let c := c s
  χ (Y * (X ^ 2 + 1 / c ^ 2))

lemma Y'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    Y ≠ 0 := by
  intro Y
  have Xbar_add_one_ne_zero :=
    Xbar_add_one_ne_zero hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  have Xbar_ne_zero := Xbar_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
  have c_sub_one_ne_zero := c_sub_one_ne_zero sq_ne_pm_two
  unfold Y Y'
  grind

omit [DecidableEq F] in
lemma X_pow_two_add_1_div_c_pow_two_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) :
    let X := Xbar s P q
    let c := c s
    X ^ 2 + 1 / c ^ 2 ≠ 0 := by
  intro X c h
  rw [← mul_left_inj' (c_ne_zero hs_ne_zero hq_card hq_mod)] at h
  rw [← mul_left_inj' (c_ne_zero hs_ne_zero hq_card hq_mod)] at h
  ring_nf at h
  change X ^ 2 * c ^ 2 + c⁻¹^2 * c ^ 2 = 0 at h
  rw [inv_pow c 2, inv_mul_cancel₀ (pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod))] at h
  rw [← add_left_inj (-1 : F), ← mul_pow] at h
  simp only [add_neg_cancel_right, zero_add] at h
  let h' := neg_one_non_square hq_card hq_mod
  have h'' : IsSquare (-1 : F) := by
    rw [← h, pow_two]
    apply IsSquare.mul_self
  contradiction

lemma z'_argument_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    let c := c s
    Y * (X ^ 2 + 1 / c ^ 2) ≠ 0 := by
  grind [Y'_ne_zero, X_pow_two_add_1_div_c_pow_two_ne_zero]

lemma z'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let z := z' sq_ne_pm_two hq_card hq_mod P
    z ≠ 0 := by
  intro z
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  let X := Xbar s P q
  let c := c s
  let z'_argument_ne_zero :=
    z'_argument_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let a := (Y * (X ^ 2 + 1 / c ^ 2))
  exact χ_a_ne_zero z'_argument_ne_zero

lemma z'_eq_one_or_z'_eq_neg_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let z := z' sq_ne_pm_two hq_card hq_mod P
    z = 1 ∨ z = -1 := by
  intro z
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  let X := Xbar s P q
  let c := c s
  let a := (Y * (X ^ 2 + 1 / c ^ 2))
  open Classical in
  let χ_of_a := χ a
  have h1 := χ_values (a := a)
  change χ_of_a = 0 ∨ χ_of_a = -1 ∨ χ_of_a = 1 at h1
  have h2 := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  change χ_of_a ≠ 0 at h2
  change χ_of_a = 1 ∨ χ_of_a = -1
  simp_all
  grind

end z

section ubar

/-- ubar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:ubar"
  (title := "The reconstructed quantity $\\bar u$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $z$ and $\bar X$ as above, define
  $$
  \bar u = z\bar X .
  $$
  -/)]
def ubar (s : F) (P : F × F) (q : ℕ) : F :=
    let Xbar := Xbar s P q
    let z := z s P q
    z * Xbar

lemma ubar_eq_zero (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let ubar := ubar s P q
    ubar = 0 := by
  grind [z_eq_zero, ubar]

lemma ubar_eq_u (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      let X := X t s
      let Xbar := Xbar s P q
      Xbar = X) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let u := u t
    let ubar := ubar s P q
    ubar = u := by
  intro P u ubar
  let X := X t s
  let Xbar := Xbar s P q
  let c := c s
  let x := x t s q
  let Y := Y t s q
  let z := z s P q
  let v := v t s;
  let χ_of_v := χ v
  let χ_of_Y := χ Y
  unfold ubar ReconstructionCoordinates.ubar
  rw [hXXbar]
  change z * X = u
  have hXbar_expand_eq_x_mul_Y : (c - 1) * s * Xbar * (1 + Xbar) = x * Y := by
    unfold Xbar
    rw [hXXbar]
    rw [← div_left_inj' (Y_ne_zero hs_ne_zero hq_card hq_mod t)]
    change x = x * Y / Y
    rw [mul_div_assoc, div_self (Y_ne_zero hs_ne_zero hq_card hq_mod t)]
    ring_nf
  have hz_eq_χY_mul_χ_sum : z = χ_of_Y * χ (X ^ 2 + 1 / c ^ 2) := by
    calc
      z = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2)) := by
        unfold z ReconstructionCoordinates.z
        change χ ((c - 1) * s * Xbar * (1 + Xbar) * P.1 * (Xbar ^ 2 + 1 / c ^ 2))
          = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2))
        unfold P ϕ
        simp only [hXbar_expand_eq_x_mul_Y]
        rw [dite_eq_left t.prop]
        change χ (x * Y * x * (Xbar ^ 2 + 1 / c ^ 2)) = χ (x ^ 2 * Y * (X ^ 2 + 1 / c ^ 2))
        unfold Xbar X
        rw [hXXbar]
        ring_nf
      _ = χ_of_Y * χ (X ^ 2 + 1 / c ^ 2) := by
        rw [χ_mul, χ_mul]
        rw [χ_a_eq_one (pow_ne_zero 2
          (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t))
          (IsSquare.sq x)]
        unfold χ_of_Y
        ring
  have hχu_sum_eq_χX_sum : χ (u ^ 2 + 1 / c ^ 2) = χ (X ^ 2 + 1 / c ^ 2) := by
    unfold X AuxiliaryCoordinates.X
    rw [mul_pow]
    nth_rw 3 [pow_two]
    rw [← χ_mul]
    rw [← pow_two, χ_a_eq_one
      (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod t)) (IsSquare.sq v)]
    unfold u
    simp_all
  have hχY_eq_χv_mul_χ_sum : χ_of_Y = χ_of_v * χ (X ^ 2 + 1 / c ^ 2) := by
    rw [← hχu_sum_eq_χX_sum]
    unfold χ_of_Y Y AuxiliaryCoordinates.Y
    let χ_sum := χ (u ^ 2 + 1 / c ^ 2)
    change χ ((χ_of_v * v) ^ ((q + 1) / 4) * χ_of_v * χ_sum) = χ_of_v * χ_sum
    rw [mul_assoc, χ_mul]
    rw [χ_a_eq_one
      (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero t hs_ne_zero hq_card hq_mod)
      (χ_IsSquare_h1 t hs_ne_zero hq_card hq_mod)]
    rw [χ_mul]
    rw [χ_χ_eq_χ hq_card hq_mod]
    rw [χ_χ_eq_χ hq_card hq_mod]
    unfold χ_of_v χ_sum
    simp_all
  have hz_eq_χv : z = χ_of_v := by
    rw [hz_eq_χY_mul_χ_sum, hχY_eq_χv_mul_χ_sum, mul_assoc, ← χ_mul, ← pow_two]
    rw [χ_a_eq_one
      (pow_ne_zero 2 (X_pow_two_add_one_div_c_pow_two_ne_zero hs_ne_zero hq_card hq_mod t))
      (IsSquare.sq (X ^ 2 + 1 / c ^ 2))]
    simp
  rw [hz_eq_χv]
  unfold X AuxiliaryCoordinates.X
  change χ_of_v * (χ_of_v * u) = u
  rw [← mul_assoc, ← χ_mul, ← pow_two]
  have hv_sq_isSquare : IsSquare (v ^ 2) := IsSquare.sq v
  rw [χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod t)) hv_sq_isSquare]
  simp

lemma ubar_eq_u' (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
      let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
      let Xbar := Xbar s P q
      Xbar = X') :
    let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let u' := u ⟨-t.val, t_h⟩
    let ubar := ubar s P q
    ubar = u' := by
  intro t_h P u' ubar
  let X' := X ⟨-t.val, t_h⟩ s
  let X := X t s
  let Xbar := Xbar s P q
  let c := c s
  let x' := x ⟨-t.val, t_h⟩ s q
  let x := x t s q
  let Y' := Y ⟨-t.val, t_h⟩ s q
  let Y := Y t s q
  let z := z s P q
  let v' := v ⟨-t.val, t_h⟩ s
  let v := v t s;
  unfold ubar ReconstructionCoordinates.ubar
  rw [hXXbar]
  change z * X' = u'
  have hXbar_expand_eq_x'_mul_Y' : (c - 1) * s * Xbar * (1 + Xbar) = x' * Y' := by
    unfold Xbar
    rw [hXXbar]
    rw [← div_left_inj' (Y_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩)]
    change x' = x' * Y' / Y'
    rw [mul_div_assoc, div_self (Y_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩)]
    ring_nf
  have hz_eq_χY'_mul_χ_sum : z = (χ Y') * (χ (X'^2 + 1 / c ^ 2)) := by
    calc
      z = (χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))) := by
        unfold z ReconstructionCoordinates.z
        change χ ((c - 1) * s * Xbar * (1 + Xbar) * P.1 * (Xbar ^ 2 + 1 / c ^ 2))
          = χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))
        unfold P ϕ
        simp only [hXbar_expand_eq_x'_mul_Y']
        rw [dite_eq_left t.prop]
        change χ (x' * Y' * x * (Xbar ^ 2 + 1 / c ^ 2)) = χ (x'^2 * Y' * (X'^2 + 1 / c ^ 2))
        unfold Xbar X' x' x
        rw [x_comparison t hs_ne_zero hq_card hq_mod]
        rw [hXXbar]
        ring_nf
      _ = (χ Y') * χ (X'^2 + 1 / c ^ 2) := by
        rw [χ_mul]
        rw [χ_mul]
        rw [χ_a_eq_one (pow_ne_zero 2
          (x_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod ⟨-t, t_h⟩))
          (IsSquare.sq x')]
        ring_nf
  have hχu'_sum_eq_χX'_sum : (χ (u'^2 + 1 / c ^ 2)) = (χ (X'^2 + 1 / c ^ 2)) := by
    unfold X' AuxiliaryCoordinates.X
    rw [mul_pow]
    nth_rw 3 [pow_two]
    rw [← χ_mul]
    rw [← pow_two, χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod ⟨-t, t_h⟩))
      (IsSquare.sq v')]
    unfold u'
    simp_all
  have hχY'_eq_χv'_mul_χ_sum : (χ Y') = (χ v') * (χ (X'^2 + 1 / c ^ 2)) := by
    rw [← hχu'_sum_eq_χX'_sum]
    unfold Y' AuxiliaryCoordinates.Y
    let χ_sum := χ (u'^2 + 1 / c ^ 2);
    change (χ (((χ v') * v') ^ ((q + 1) / 4) * (χ v') * χ_sum)) = (χ v') * χ_sum
    rw [mul_assoc, χ_mul]
    rw [χ_a_eq_one
      (χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero ⟨-t.val, t_h⟩ hs_ne_zero hq_card hq_mod)
      (χ_IsSquare_h1 ⟨-t.val, t_h⟩ hs_ne_zero hq_card hq_mod)]
    rw [χ_mul, χ_χ_eq_χ hq_card hq_mod]
    rw [χ_χ_eq_χ hq_card hq_mod]
    unfold χ_sum
    simp_all
  have hz_eq_χv' : z = (χ v') := by
    rw [hz_eq_χY'_mul_χ_sum, hχY'_eq_χv'_mul_χ_sum, mul_assoc]
    rw [← χ_mul, ← pow_two]
    rw [χ_a_eq_one (pow_ne_zero 2
        (X_pow_two_add_one_div_c_pow_two_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩))
      (IsSquare.sq (X'^2 + 1 / c ^ 2))]
    simp
  rw [hz_eq_χv']
  unfold X' AuxiliaryCoordinates.X
  change (χ v') * ((χ v') * u') = u'
  rw [← mul_assoc, ← χ_mul, ← pow_two]
  have hv'_sq_isSquare : IsSquare (v'^2) := IsSquare.sq v'
  rw [χ_a_eq_one (pow_ne_zero 2 (v_ne_zero hs_ne_zero hq_card hq_mod ⟨-t.val, t_h⟩))
    hv'_sq_isSquare]
  simp

lemma ubar_h1 (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let u' := u ⟨-t.val, t_h⟩
    let u := u t
    let ubar := ubar s P.val q
    ubar = u ∨ ubar = u' := by
  intro P t_h u' u ubar
  rcases (Xbar_h4 t hs_ne_zero sq_ne_pm_two hq_card hq_mod) with h | h
  · left
    exact ubar_eq_u t hs_ne_zero sq_ne_pm_two hq_card hq_mod h
  · right
    exact ubar_eq_u' t hs_ne_zero sq_ne_pm_two hq_card hq_mod h

/-- The key step: rewriting `1 + ubar(ϕ(t))` in the main case (t ≠ ±1) to show it is ne_zero,
    using `ubar_h1` which gives `ubar = u(t)` or `ubar = u(-t)`. -/
lemma one_add_ubar_ne_zero_main_case (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : (s : F) ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    let ubar := ubar s P q
    1 + ubar ≠ 0 := by
  intro P ubar
  unfold ubar
  obtain h|h := ubar_h1 t hs_ne_zero sq_ne_pm_two hq_card hq_mod
  · rw [h]
    exact one_add_u_ne_zero t hq_card hq_mod
  · rw [h]
    have ht_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    exact one_add_u_ne_zero ⟨-t.val, ht_h⟩ hq_card hq_mod

lemma one_add_ubar_ne_zero_base_case (t : {n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).1
    let ubar := ubar s P q
    1 + ubar ≠ 0 := by
  intro P ubar
  unfold ubar
  rw [ubar_eq_zero, add_zero]
  exact one_ne_zero' F

lemma one_add_ubar_ne_zero (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ ϕOverF hs_ne_zero sq_ne_pm_two hq_card hq_mod}) :
    let ubar := ubar s P q
    (1 + ubar) ≠ 0 := by
  intro ubar
  have hP_prop := P.prop
  unfold ϕOverF at hP_prop
  obtain ⟨t, ht⟩ := hP_prop
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · have hne := one_add_ubar_ne_zero_main_case ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
    grind
  · have ht_eq : t = 1 ∨ t = -1 := by grind
    have hne := one_add_ubar_ne_zero_base_case ⟨t, ht_eq⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
    grind

/-- `u'` is the `u` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def u' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let z := z' sq_ne_pm_two hq_card hq_mod P
  let X := Xbar s P q
  z * X

lemma u'_pow_two_eq_X_pow_two
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    u ^ 2 = X ^ 2 := by
  grind [u, u', z', z'_eq_one_or_z'_eq_neg_one]

lemma u'_eq_Xbar_or_u'_eq_neg_Xbar
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    u = X ∨ u = -X := by
  grind [u, u', z'_eq_one_or_z'_eq_neg_one]

lemma u'_ne_neg_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    X ≠ 1 → u ≠ -1 := by
  intro u X h1
  have hz'_cases := z'_eq_one_or_z'_eq_neg_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hXbar_ne_pm_one := Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold u u'
  grind

lemma one_add_u'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    X ≠ 1 → 1 + u ≠ 0 := by
  intro u X h1
  have hz'_cases := z'_eq_one_or_z'_eq_neg_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hXbar_ne_pm_one := Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold u u'
  grind

lemma u'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    X ≠ 1 → u ≠ 0 := by
  intro u X h1
  have hz'_cases := z'_eq_one_or_z'_eq_neg_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hz_ne_zero := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  have hXbar_ne_zero := Xbar_ne_zero hq_card hq_mod ⟨P.val, P_props⟩
  have hXbar_ne_pm_one := Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold u u'
  grind

/-- `v'` is the `v` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def v' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let r := r s
  -- Note: this is just the definition of v as in theorem 1
  u ^ 5 + (r ^ 2 - 2) * u ^ 3 + u

lemma v'_eq_z'_mul_Y'_pow_two
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (y_ne_one : P.val.2 ≠ 1) :
    let z := z' sq_ne_pm_two hq_card hq_mod P
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let X := Xbar s P q
    X ≠ 1 → v = z * Y ^ 2 := by
  intro z Y v X h1
  let r := r s
  let c := c s
  have hXbar_ne_pm_one := Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  have hY'_sq := Y'_pow_two_eq_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_ne_one
  have hz_cube_eq_z : z ^ 3 = z := by
    have := χ_of_a_pow_n_eq_χ_a (Y * (X ^ 2 + 1 / c ^ 2)) ⟨3, by grind⟩
    change z ^ 3 = z at this
    exact this
  have hz_pow5_eq_z : z ^ 5 = z := by
    have := χ_of_a_pow_n_eq_χ_a (Y * (X ^ 2 + 1 / c ^ 2)) ⟨5, by grind⟩
    change z ^ 5 = z at this
    exact this
  let x := P.val.1
  have hv_eq_z_mul_expand : v = z * (X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X) := by
    change (z * X) ^ 5 + (r ^ 2 - 2) * (z * X) ^ 3 + (z * X) = z * (X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X)
    repeat rw [mul_pow]
    rw [hz_cube_eq_z, hz_pow5_eq_z]
    grind
  grind

lemma v'_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let v := v' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → v ≠ 0 := by
  intro X v h1
  have hv_eq_z_mul_Y_sq :=
    v'_eq_z'_mul_Y'_pow_two hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  have hv_eq_zY2 : v = z * Y ^ 2 := by grind
  rw [hv_eq_zY2]
  have hY_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  have hz_ne_zero := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  grind

lemma χ_of_v'_eq_χ_of_z'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let z := z' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let χ_of_v := χ v
    let χ_of_z := χ z
    X ≠ 1 → χ_of_v = χ_of_z := by
  intro X z v χ_of_v χ_of_z h
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  have hv_eq_zY2 :=
    v'_eq_z'_mul_Y'_pow_two hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_ne_one
  unfold χ_of_v v
  rw [hv_eq_zY2 h]
  have hY_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  rw [χ_of_a_eq_χ_a_mul_b_pow_two hY_ne_zero]

lemma χ_of_z'_eq_z' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) :
    let X := Xbar s P q
    let z := z' sq_ne_pm_two hq_card hq_mod P
    let χ_of_z := χ z
    X ≠ 1 → χ_of_z = z := by
  intro X z χ_of_z h1
  exact χ_χ_eq_χ hq_card hq_mod

lemma χ_of_v'_eq_z'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let z := z' sq_ne_pm_two hq_card hq_mod P
    let χ_of_v := χ v
    X ≠ 1 → χ_of_v = z := by
  grind [χ_of_v'_eq_χ_of_z', χ_of_z'_eq_z']

lemma X'_eq_χ_of_v'_mul_u'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let χ_of_v := χ v
    X ≠ 1 → X = χ_of_v * u := by
  intro X v u χ_of_v h1
  have hχv_eq_z := χ_of_v'_eq_z'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  unfold χ_of_v v
  rw [hχv_eq_z h1]
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hz_ne_zero := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  rw [mul_comm, ← div_left_inj' hz_ne_zero]
  rw [mul_div_assoc, div_self hz_ne_zero]
  change X / z = z * X * 1
  have hz_arg_ne_zero :=
    z'_argument_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let Y := Y' sq_ne_pm_two hq_card hq_mod P
  let c := c s
  let a := (Y * (X ^ 2 + 1 / c ^ 2))
  nth_rw 1 [← mul_one X]
  unfold z z'
  rw [mul_div_assoc, ← one_div_χ_of_a_eq_χ_a]
  grind

lemma Y'_pow_two_eq_χ_of_v'_mul_v'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let χ_of_v := χ v
    X ≠ 1 → Y ^ 2 = χ_of_v * v := by
  intro X Y v χ_of_v h1
  have hv_eq_zY2 :=
    v'_eq_z'_mul_Y'_pow_two hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props y_ne_one
  let z := z' sq_ne_pm_two hq_card hq_mod P
  have hv_eq_zY2' : v = z * Y ^ 2 := by grind
  have hz_ne_zero := z'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  rw [mul_comm, ← div_left_inj' hz_ne_zero] at hv_eq_zY2'
  rw [mul_div_assoc, div_self hz_ne_zero, mul_one] at hv_eq_zY2'
  change v / z = Y ^ 2 at hv_eq_zY2'
  have hz_arg_ne_zero :=
    z'_argument_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let c := c s
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let r := r s
  let a := u ^ 5 + (r ^ 2 - 2) * u ^ 3 + u
  rw [← hv_eq_zY2', mul_comm]
  unfold χ_of_v v v'
  rw [one_div_χ_of_a_eq_χ_a]
  change v / z = v * (1 / χ_of_v)
  have hχv_eq_z := χ_of_v'_eq_z'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  unfold χ_of_v v
  rw [hχv_eq_z h1]
  grind

lemma χ_of_v'_eq_z'_unfold_of_X'_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let c := c s
    X ≠ 1 → (χ v) = χ (Y * (X ^ 2 + 1 / c ^ 2)) := by
  intro X Y v c h1
  rw [χ_of_v'_eq_z' hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1]
  rfl

lemma χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_div_c_pow_two
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let c := c s
    X ≠ 1 → (χ v) = χ (Y * (u ^ 2 + 1 / c ^ 2)) := by
  grind [χ_of_v'_eq_z'_unfold_of_X'_ne_one, u'_pow_two_eq_X_pow_two]

lemma u'_pow_two_add_one_div_c_pow_two_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) :
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let c := c s
    u ^ 2 + 1 / c ^ 2 ≠ 0 := by
  intro u c h
  have hneg_one_sq : -1 = (u * c) ^ 2 := by grind [pow_ne_zero, c_ne_zero]
  have hisSquare : IsSquare (-1 : F) := by
    rw [hneg_one_sq, pow_two]
    apply IsSquare.mul_self (u * c)
  have hmod_ne_three : q % 4 ≠ 3 := by
    rw [FiniteField.isSquare_neg_one_iff, hq_card] at hisSquare
    exact hisSquare
  contradiction

lemma Y'_observation1
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let c := c s
    X ≠ 1 → (χ Y) = (χ v) * χ (u ^ 2 + 1 / c ^ 2) := by
  intro X Y v u c h1
  have hχv_eq_χ_term := χ_of_v'_eq_z'_unfold_of_X'_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  have hχv_eq_χ_Yu := χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_div_c_pow_two
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  let term1 := (u ^ 2 + 1 / c ^ 2)
  let term2 := Y * term1
  have hstep2 : (χ v) * χ (u ^ 2 + 1 / c ^ 2) = (χ term2) * χ (u ^ 2 + 1 / c ^ 2) := by grind
  have hstep3 : (χ v) * χ (u ^ 2 + 1 / c ^ 2) = (χ Y) * (χ term1) * χ (u ^ 2 + 1 / c ^ 2) := by
    grind [χ_mul]
  rw [hstep3]
  have hterm1_mul_self_eq_one : (χ term1) * χ (u ^ 2 + 1 / c ^ 2) = 1 := by
    rw [← pow_two]
    have hterm1_ne_zero := u'_pow_two_add_one_div_c_pow_two_ne_zero
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P
    rw [χ_of_a_even_pow_n_eq_one hterm1_ne_zero ⟨2, even_two⟩]
  grind

lemma Y'_observation2
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let Y := Y' sq_ne_pm_two hq_card hq_mod P
    let v := v' sq_ne_pm_two hq_card hq_mod P
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let c := c s
  X ≠ 1 → Y = ((χ v) * v) ^ ((q + 1) / 4) * (χ v) * χ (u ^ 2 + 1 / c ^ 2) := by
  intro X Y v u c h1
  have hχv_eq_χ_term := χ_of_v'_eq_z'_unfold_of_X'_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  have hχv_eq_χ_Yu := χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_div_c_pow_two
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  have hobs1 := Y'_observation1
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  change (χ Y) = (χ v) * χ (u ^ 2 + 1 / c ^ 2) at hobs1
  have hY_sq := Y'_pow_two_eq_χ_of_v'_mul_v'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  rw [← hY_sq, mul_assoc, ← hobs1]
  rw [← pow_mul, add_comm]
  change Y = Y ^ (2 * ((1 + q) / 4)) * (χ Y)
  nth_rw 2 [mul_comm]
  rw [one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
  rw [add_comm, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_card hq_mod]
  rw [mul_comm, ← mul_assoc]
  rw [← χ_mul, ← pow_two]
  have hY_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero
    y_ne_one
  rw [χ_sq hY_ne_zero]
  grind

end ubar

section tbar

/-- tbar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:tbar"
  (title := "The reconstructed preimage $\\bar t$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\bar u$ as above, define
  $$
  \bar t = (1 - \bar u)/(1 + \bar u) .
  $$
  -/)]
def tbar (s : F) (P : F × F) (q : ℕ) : F :=
    let ubar := ubar s P q
    (1 - ubar) / (1 + ubar)

lemma tbar_eq_one (t : { t : F // t = 1 ∨ t = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let tbar := tbar s P q
    tbar = 1 := by
  intro P tbar_of_P
  unfold tbar_of_P tbar
  let ubar_of_P := ubar s P q
  change (1 - ubar_of_P) / (1 + ubar_of_P) = 1
  unfold ubar_of_P
  rw [ubar_eq_zero t hs_ne_zero sq_ne_pm_two hq_card hq_mod]
  simp

lemma tbar_eq_t (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let X := X t s
      let Xbar := Xbar s P q
      Xbar = X) :
    let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let tbar_of_P := tbar s P q
    tbar_of_P = t := by
  intro P tbar_of_P
  let u := u t
  let ubar := ubar s P q
  have h : ubar = u := ubar_eq_u t hs_ne_zero sq_ne_pm_two hq_card hq_mod hXXbar
  unfold u AuxiliaryCoordinates.u at h
  unfold tbar_of_P tbar
  change (1 - ubar) / (1 + ubar) = t.val
  change ubar = (1 - t.val) / (1 + t.val) at h
  rw [h, sub_div' (one_add_t_ne_zero t)]
  rw [add_div' (1 - t.val) 1 (1 + t.val) (one_add_t_ne_zero t)]
  rw [div_div_div_eq]
  have h' : (1 + t.val) * 2 ≠ 0 := mul_ne_zero (one_add_t_ne_zero t) (two_ne_zero hq_card hq_mod)
  grind

lemma tbar_eq_t' (t : { t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (hXXbar :
      let P := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
      let X' := X ⟨-t.val, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
      let Xbar := Xbar s P q
      Xbar = X')
    :
    let P := (ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod).val
    let tbar_of_P := tbar s P q
    let t' := -t.val
    tbar_of_P = t' := by
  intro P tbar_of_P t'
  have t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let u' := u ⟨t', t_h⟩
  let ubar := ubar s P q
  let h : ubar = u' := ubar_eq_u' t hs_ne_zero sq_ne_pm_two hq_card hq_mod hXXbar
  unfold u' u at h
  unfold tbar_of_P tbar
  change (1 - ubar) / (1 + ubar) = t'
  change ubar = (1 - t') / (1 + t') at h
  rw [h, sub_div' (one_add_t_ne_zero ⟨t', t_h⟩)]
  rw [add_div' (1 - t') 1 (1 + t') (one_add_t_ne_zero ⟨t', t_h⟩), div_div_div_eq]
  have h' : ((1 + t') * 2) ≠ 0 :=
    mul_ne_zero (one_add_t_ne_zero ⟨t', t_h⟩) (two_ne_zero hq_card hq_mod)
  grind

@[blueprint "lemma:tbar_in_t_or_neg_t"
  (title := "$\\bar t = \\pm t$")
  (statement := /--
  For $t \in \mathbb{F}_q$, the parameter $\bar t$ reconstructed from $\varphi(t)$ in
  Theorem 3.3 satisfies $\bar t = t$ or $\bar t = -t$. This is the key step showing that
  $\varphi(t)$ has no preimages besides $t$ and $-t$.
  -/)]
lemma tbar_in_t_or_neg_t (t : F)
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let P := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod
    let t' := -t
    let tbar_of_P := tbar s P q
    tbar_of_P = t ∨ tbar_of_P = t' := by
  intro P t' tbar_of_P
  by_cases h : t ≠ 1 ∧ t ≠ -1
  · rcases (Xbar_h4 ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod) with h1 | h1
    · left
      exact tbar_eq_t ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod h1
    · right
      exact tbar_eq_t' ⟨t, h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod h1
  · have h' : t = 1 ∨ t = -1 := by
      rw [← not_ne_iff, ← not_ne_iff, ← Lean.Grind.not_and]
      exact h
    unfold tbar_of_P t'
    rw [tbar_eq_one ⟨t, h'⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod]
    grind

/-- `t'` is the `t` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def t' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let u := u' sq_ne_pm_two hq_card hq_mod P
  (1 - u) / (1 + u)

lemma t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → t ≠ 1 ∧ t ≠ -1 := by
  intro X t h1
  unfold t t'
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let u'_eq_Xbar_or_u'_eq_neg_Xbar := u'_eq_Xbar_or_u'_eq_neg_Xbar
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  change u = X ∨ u = -X at u'_eq_Xbar_or_u'_eq_neg_Xbar
  change (1 - u) / (1 + u) ≠ 1 ∧ (1 - u) / (1 + u) ≠ -1
  let one_add_u'_ne_zero := one_add_u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let u'_ne_zero := u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let two_ne_zero := two_ne_zero hq_card hq_mod
  and_intros
  · intro h2
    have h3 : 2 = 0 := by grind
    contradiction
  · intro h2
    have h3 : 2 = 0 := by grind
    contradiction

lemma one_add_t'_ne_zero (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → t + 1 ≠ 0 := by
  grind [t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one]

lemma u'_eq_one_sub_t'_div_one_add_t'
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1) :
    let X := Xbar s P.val q
    let u := u' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    X ≠ 1 → u = (1 - t) / (1 + t) := by
  intro X u t h1
  unfold t t'
  let u := u' sq_ne_pm_two hq_card hq_mod P
  let one_add_u'_ne_zero := one_add_u'_ne_zero
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one h1
  let two_ne_zero := two_ne_zero hq_card hq_mod
  grind

lemma u'_eq_u (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q
      X ≠ 1) :
    let u' := u' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let u := u ⟨t, t_h⟩
    u' = u := by
  grind [u', u, u'_eq_one_sub_t'_div_one_add_t']

lemma v'_eq_v (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P.val q;
      X ≠ 1) :
    let v' := v' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let v := v ⟨t, t_h⟩ s
    v' = v := by
  grind [v', v, u'_eq_one_sub_t'_div_one_add_t', u'_eq_u]

lemma X'_eq_X (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q;
      X ≠ 1) :
    let X' := Xbar s P q
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let X := X ⟨t, t_h⟩ s
    X' = X := by
  intro X' t t_h X
  let h1 := u'_eq_u hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h2 := v'_eq_v hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h3 := X'_eq_χ_of_v'_mul_u'
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold X'
  rw [h3, h1, h2]
  rfl

lemma Y'_eq_Y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X := Xbar s P q;
      X ≠ 1) :
    let Y' := Y' sq_ne_pm_two hq_card hq_mod P
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let Y := Y ⟨t, t_h⟩ s q
    Y' = Y := by
  intro Y' t t_h Y
  let h1 := u'_eq_u hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h2 := v'_eq_v hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h3 := Y'_observation2
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold Y'
  rw [h3, h1, h2]
  rfl

/-- `x'` is the `x` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def x' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let c := c s
  let X' := Xbar s P q
  let Y' := Y' sq_ne_pm_two hq_card hq_mod P
  (c - 1) * s * X' * (1 + X') / Y'

lemma x'_eq_x (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let x := x ⟨t, t_h⟩ s q
    let x' := x' sq_ne_pm_two hq_card hq_mod P
    x' = x := by
  intro t t_h x x'
  unfold x' ReconstructionCoordinates.x' x OutputCoordinates.x
  let hY'_eq_Y := Y'_eq_Y hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let hX'_eq_X := X'_eq_X hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

/-- `y'` is the `y` equivalent used in the proof reverse argumentation of Theorem 3 part C. -/
def y' (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q)
    (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) : F :=
  let X' := Xbar s P q
  let r := r s
  (r * X' - (1 + X') ^ 2) / (r * X' + (1 + X') ^ 2)

lemma y'_eq_y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y' := y' sq_ne_pm_two hq_card hq_mod P
    y' = y := by
  intro t t_h y y'
  unfold y' ReconstructionCoordinates.y' y OutputCoordinates.y
  let hX'_eq_X := X'_eq_X
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

theorem x'_and_y'_fulfill_curve_equation
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let x' := x' sq_ne_pm_two hq_card hq_mod P
    let y' := y' sq_ne_pm_two hq_card hq_mod P
    (curve s).Equation x' y' := by
  intro x' y'
  let t := t' sq_ne_pm_two hq_card hq_mod P
  let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let x := x ⟨t, t_h⟩ s q
  let y := y ⟨t, t_h⟩ s
  let x'_eq_x := x'_eq_x hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let y'_eq_y := y'_eq_y hs_ne_zero
    sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h := curve_equation ⟨t, t_h⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
  rw [curve_equation_iff]
  grind [x'_eq_x, y'_eq_y]

lemma y_eq_y_of_P (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y_of_P := P.val.2
    y = y_of_P := by
  intro t t_h y y_of_P
  let y_with_Xbar := y_with_Xbar hs_ne_zero hq_card hq_mod ⟨P.val, P_props⟩ y_ne_one
  unfold y_of_P
  rw [y_with_Xbar]
  unfold y OutputCoordinates.y
  let h := X'_eq_X hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  grind

lemma x_eq_x_of_P (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let x := x ⟨t, t_h⟩ s q
    let x_of_P := P.val.1
    x = x_of_P := by
  intro t t_h x x_of_P
  let Y' := Y' sq_ne_pm_two hq_card hq_mod P
  let c := c s
  let X := Xbar s P q
  let Y'_ne_zero := Y'_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one
  change x_of_P ≠ 0 at x_ne_zero
  have h1 : Y' = (c - 1) * s * X * (1 + X) / x_of_P := by grind [Y', ReconstructionCoordinates.Y']
  have h2 : x_of_P = (c - 1) * s * X * (1 + X) / Y' := by
    unfold Y' ReconstructionCoordinates.Y'
    rw [← div_left_inj' x_ne_zero, ← mul_left_inj' Y'_ne_zero]
    change x_of_P / x_of_P * Y' = (c - 1) * s * X * (1 + X) / Y' / x_of_P * Y'
    grind
  rw [h2]
  let h3 := Y'_eq_Y
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  let h4 := X'_eq_X
    hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
  unfold Y' X
  rw [h3, h4]
  rfl

lemma x_y_of_P_eq_x_y (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {p : F × F // p ∈ EOverF sq_ne_pm_two hq_card hq_mod}) (P_props : ϕOverFProps s P)
    (x_ne_zero : P.val.1 ≠ 0) (y_ne_one : P.val.2 ≠ 1)
    (hXXbar :
      let X' := Xbar s P q
      X' ≠ 1) :
    let t := t' sq_ne_pm_two hq_card hq_mod P
    let t_h := t'_ne_one_and_t'_ne_neg_one_of_Xbar_ne_one
      hs_ne_zero sq_ne_pm_two hq_card hq_mod P P_props x_ne_zero y_ne_one hXXbar
    let y := y ⟨t, t_h⟩ s
    let y_of_P := P.val.2
    let x := x ⟨t, t_h⟩ s q
    let x_of_P := P.val.1
    (x, y) = (x_of_P, y_of_P) := by
  grind [x_eq_x_of_P, y_eq_y_of_P]

end tbar

end Elligator.Elligator1.ReconstructionCoordinates
