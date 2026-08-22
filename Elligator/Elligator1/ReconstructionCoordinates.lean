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

lemma ϕ_of_t_eq_zero_one (t : { n : F // n = 1 ∨ n = -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let ϕ := ϕ t.val hs_ne_zero sq_ne_pm_two hq_card hq_mod
    ϕ.val = (0, 1) := by
  intro ϕ
  unfold ϕ Elligator1.ϕ
  rcases t.prop with h | h <;> simp [h]

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

end η

section XηRelation

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

end XηRelation

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

end tbar

end Elligator.Elligator1.ReconstructionCoordinates
