/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map
public import Elligator.Elligator1.ReconstructionCoordinates
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# ϕ_over_F Characterization

TODO

## Main Results

* TODO

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.PhiOverFCharacterization

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates
open Elligator.Elligator1.ReconstructionCoordinates

/-- `ϕOverFProp1` is the first property fulfilled by Ps in `EOverF s`.
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

/-- `ϕOverFProp2` is the second property fulfilled by Ps in `EOverF s`.

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

/-- `ϕOverFProp3` is the third property fulfilled by Ps in `EOverF s`.

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
in `EOverF s`, i.e. `ϕOverFProp1`, `ϕOverFProp2` and `ϕOverFProp3`.

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
  have h1 : X ^ 2 + 2 * (1 + η * r) * X + 1 = 0 := X_quadratic_eq_of_η t hs_ne_zero sq_ne_pm_two hq_card hq_mod
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
  have h : X + 1 / X = -2 * (1 + η * r) := X_add_inv_X_eq_neg_two_mul_one_add_η_mul_r t hs_ne_zero sq_ne_pm_two hq_card hq_mod
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

end Elligator.Elligator1.PhiOverFCharacterization
