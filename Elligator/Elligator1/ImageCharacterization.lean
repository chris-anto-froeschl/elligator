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
# Reconstruction Coordinates

TODO

## Main Results

* TODO

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.ImageCharacterization

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters
open Elligator.Elligator1.AuxiliaryCoordinates
open Elligator.Elligator1.OutputCoordinates
open Elligator.Elligator1.ReconstructionCoordinates

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

lemma Xbar_ne_one_and_Xbar_ne_neg_one_of_Xbar_ne_one
    (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (P : {P : F × F // ϕOverFProps s P})
    (y_ne_one : P.val.2 ≠ 1) :
    let Xbar := Xbar s P q
    Xbar ≠ 1 → Xbar ≠ 1 ∧ Xbar ≠ -1 :=
  by grind [Xbar_ne_neg_one]

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

end Elligator.Elligator1.ImageCharacterization
