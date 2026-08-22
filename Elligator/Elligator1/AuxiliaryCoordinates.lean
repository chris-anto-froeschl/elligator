/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.CurveParameters

/-!
# Auxiliary Coordinates

TODO

## Main Results

* TODO

## References

See [Bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Elligator.Elligator1.AuxiliaryCoordinates

variable {F : Type*} [Field F]
variable {s : F}
variable {q : ℕ}

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol
open Elligator.Elligator1.CurveParameters

section u

/-- u(t) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:u"
  (title := "The auxiliary quantity $u$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$ define
  $$
  u = (1 - t)/(1 + t) .
  $$
  -/)]
def u (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : F :=
    let t := t.val
    (1 - t) / (1 + t)

@[blueprint "lemma:u_ne_zero"
  (title := "$u \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $u = (1 - t)/(1 + t) \neq 0$ for
  $t \in \mathbb{F}_q \setminus \{\pm 1\}$, since $1 - t \neq 0$ and $1 + t \neq 0$.
  -/)]
lemma u_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : u t ≠ (0 : F) :=
  div_ne_zero (one_sub_t_ne_zero t) (one_add_t_ne_zero t)

lemma u_comparison (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let u1 := u t
    let ubar := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
    ubar = 1 / u1 := by
  intro t1 t2 u1 ubar
  calc
    ubar = (1 - t2) / (1 + t2) := by simp [ubar, u]
    _ = (1 + t) / (1 - t) := by simp [t2, t1]; ring
    _ = 1 / u1 := by simp [u1, u]

@[simp]
lemma u_of_zero :
    let u := u ⟨(0 : F), by simp⟩
    u = 1 := by
  simp [u]

lemma one_add_u_ne_zero [Fintype F] (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    1 + (u t) ≠ 0 := by
  unfold u
  rw [add_div' _ _ _ (one_add_t_ne_zero t)]
  norm_num
  constructor
  · exact two_ne_zero hq_card hq_mod
  · exact one_add_t_ne_zero t

end u

variable [Fintype F]

section v

/-- v(t, s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:v"
  (title := "The auxiliary quantity $v$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$, with $u$ and $r$ as above, define
  $$
  v = u ^ 5 + (r ^ 2 - 2)u ^ 3 + u .
  $$
  -/)]
def v (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
    let u := u t
    let r := r s
    u ^ 5 + (r ^ 2 - 2) * u ^ 3 + u

lemma v_factored (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let v := v t s
    let c := c s
    let u := u t
    v = u * (u ^ 2 + c ^ 2) * (u ^ 2 + 1 / c ^ 2) := by
  intro v c u
  let r := r s
  change u ^ 5 + (r ^ 2 - 2) * u ^ 3 + u = u * (u ^ 2 + c ^ 2) * (u ^ 2 + 1 / c ^ 2)
  have hc_sq_ne_zero : c ^ 2 ≠ 0 := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)
  grind [r_sq_sub_two_eq_c_sq_add_inv_c_sq]

lemma v_factored_second_factor_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    (u t) ^ 2 + (c s) ^ 2 ≠ 0 := by
  intro h_sum_eq_zero
  let c := c s
  let u := u t
  have h_neg_one_sq : -1 = (u / c) ^ 2 := by
    have hc_sq_ne_zero := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)
    grind
  have h_isSquare : IsSquare (-1 : F) := by
    rw [h_neg_one_sq, pow_two]
    apply IsSquare.mul_self (u / c)
  rw [FiniteField.isSquare_neg_one_iff, hq_card] at h_isSquare
  contradiction

lemma v_factored_third_factor_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    (u t) ^ 2 + 1 / (c s) ^ 2 ≠ 0 := by
  intro h_sum_eq_zero
  have h_neg_one_sq : -1 = ((u t) * (c s)) ^ 2 := by
    grind [pow_ne_zero, c_ne_zero, div_left_inj']
  have h_isSquare : IsSquare (-1 : F) := by
    rw [h_neg_one_sq, pow_two]
    apply IsSquare.mul_self
  rw [FiniteField.isSquare_neg_one_iff, hq_card] at h_isSquare
  contradiction

@[blueprint "lemma:v_ne_zero"
  (title := "$v \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $v \neq 0$.
  -/)]
lemma v_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    v t s ≠ 0 := by
  rw [v_factored hs_ne_zero hq_card hq_mod t]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply u_ne_zero t
    · exact (v_factored_second_factor_ne_zero hs_ne_zero hq_card hq_mod t)
  · exact (v_factored_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)

lemma χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero [DecidableEq F]
    (t : { t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let v := v t s
    ((χ v) * v) ^ ((q + 1) / 4) ≠ 0 := by
  intro v
  rw [mul_pow (χ v) v ((q + 1) / 4)]
  apply mul_ne_zero
  · apply pow_ne_zero ((q + 1) / 4) (χ_a_ne_zero (v_ne_zero hs_ne_zero hq_card hq_mod t))
  · apply pow_ne_zero ((q + 1) / 4) (v_ne_zero hs_ne_zero hq_card hq_mod t)

-- TODO move comparisons out
omit [Fintype F] in
lemma v_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let u1 := u t
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    let r := r s
    v2 = 1 / u1 ^ 5 + (r ^ 2 - 2) * 1 / u1 ^ 3 + 1 / u1 := by
  intro t1 t2 u1 v2 r_of_s
  let ubar := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
  calc
    v2 = ubar ^ 5 + (r_of_s ^ 2 - 2) * ubar ^ 3 + ubar := by rfl
    _ = 1 / u1 ^ 5 + (r_of_s ^ 2 - 2) * 1/ u1 ^ 3 + 1 / u1 := by
      unfold ubar u1 t2 t1
      rw [u_comparison t]
      ring_nf

omit [Fintype F] in
lemma v_comparison_implication1 (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let u1 := u t
    let v1 := v t s
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    v2 * u1 ^ 6 = v1 := by
  intro t1 t2 u1 v1 v2
  let r := r s
  calc
    v2 * u1 ^ 6 = u1 + (r ^ 2 - 2) * u1 ^ 3 + u1 ^ 5 := by
      unfold v2
      rw [v_comparison t]
      grind
    _ = v1 := by grind [v]

omit [Fintype F] in
lemma v_comparison_implication2 (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let u1 := u t
    let v1 := v t s
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    v2 = v1 / u1 ^ 6 := by
  intro t1 t2 u1 v1 v2
  have hu1_pow6_ne_zero : u1 ^ 6 ≠ 0 := pow_ne_zero 6 (u_ne_zero t)
  rw [← mul_right_inj' hu1_pow6_ne_zero]
  unfold v1
  rw [← v_comparison_implication1 t]
  grind

lemma v_comparison_implication3 [DecidableEq F]
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    χ ((u t) ^ 6) = 1 := by
  let u := u t
  have h : u ^ 6 = u ^ 2 * u ^ 2 * u ^ 2 := by ring
  rw [h, χ_mul, χ_mul, χ_sq (u_ne_zero t)]
  rw [mul_one, mul_one]

lemma v_comparison_implication4 [DecidableEq F]
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let v1 := v t s
    let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    χ v2 = χ v1 := by
  intro t1 t2 v1 v2
  let u := u t
  unfold v1
  rw [← v_comparison_implication1 t]
  change χ v2= χ (v2 * u ^ 6)
  rw [χ_mul, v_comparison_implication3 t, mul_one]

omit [Fintype F] in
@[simp]
lemma v_of_zero :
    let v := v ⟨(0 : F), by simp⟩ s
    v = (r s) ^ 2 := by
  intro v_of_t
  unfold v_of_t v
  rw [u_of_zero]
  ring

lemma χ_IsSquare_h1 [DecidableEq F]
    (t : { t : F // t ≠ 1 ∧ t ≠ -1})
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

end v

variable [DecidableEq F]

section X

/-- X(t, s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:X"
  (title := "The auxiliary coordinate $X$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$, with $u$ and $v$ as above and $\chi$ the
  quadratic character of $\mathbb{F}_q$, define
  $$
  X = \chi(v) u .
  $$
  -/)]
def X (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
    let u := u t
    let v := v t s
    (χ v) * u

lemma X_pow_two_add_one_div_c_pow_two_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    (X t s) ^ 2 + 1 / (c s) ^ 2 ≠ 0 := by
  let X := X t s
  let c := c s
  intro h_sum_eq_zero
  have h_cleared : X ^ 2 * c ^ 2 + c⁻¹^2 * c ^ 2 = 0 := by grind
  have h_prod_eq_neg_one : X ^ 2 * c ^ 2 = -1 := by grind [c_ne_zero]
  have h_not_isSquare : ¬IsSquare (-1 : F) := neg_one_non_square hq_card hq_mod
  have h_isSquare : IsSquare (-1 : F) := by
    rw [← h_prod_eq_neg_one, ← mul_pow]
    apply IsSquare.sq (X * c)
  contradiction

@[blueprint "lemma:X_ne_zero"
  (title := "$X \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $X = \chi(v)u \neq 0$, since $u \neq 0$ and
  $\chi(v) \neq 0$.
  -/)]
lemma X_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    (X t s) ≠ 0 := by
  apply mul_ne_zero
  · apply χ_a_ne_zero (v_ne_zero hs_ne_zero hq_card hq_mod t)
  · apply u_ne_zero t

lemma X_comparison (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Xbar := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    Xbar = 1 / X1 := by
  intro t1 t2 X1 Xbar
  let u1 := u t
  let ubar := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  calc
    Xbar = (χ v2) * ubar := by rfl
    _ = (χ v1) / u1 := by
      unfold v2 t2
      rw [v_comparison_implication4 t]
      unfold ubar
      rw [u_comparison t]
      change (χ v1) * (1 / u1) = (χ v1) / u1
      ring
    _ = 1 / ((χ v1) * u1) := by
      nth_rw 1 [one_div_χ_of_a_eq_χ_a]
      ring
    _ = 1 / X1 := by rfl

@[simp]
lemma X_of_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let X := X ⟨(0 : F), by simp⟩ s
    X = 1 := by
  intro X
  unfold X AuxiliaryCoordinates.X
  let χ_of_v := χ (v ⟨(0 : F), by simp⟩ s)
  rw [u_of_zero]
  change χ_of_v * 1 = 1
  unfold χ_of_v
  rw [v_of_zero]
  rw [χ_sq (r_ne_zero hs_ne_zero hq_card hq_mod), mul_one]

end X

section Y

/-- Y(t, s) is a function defined in the paper.

`q` is still unrelated to the cardinality F here by intention. The theorems using
`Y` will build the necessary context to show useful properties of `Y` by creating
the relation of Field cardinality and `q`.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:Y"
  (title := "The auxiliary coordinate $Y$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$, with $u$, $v$ and $c$ as above, define
  $$
  Y = (\chi(v)v)^{(q+1)/4} \chi(v) \chi(u ^ 2 + 1/c ^ 2) .
  $$
  -/)]
def Y (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) (q : ℕ) : F :=
    let u := u t
    let c := c s
    let v := v t s
    ((χ v) * v) ^ ((q + 1) / 4) * (χ v) * χ (u ^ 2 + 1 / c ^ 2)

lemma Y_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let Y := Y t s q
    Y ≠ 0 := by
  let u := u t
  let v := v t s
  let χ_of_sum := χ (u ^ 2 + 1 / (c s) ^ 2)
  intro Y
  change ((χ v) * v) ^ ((q + 1) / 4) * (χ v) * χ_of_sum ≠ 0
  have hv_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
  apply mul_ne_zero
  · apply mul_ne_zero
    · rw [mul_pow (χ v) v ((q + 1) / 4)]
      apply mul_ne_zero
      · apply pow_ne_zero (((q + 1) / 4) : ℕ)
        apply χ_a_ne_zero hv_ne_zero
      · apply pow_ne_zero (((q + 1) / 4) : ℕ)
        apply hv_ne_zero
    · apply χ_a_ne_zero hv_ne_zero
  · apply χ_a_ne_zero (v_factored_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)

@[blueprint "lemma:X_mul_Y_ne_zero"
  (title := "$XY \\neq 0$, so $x$ is defined")
  (statement := /--
  In the situation of Theorem 1, $XY \neq 0$; in particular $Y \neq 0$, so
  $x = (c - 1)sX(1 + X)/Y$ is defined.
  -/)]
lemma X_mul_Y_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let X := X t s
    let Y := Y t s q
    X * Y ≠ 0 := by
  apply mul_ne_zero
  · apply X_ne_zero hs_ne_zero hq_card hq_mod t
  · apply Y_ne_zero hs_ne_zero hq_card hq_mod t

@[blueprint "lemma:one_add_X_ne_zero"
  (title := "$1 + X \\neq 0$, so $x \\neq 0$")
  (statement := /--
  In the situation of Theorem 1, $1 + X \neq 0$: if $X = -1$ then $u = -\chi(v)$, so
  $v = -\chi(v)r ^ 2$ and hence $\chi(v) = -\chi(v)$, a contradiction.
  -/)]
lemma one_add_X_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let X := X t s
    (1 + X) ≠ (0 : F) := by
  let u := u t
  let v := v t s
  let r := r s
  have hv_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
  intro X
  change 1 + (χ v) * u ≠ 0
  intro h_contra
  have h_chi_v_mul_u_eq_neg_one : (χ v) * u = -1 := by grind
  have h_u_eq_neg_chi_v : u = -(χ v) := by grind [one_div_χ_of_a_eq_χ_a]
  have h_v_eq_expand : v = -(χ v) * (1 + r ^ 2 - 2 + 1) := by
    change u ^ 5 + (r ^ 2 - 2) * u ^ 3 + u = -(χ v) * (1 + r ^ 2 - 2 + 1)
    repeat rw [h_u_eq_neg_chi_v]
    rw [← neg_one_mul, mul_pow, mul_pow]
    grind [χ_of_a_pow_n_eq_χ_a]
  have h_v_eq_neg_chi_v_mul_r_sq : v = -(χ v) * r ^ 2 := by grind
  have h_chi_v_eq_neg_chi_v : (χ v) = -(χ v) := by
    rw [h_u_eq_neg_chi_v] at h_chi_v_mul_u_eq_neg_one
    change (χ v) * -(χ v) = -1 at h_chi_v_mul_u_eq_neg_one
    nth_rw 1 [h_v_eq_neg_chi_v_mul_r_sq] at h_chi_v_mul_u_eq_neg_one
    rw [χ_mul] at h_chi_v_mul_u_eq_neg_one
    nth_rw 1 [← neg_one_mul] at h_chi_v_mul_u_eq_neg_one
    rw [χ_mul, χ_neg_one hq_card hq_mod] at h_chi_v_mul_u_eq_neg_one
    rw [χ_χ_eq_χ hq_card hq_mod] at h_chi_v_mul_u_eq_neg_one
    have hr_sq_ne_zero : r ^ 2 ≠ 0 := pow_ne_zero 2 (r_ne_zero hs_ne_zero hq_card hq_mod)
    have hr_sq_isSquare : IsSquare (r ^ 2) := IsSquare.sq r
    grind [χ_a_eq_one]
  have h_chi_v_ne_neg_chi_v : (χ v) ≠ -(χ v) := neg_χ_a_ne_χ_a hv_ne_zero hq_card hq_mod
  contradiction

lemma Y_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Y1 := Y t s q
    let Y2 := Y ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s q
    Y2 = Y1 / X1 ^ 3 := by
  intro t1 t2 X1 Y1 Y2
  let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
  let c := c s
  let r := r s
  let u1 := u t
  let ubar := u ⟨t2, t_h⟩
  let v1 := v t s
  let v2 := v ⟨t2, t_h⟩ s
  have hu1_ne_zero := u_ne_zero (t := t)
  have first_factor :
    ((χ v2) * v2) ^ ((q + 1) / 4) = ((χ v1) * v1) ^ ((q + 1) / 4) * (χ u1) / u1 ^ 3 := by
      have h_v2_mul_v2_eq_v1_mul_v1_div_u1_pow6 : (χ v2) * v2 = (χ v1) * v1 / u1 ^ 6 := by
        rw [v_comparison_implication4 t]
        unfold v2
        rw [v_comparison_implication2 t]
        change (χ v1) * (v1 / u1 ^ 6) = (χ v1) * v1 / u1 ^ 6
        rw [← mul_div_assoc]
      have h_chi_u1_mul_u1_cubed_isSquare : IsSquare ((χ u1) * u1 ^ 3) := by
        have h_chi_u1_mul_u1_cubed_ne_zero : (χ u1) * u1 ^ 3 ≠ 0 := by
          apply mul_ne_zero
          · apply χ_a_ne_zero hu1_ne_zero
          · apply pow_ne_zero 3 hu1_ne_zero
        apply (χ_eq_one_iff_isSquare h_chi_u1_mul_u1_cubed_ne_zero hq_card hq_mod).mp
        have h_three_eq_one_add_two : (3 : ℕ) = 1 + 2 := by norm_num
        rw [h_three_eq_one_add_two, pow_add u1 1 2, ← mul_assoc, pow_one]
        rw [χ_mul, χ_mul]
        rw [χ_χ_eq_χ hq_card hq_mod]
        rw [← χ_mul, ← pow_two]
        have h_u1_sq_isSquare : IsSquare (u1 ^ 2) := IsSquare.sq u1
        have h_chi_u1_sq_eq_one : χ (u1 ^ 2) = 1 := by
          apply (χ_eq_one_iff_isSquare (pow_ne_zero 2 hu1_ne_zero) hq_card hq_mod).mpr
          exact h_u1_sq_isSquare
        simp [h_chi_u1_sq_eq_one]
      have h_u1_pow6_pow_eq_chi_u1_mul_u1_cubed : (u1 ^ 6) ^ ((q + 1) / 4) = (χ u1) * u1 ^ 3 := by
        have h_six_eq_three_mul_two : 6 = 3 * 2 := by norm_num
        rw [h_six_eq_three_mul_two, ← pow_mul, mul_assoc, mul_comm, pow_mul, mul_comm]
        rw [add_comm, one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
        rw [add_comm, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_card hq_mod]
        change ((χ u1) * u1) ^ 3 = (χ u1) * u1 ^ 3
        rw [mul_pow, χ_of_a_pow_n_eq_χ_a u1 ⟨3, by trivial⟩]
      calc
        ((χ v2) * v2) ^ ((q + 1) / 4) = ((χ v1) * v1 / u1 ^ 6) ^ ((q + 1) / 4) := by
          rw [h_v2_mul_v2_eq_v1_mul_v1_div_u1_pow6]
        _ = ((χ v1) * v1) ^ ((q + 1) / 4) * (χ u1) / u1 ^ 3 := by
          rw [div_pow, h_u1_pow6_pow_eq_chi_u1_mul_u1_cubed]
          nth_rw 2 [one_div_χ_of_a_eq_χ_a]
          grind
  have second_factor : (χ v2) = (χ v1) := v_comparison_implication4 t
  have third_factor : χ (ubar ^ 2 + 1 / c ^ 2) = χ (u1 * v1 * (u1 ^ 2 + 1 / c ^ 2)) := by
    calc
      χ (ubar ^ 2 + 1 / c ^ 2)
        = χ ((c ^ 2 * u1 ^ 4 * (ubar ^ 2 + 1 / c ^ 2)) * (u1 ^ 2 + 1 / c ^ 2) ^ 2) := by
        rw [← χ_of_a_eq_χ_a_mul_b_pow_two (c_ne_zero hs_ne_zero hq_card hq_mod)]
        rw [mul_comm, ← χ_of_a_eq_χ_a_mul_b_pow_two (pow_ne_zero 2 hu1_ne_zero)]
        rw [χ_of_a_eq_χ_a_mul_b_pow_two
          (v_factored_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)]
        grind
      _ = χ ((u1 ^ 2 * (c ^ 2 + u1 ^ 2)) * (u1 ^ 2 + 1 / c ^ 2) ^ 2) := by
        rw [pow_two ubar]
        unfold ubar
        rw [u_comparison t]
        change χ (c ^ 2 * u1 ^ 4 * (1 / u1 * (1 / u1) + 1 / c ^ 2) * (u1 ^ 2 + 1 / c ^ 2) ^ 2)
          = χ (u1 ^ 2 * (c ^ 2 + u1 ^ 2) * (u1 ^ 2 + 1 / c ^ 2) ^ 2)
        have h_clear_denominators :
            c ^ 2 * u1 ^ 4 * (1 / u1 * (1 / u1) + 1 / c ^ 2) = u1 ^ 2 * (c ^ 2 + u1 ^ 2) := by
          have hc_sq_ne_zero : c ^ 2 ≠ 0 := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)
          grind
        rw [h_clear_denominators]
      _ = χ (u1 * v1 * (u1 ^ 2 + 1 / c ^ 2)) := by grind [v_factored]
  calc
    Y2 = Y1 * (χ u1) * χ (u1 * v1) / u1 ^ 3 := by
      unfold Y2 Y
      change ((χ v2) * v2) ^ ((q + 1) / 4) * (χ v2) * χ (ubar ^ 2 + 1 / c ^ 2)
        = Y1 * (χ u1) * χ (u1 * v1) / u1 ^ 3
      rw [first_factor, second_factor, third_factor, χ_mul]
      have h_rearrange :
        ((χ v1) * v1) ^ ((q + 1) / 4) * (χ u1) / u1 ^ 3 * (χ v1)
        * (χ (u1 * v1) * (χ (u1 ^ 2 + 1 / c ^ 2)))
        = ((χ v1) * v1) ^ ((q + 1) / 4) * (χ v1) * (χ (u1 ^ 2 + 1 / c ^ 2))
          * (χ u1) * χ (u1 * v1) / u1 ^ 3 := by ring_nf
      rw [h_rearrange]
      rfl
    _ = Y1 / ((χ v1) * u1) ^ 3 := by
      calc
      Y1 * (χ u1) * χ (u1 * v1) / u1 ^ 3 = Y1 * (χ v1) / u1 ^ 3 := by
        rw [χ_mul, ← mul_assoc, mul_assoc Y1, ← χ_mul, ← pow_two, χ_sq hu1_ne_zero, mul_one]
      _ = Y1 / ((χ v1) * u1) ^ (2 + 1) := by
        nth_rw 1 [one_div_χ_of_a_eq_χ_a]
        rw [mul_div_assoc, div_div]
        nth_rw 1 [← χ_of_a_pow_n_eq_χ_a v1 ⟨3, by trivial⟩, ← mul_pow]
        ring_nf
    _ = Y1 / X1 ^ 3 := by rfl

end Y

end Elligator.Elligator1.AuxiliaryCoordinates
