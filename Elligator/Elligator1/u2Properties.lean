import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties
import Elligator.Elligator1.dProperties
import Elligator.Elligator1.uProperties
import Elligator.Elligator1.vProperties
import Elligator.Elligator1.XProperties
import Elligator.Elligator1.YProperties
import Elligator.Elligator1.xProperties
import Elligator.Elligator1.yProperties
import Elligator.Elligator1.etaProperties
import Elligator.Elligator1.X2Properties
import Elligator.Elligator1.zProperties

namespace Elligator.Elligator1

section u2Properties

variable {F : Type*} [Field F] [Fintype F]

lemma u2_eq_zero
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u2_of_point = 0 := by
    intro point u2_of_point
    unfold u2_of_point u2
    rw [z_eq_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma u2_eq_u
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (X_h :
    let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    X2_of_t = X_of_t
  )
  :
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u2_of_t = u_of_t := by
    intro point u_of_t u2_of_t
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X'_of_t := X ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_Y := LegendreSymbol.χ Y_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold u2_of_t u2
    rw [X_h]
    change z_of_point * X_of_t = u_of_t
    have h1 : (c_of_s - 1) * s * X2_of_t * (1 + X2_of_t) = x_of_t * Y_of_t := by
      unfold X2_of_t
      rw [X_h]
      rw [← div_left_inj' (Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      change x_of_t = x_of_t * Y_of_t / Y_of_t
      rw [mul_div_assoc, div_self (Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      ring_nf
    have h2 : z_of_point = χ_of_Y * (LegendreSymbol.χ (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      calc
        z_of_point = (LegendreSymbol.χ (x_of_t^2 * Y_of_t * (X_of_t^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
          unfold z_of_point z
          change LegendreSymbol.χ ((c_of_s - 1) * s * X2_of_t * (1 + X2_of_t) * point.1 * (X2_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (x_of_t ^ 2 * Y_of_t * (X_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          unfold point ϕ
          simp only [h1]
          rw [dif_pos t.prop]
          change LegendreSymbol.χ (x_of_t * Y_of_t * x_of_t * (X2_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (x_of_t ^ 2 * Y_of_t * (X_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          unfold X2_of_t X_of_t
          rw [X_h]
          ring_nf
        _ = χ_of_Y * (LegendreSymbol.χ (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
          rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (x_of_t^2 * Y_of_t) (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (x_of_t^2)  Y_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_a_eq_one (x_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)) (IsSquare.sq x_of_t) q field_cardinality q_prime_power q_mod_4_congruent_3]
          unfold χ_of_Y
          ring_nf
    have h3 : (LegendreSymbol.χ (u_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) = (LegendreSymbol.χ (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      unfold X_of_t X
      rw [mul_pow]
      nth_rw 3 [pow_two]
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v_of_t v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [← pow_two, LegendreSymbol.χ_a_eq_one (v_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)) (IsSquare.sq v_of_t) q field_cardinality q_prime_power q_mod_4_congruent_3]
      unfold u_of_t
      simp_all
    have h4 : χ_of_Y = χ_of_v * (LegendreSymbol.χ (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      rw [← h3]
      unfold χ_of_Y Y_of_t Y
      let χ_sum := LegendreSymbol.χ (u_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3;
      change (LegendreSymbol.χ ((χ_of_v * v_of_t)^((q + 1) / 4) * χ_of_v * χ_sum) q field_cardinality q_prime_power q_mod_4_congruent_3) = χ_of_v * χ_sum
      rw [mul_assoc, LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b ((χ_of_v * v_of_t)^((q + 1) / 4)) (χ_of_v * χ_sum) q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_a_eq_one ((χ_of_v * v_of_t)^((q + 1) / 4)) (χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) (χ_IsSquare_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b χ_of_v χ_sum q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a (u_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3]
      unfold χ_of_v χ_sum
      simp_all
    have h5 : z_of_point = χ_of_v := by
      rw [h2, h4, mul_assoc]
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (X_of_t^2 + 1 / c_of_s^2) (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
      rw [LegendreSymbol.χ_a_eq_one ((X_of_t^2 + 1 / c_of_s^2)^2) (FiniteFieldBasic.pow_two_ne_zero (X_pow_two_add_one_over_c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)) (IsSquare.sq (X_of_t^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3]
      simp
    rw [h5]
    unfold X_of_t X
    change χ_of_v * (χ_of_v * u_of_t ) = u_of_t
    rw [← mul_assoc, ← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v_of_t v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
    have h6 : IsSquare (v_of_t^2) := by exact IsSquare.sq v_of_t
    rw [LegendreSymbol.χ_a_eq_one (v_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)) h6 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma u2_eq_u'
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (X_h :
    let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let X'_of_t := X ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    X2_of_t = X'_of_t
  )
  :
  have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let u'_of_t := u ⟨-t.val, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u2_of_t = u'_of_t := by
    intro h2_2 point u'_of_t u2_of_t
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X'_of_t := X ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let x'_of_t := x ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let Y'_of_t := Y ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let v'_of_t := v ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v' := LegendreSymbol.χ v'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_Y := LegendreSymbol.χ Y_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_Y' := LegendreSymbol.χ Y'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold u2_of_t u2
    rw [X_h]
    change z_of_point * X'_of_t = u'_of_t
    have h1 : (c_of_s - 1) * s * X2_of_t * (1 + X2_of_t) = x'_of_t * Y'_of_t := by
      unfold X2_of_t
      rw [X_h]
      rw [← div_left_inj' (Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t.val, h2_2⟩)]
      change x'_of_t = x'_of_t * Y'_of_t / Y'_of_t
      rw [mul_div_assoc, div_self (Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t.val, h2_2⟩)]
      ring_nf
    have h2 : z_of_point = χ_of_Y' * (LegendreSymbol.χ (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      calc
        z_of_point = (LegendreSymbol.χ (x'_of_t^2 * Y'_of_t * (X'_of_t^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
          unfold z_of_point z
          change LegendreSymbol.χ ((c_of_s - 1) * s * X2_of_t * (1 + X2_of_t) * point.1 * (X2_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (x'_of_t ^ 2 * Y'_of_t * (X'_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          unfold point ϕ
          simp only [h1]
          rw [dif_pos t.prop]
          change LegendreSymbol.χ (x'_of_t * Y'_of_t * x_of_t * (X2_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (x'_of_t ^ 2 * Y'_of_t * (X'_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          unfold X2_of_t X'_of_t x'_of_t x_of_t
          rw [x_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [X_h]
          ring_nf
        _ = χ_of_Y' * (LegendreSymbol.χ (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
          rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (x'_of_t^2 * Y'_of_t) (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (x'_of_t^2) Y'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_a_eq_one (x'_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t, h2_2⟩)) (IsSquare.sq x'_of_t) q field_cardinality q_prime_power q_mod_4_congruent_3]
          unfold χ_of_Y'
          ring_nf
    have h3 : (LegendreSymbol.χ (u'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) = (LegendreSymbol.χ (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      unfold X'_of_t X
      rw [mul_pow]
      nth_rw 3 [pow_two]
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v'_of_t v'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [← pow_two, LegendreSymbol.χ_a_eq_one (v'_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t, h2_2⟩)) (IsSquare.sq v'_of_t) q field_cardinality q_prime_power q_mod_4_congruent_3]
      unfold u'_of_t
      simp_all
    have h4 : χ_of_Y' = χ_of_v' * (LegendreSymbol.χ (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      rw [← h3]
      unfold χ_of_Y' Y'_of_t Y
      let χ_sum := LegendreSymbol.χ (u'_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3;
      change (LegendreSymbol.χ ((χ_of_v' * v'_of_t)^((q + 1) / 4) * χ_of_v' * χ_sum) q field_cardinality q_prime_power q_mod_4_congruent_3) = χ_of_v' * χ_sum
      rw [mul_assoc, LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b ((χ_of_v' * v'_of_t)^((q + 1) / 4)) (χ_of_v' * χ_sum) q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_a_eq_one ((χ_of_v' * v'_of_t)^((q + 1) / 4)) (χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) (χ_IsSquare_h1 ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b χ_of_v' χ_sum q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a v'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a (u'_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3]
      unfold χ_of_v' χ_sum
      simp_all
    have h5 : z_of_point = χ_of_v' := by
      rw [h2, h4, mul_assoc]
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (X'_of_t^2 + 1 / c_of_s^2) (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
      rw [LegendreSymbol.χ_a_eq_one ((X'_of_t^2 + 1 / c_of_s^2)^2) (FiniteFieldBasic.pow_two_ne_zero (X_pow_two_add_one_over_c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t.val, h2_2⟩)) (IsSquare.sq (X'_of_t^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3]
      simp
    rw [h5]
    unfold X'_of_t X
    change χ_of_v' * (χ_of_v' * u'_of_t ) = u'_of_t
    rw [← mul_assoc, ← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v'_of_t v'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
    have h6 : IsSquare (v'_of_t^2) := by exact IsSquare.sq v'_of_t
    rw [LegendreSymbol.χ_a_eq_one (v'_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t.val, h2_2⟩)) h6 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma u2_h1
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let u'_of_t := u ⟨-t.val, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u2_of_t = u_of_t ∨ u2_of_t = u'_of_t := by
    intro point u_of_t h2_2 u'_of_t u2_of_t
    rcases (X2_h4 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) with h | h
    · left
      exact u2_eq_u t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h
    · right
      exact u2_eq_u' t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h


/-- The key step: rewriting `1 + u2(ϕ(t))` in the main case (t ≠ ±1) to show it is nonzero,
    using `u2_h1` which gives `u2 = u(t)` or `u2 = u(-t)`. -/
lemma one_add_u2_ne_zero_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  {s : F}
  (s_h1 : (s : F) ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  {q : ℕ}
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let P := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).1
  let u2 := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P
  1 + u2 ≠ 0 := by
    intro P u2
    unfold u2
    obtain h|h := u2_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · rw [h]
      exact one_add_u_ne_zero t field_cardinality q_prime_power q_mod_4_congruent_3
    · rw [h]
      let t_h := FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
      exact one_add_u_ne_zero ⟨ -t.val, t_h ⟩ field_cardinality q_prime_power q_mod_4_congruent_3

lemma one_add_u2_ne_zero_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  {s : F}
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  {q : ℕ}
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let P := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).1
  let u2 := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P
  1 + u2 ≠ 0 := by
    intro P u2
    unfold u2
    rw [u2_eq_zero, add_zero]
    exact FiniteFieldBasic.one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3

lemma one_add_u2_ne_zero
  {s : F}
  (s_h1 : (s : F) ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  {q : ℕ}
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  (1 + u2_of_point) ≠ 0 := by
    intro u2_of_point
    let point_prop := point.prop
    unfold ϕ_over_F at point_prop
    rw [Set.mem_setOf_eq] at point_prop
    obtain ⟨t, ht⟩ := point_prop
    by_cases h : t ≠ 1 ∧ t ≠ -1
    · let h2 := one_add_u2_ne_zero_main_case ⟨t, h⟩ s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
      grind
    · have h2 : t = 1 ∨ t = -1 := by
        push_neg at h
        grind
      have h3 := one_add_u2_ne_zero_base_case ⟨t, h2⟩ s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
      grind

-- Theorem 3 part C define
noncomputable def u'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  : F :=
  let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  z * X

lemma u'_pow_two_eq_X_pow_two
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u^2 = X^2 := by
    intro u X
    let z'_eq_one_or_z'_eq_neg_one := z'_eq_one_or_z'_eq_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    unfold u u'
    grind

lemma u'_eq_X2_or_u'_eq_neg_X2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u = X ∨ u = -X := by
    intro u X
    let z'_eq_one_or_z'_eq_neg_one := z'_eq_one_or_z'_eq_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    unfold u u'
    grind

lemma u'_ne_neg_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X ≠ 1 → u ≠ -1 := by
    intro u X h1
    let z'_eq_one_or_z'_eq_neg_one := z'_eq_one_or_z'_eq_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one := X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_ne_one
    unfold u u'
    grind

lemma one_add_u'_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X ≠ 1 → 1 + u ≠ 0 := by
    intro u X h1
    let z'_eq_one_or_z'_eq_neg_one := z'_eq_one_or_z'_eq_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one := X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_ne_one
    unfold u u'
    grind

lemma u'_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X ≠ 1 → u ≠ 0 := by
    intro u X h1
    let z'_eq_one_or_z'_eq_neg_one := z'_eq_one_or_z'_eq_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let z_ne_zero := z'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let X2_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one := X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_ne_one
    unfold u u'
    grind

-- Theorem 3 part C define
noncomputable def v'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  : F :=
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let r := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  -- Note: this is just the definition of v as in theorem 1
  u^5 + (r^2 - 2) * u^3 + u

lemma v'_eq_z'_mul_Y'_pow_two
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X ≠ 1 → v = z * Y^2 := by
    intro z Y v X h1
    let r := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one := X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_ne_one
    let Y'_pow_two_eq_of_X2_ne_one := Y'_pow_two_eq_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props y_ne_one
    let z_pow_three_eq_z := LegendreSymbol.χ_of_a_pow_n_eq_χ_a (Y * (X^2 + 1 / c^2)) ⟨3, by grind⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    change z^3 = z at z_pow_three_eq_z
    let z_pow_five_eq_z := LegendreSymbol.χ_of_a_pow_n_eq_χ_a (Y * (X^2 + 1 / c^2)) ⟨5, by grind⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    change z^5 = z at z_pow_five_eq_z
    let x := point.val.1
    have h2 : v = z * (X^5 + (r^2 - 2) * X^3 + X) := by
      change (z * X)^5 + (r^2 - 2) * (z * X)^3 + (z * X) = z * (X^5 + (r^2 - 2) * X^3 + X)
      repeat rw [mul_pow]
      rw [z_pow_three_eq_z, z_pow_five_eq_z]
      grind
    grind

lemma v'_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  X ≠ 1 → v ≠ 0 := by
    intro X v h1
    let v'_eq_z'_mul_Y'_pow_two := v'_eq_z'_mul_Y'_pow_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    have h2 : v = z * Y^2 := by grind
    rw [h2]
    let h3 := Y'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z_ne_zero := z'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    grind

lemma χ_of_v'_eq_χ_of_z'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_v := LegendreSymbol.χ v q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_z := LegendreSymbol.χ z q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → χ_of_v = χ_of_z := by
    intro X z v χ_of_v χ_of_z h1
    let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let v'_eq_z'_mul_Y'_pow_two := v'_eq_z'_mul_Y'_pow_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    unfold χ_of_v v
    rw [v'_eq_z'_mul_Y'_pow_two]
    let h2 := Y'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    rw [← LegendreSymbol.χ_of_a_eq_χ_a_mul_b_pow_two z h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    grind

lemma χ_of_z'_eq_z'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_z := LegendreSymbol.χ z q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → χ_of_z = z := by
    intro X z χ_of_z h1
    let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let v'_eq_z'_mul_Y'_pow_two := v'_eq_z'_mul_Y'_pow_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    exact LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a (Y * (X^2 + 1 / c^2)) q field_cardinality q_prime_power q_mod_4_congruent_3

lemma χ_of_v'_eq_z'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_v := LegendreSymbol.χ v q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → χ_of_v = z := by
    intro X v z χ_of_z h1
    let χ_of_v'_eq_χ_of_z' := χ_of_v'_eq_χ_of_z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let χ_of_z'_eq_z' := χ_of_z'_eq_z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    grind

lemma X'_eq_χ_of_v'_mul_u'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_v := LegendreSymbol.χ v q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → X = χ_of_v * u := by
    intro X v u χ_of_v h1
    let χ_of_v'_eq_z' := χ_of_v'_eq_z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    unfold χ_of_v v
    rw [χ_of_v'_eq_z' h1]
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let z_ne_zero := z'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    rw [mul_comm, ← div_left_inj' z_ne_zero]
    rw [mul_div_assoc, div_self z_ne_zero]
    change X / z = z * X * 1
    let z'_argument_ne_zero := z'_argument_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let a := (Y * (X^2 + 1 / c^2))
    nth_rw 1 [← mul_one X]
    unfold z z'
    rw [mul_div_assoc, LegendreSymbol.one_over_χ_of_a_eq_χ_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    grind

lemma Y'_pow_two_eq_χ_of_v'_mul_v'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_v := LegendreSymbol.χ v q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → Y^2 = χ_of_v * v := by
    intro X Y v χ_of_v h1
    let v'_eq_z'_mul_Y'_pow_two := v'_eq_z'_mul_Y'_pow_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    have h2 : v = z * Y^2 := by grind
    let z_ne_zero := z'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    rw [mul_comm, ← div_left_inj' z_ne_zero] at h2
    rw [mul_div_assoc, div_self z_ne_zero, mul_one] at h2
    change v / z = Y^2 at h2
    let z'_argument_ne_zero := z'_argument_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let r := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let a := u^5 + (r^2 - 2) * u^3 + u
    rw [← h2, mul_comm]
    unfold χ_of_v v v'
    rw [← LegendreSymbol.one_over_χ_of_a_eq_χ_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    change v / z = v * (1 / χ_of_v)
    let χ_of_v'_eq_z' := χ_of_v'_eq_z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    unfold χ_of_v v
    rw [χ_of_v'_eq_z' h1]
    grind

lemma χ_of_v'_eq_z'_unfold_of_X'_ne_1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_v := LegendreSymbol.χ v q field_cardinality q_prime_power q_mod_4_congruent_3
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let term := Y * (X^2 + 1 / c^2)
  let χ_of_term := LegendreSymbol.χ term q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → χ_of_v = χ_of_term := by
    intro X Y v χ_of_v c term χ_of_term h1
    let χ_of_v'_eq_z' := χ_of_v'_eq_z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let X2_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩
    change X ≠ 0 at X2_ne_zero
    unfold χ_of_v χ_of_term term
    rw [χ_of_v'_eq_z' h1]
    rfl

lemma χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_v := LegendreSymbol.χ v q field_cardinality q_prime_power q_mod_4_congruent_3
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let term := Y * (u^2 + 1 / c^2)
  let χ_of_term := LegendreSymbol.χ term q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → χ_of_v = χ_of_term := by
    intro X Y v u χ_of_v c term χ_of_term h1
    let χ_of_v'_eq_z'_unfold_of_X'_ne_1 := χ_of_v'_eq_z'_unfold_of_X'_ne_1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    let u'_pow_two_eq_X_pow_two := u'_pow_two_eq_X_pow_two s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    grind

lemma u'_pow_two_add_one_over_c_pow_two_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  :
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  u^2 + 1 / c^2 ≠ 0 := by
    intro u_of_t c_of_s h1
    have h1_1 : -1 = (u_of_t * c_of_s)^2 := by
      ring
      have h1_1_1 : c_of_s^2 = c_of_s^2 := by rfl
      rw [← div_left_inj' (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
      rw [mul_div_assoc]
      rw [← div_eq_one_iff_eq (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1_1_1
      rw [h1_1_1, mul_one]
      rw [← add_left_inj (1 / c_of_s^2)]
      have h1_1_3 : 1 / c_of_s^2 = 1 / c_of_s^2 := by rfl
      rw [← neg_one_mul, mul_div_assoc, neg_one_mul]
      rw [neg_add_eq_zero.2 h1_1_3]
      symm
      exact h1
    have h1_2 : IsSquare (-1 : F) := by
      rw [h1_1]
      rw [pow_two]
      apply IsSquare.mul_self (u_of_t * c_of_s)
    have h1_3 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h1_2
      rw [field_cardinality] at h1_2
      exact h1_2
    contradiction

lemma Y'_observation1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_Y := LegendreSymbol.χ Y q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v := LegendreSymbol.χ v q field_cardinality q_prime_power q_mod_4_congruent_3
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_u'_pow_two_add_one_over_c_pow_two := LegendreSymbol.χ (u^2 + 1 / c^2) q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → χ_of_Y = χ_of_v * χ_of_u'_pow_two_add_one_over_c_pow_two  := by
    intro X Y v u χ_of_Y χ_of_v c χ_of_u'_pow_two_add_one_over_c_pow_two h1
    let χ_of_v'_eq_z'_unfold_of_X'_ne_1 := χ_of_v'_eq_z'_unfold_of_X'_ne_1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    let χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two := χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two  s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    unfold χ_of_v
    let term1 := (u^2 + 1 / c^2)
    let term2 := Y * term1
    let χ_of_term1 := LegendreSymbol.χ term1 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_term2 := LegendreSymbol.χ term2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2 : χ_of_v * χ_of_u'_pow_two_add_one_over_c_pow_two = χ_of_term2 * χ_of_u'_pow_two_add_one_over_c_pow_two := by grind
    have h3 : χ_of_v * χ_of_u'_pow_two_add_one_over_c_pow_two = χ_of_Y * χ_of_term1 * χ_of_u'_pow_two_add_one_over_c_pow_two := by
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b Y term1 q field_cardinality q_prime_power q_mod_4_congruent_3]
      grind
    rw [h3]
    have h4 : χ_of_term1 * χ_of_u'_pow_two_add_one_over_c_pow_two = 1 := by
      rw [← pow_two]
      let term1_ne_zero := u'_pow_two_add_one_over_c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
      rw [LegendreSymbol.χ_of_a_even_pow_n_eq_one term1 term1_ne_zero ⟨2, even_two⟩ ]
    grind

lemma Y'_observation2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let Y := Y' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let v := v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let χ_of_Y := LegendreSymbol.χ Y q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v := LegendreSymbol.χ v q field_cardinality q_prime_power q_mod_4_congruent_3
  let c := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_u'_pow_two_add_one_over_c_pow_two := LegendreSymbol.χ (u^2 + 1 / c^2) q field_cardinality q_prime_power q_mod_4_congruent_3
  X ≠ 1 → Y = (χ_of_v * v)^((q + 1) / 4) * χ_of_v * χ_of_u'_pow_two_add_one_over_c_pow_two  := by
    intro X Y v u χ_of_Y χ_of_v c χ_of_u'_pow_two_add_one_over_c_pow_two h1
    let χ_of_v'_eq_z'_unfold_of_X'_ne_1 := χ_of_v'_eq_z'_unfold_of_X'_ne_1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    let χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two := χ_of_v'_eq_χ_Y'_mul_u'_pow_two_add_one_over_c_pow_two  s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    let Y'_observation1 := Y'_observation1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    change χ_of_Y = χ_of_v * χ_of_u'_pow_two_add_one_over_c_pow_two at Y'_observation1
    let Y'_pow_two_eq_χ_of_v'_mul_v' := Y'_pow_two_eq_χ_of_v'_mul_v' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one h1
    rw [← Y'_pow_two_eq_χ_of_v'_mul_v', mul_assoc, ← Y'_observation1]
    rw [← pow_mul, add_comm]
    change Y = Y^(2 * ((1 + q) / 4)) * χ_of_Y
    rw [← field_cardinality]
    nth_rw 2 [mul_comm]
    rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two q field_cardinality q_mod_4_congruent_3]
    rw [field_cardinality, add_comm, LegendreSymbol.a_pow_q_add_one_over_two_eq_χ_of_a_mul_a Y q field_cardinality q_prime_power q_mod_4_congruent_3]
    change Y = χ_of_Y * Y * χ_of_Y
    rw [mul_comm, ← mul_assoc]
    rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b Y Y q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
    let Y'_ne_zero := Y'_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    rw [LegendreSymbol.χ_of_a_pow_two_eq_one Y Y'_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3]
    grind
