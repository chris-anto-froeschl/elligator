import Mathlib
import Mathlib.Data.Set.Basic
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
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
import Elligator.Elligator1.Map
import Elligator.Elligator1.X2Properties
import Elligator.Elligator1.u2Properties
import Elligator.Elligator1.zProperties
import Elligator.Elligator1.t2Properties
import Elligator.Elligator1.phiProperties

namespace Elligator.Elligator1

-- Original: Chapter "3.3 Inverting the map" - Theorem 3
section InvertedMap

variable {F : Type*} [Field F] [Fintype F]

-- Original: Chapter "3.3 Inverting the map" - Theorem 3.1 :
--
-- "If t ∈ Fq then the set of preimages of ϕ(t) under ϕ is {t, −t}"
theorem ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let ϕ_of_neg_t := (ϕ (-t) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_t = ϕ_of_neg_t
  ↔ ¬ (∃ (p : { n : F // n ≠ t ∧ n ≠ -t}), ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ_of_t) := by
    intro ϕ_of_t ϕ_of_neg_t
    constructor
    · intro h
      exact ϕ_preimages t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · intro h
      exact ϕ_of_t_eq_ϕ_of_neg_t t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Original: Chapter "3.3 Inverting the map" - Theorem 3.2 :
--
-- "ϕ(Fq) is the set of (x, y) ∈ E(Fq) such that
-- • y + 1 ≠ 0;
-- • (1+ηr)² - 1 is a square, where η = (y − 1) / (2(y + 1)); and
-- • if ηr = −2 then x = 2s(c − 1)χ(c)/r."
--
-- Note: Original statement does not read like an iff. Only the proof explanation
-- makes this more concrete
theorem point_props_iff_point_in_ϕ_over_F_of_point
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  ↔ point.val ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 := by
    intro point
    constructor
    · exact point_in_ϕ_over_F_of_point_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    · exact point_props_of_point_in_ϕ_over_F t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Original: Chapter "3.3 Inverting the map" - Theorem 3.3
-- If (x, y) ∈ ϕ(Fq) then the following elements X_bar, z, u_bar, t_bar of Fq are defined and ϕ(t_bar) = (x, y):
--    X_bar = −(1 + ηr) + ((1 + ηr)² − 1)^((q+1)/4),
--    z = χ((c − 1)s * X_bar * (1 + X_bar) * x * (X_bar² + 1/c²)),
--    u_bar = z * X_bar,
--    t_bar = (1 − u_bar)/(1 + u_bar)
theorem ϕ_of_t2_eq_x_y
  -- Fix t ∈ F_q
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  -- Define (x, y) = ϕ(t)
  let point := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let x_of_t := point.1
  let y_of_t := point.2
  -- t2 defined (and used to build ϕ(t2))
  let t' := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let ϕ_of_t' := (ϕ t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_t' = (x_of_t, y_of_t) := by
    intro point x_of_point y_of_point t' ϕ_of_t'
    unfold x_of_point y_of_point point ϕ
    simp only []
    split
    · rename_i h
      exact ϕ_of_t2_eq_x_y_main_case ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · rename_i h
      have h1_1 : t = 1 ∨ t = -1 := by
        rw [← not_ne_iff, ← not_ne_iff, ← Lean.Grind.not_and]
        exact h
      simp
      exact ϕ_of_t2_eq_x_y_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

theorem X2_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  let y := point.val.snd
  2 * (y + 1) ≠ 0 := by
    intro y
    have h1 : y + 1 ≠ 0 := by
      unfold y
      let h1_1 := point.prop
      unfold ϕ_over_F at h1_1
      rw [Set.mem_setOf_eq] at h1_1
      rcases h1_1 with ⟨t, h1_2⟩
      unfold ϕ at h1_2
      by_cases h1_3 : t ≠ 1 ∧ t ≠ -1
      · simp only [] at h1_2
        rw [dif_pos h1_3] at h1_2
        let h1_4 := congrArg Prod.snd h1_2
        simp at h1_4
        rw [← h1_4]
        exact y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h1_3⟩
      · simp only [] at h1_2
        rw [dif_neg h1_3] at h1_2
        let h1_4 := congrArg Prod.snd h1_2
        simp at h1_4
        rw [← h1_4]
        ring_nf
        exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)
    apply mul_ne_zero
    · exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)
    · exact h1

theorem z_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  c_of_s^2 ≠ 0
  := by
    exact (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)

theorem t2_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  (1 + u2_of_point) ≠ 0 := by
    exact one_add_u2_ne_zero s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3 point
