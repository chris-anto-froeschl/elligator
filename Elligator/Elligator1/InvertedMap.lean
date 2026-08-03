/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.phiProperties

/-!
# Inverted Map

This file collects the three conclusions of Theorem 3 in the Elligator paper. It describes the
preimage and image of `ϕ`, and verifies the paper's explicit inverse formula on that image.

## Main results

- `ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages`: the preimage of `ϕ t` consists exactly of `t` and `-t`;
  in particular, `ϕ t = ϕ (-t)` and there are no other preimages.
- `P_props_iff_P_in_ϕOverF_of_P`: membership in the image `ϕ(F)` is equivalent to the three
  algebraic point conditions stated in part 2 of Theorem 3.
- `X2_defined`, `z_defined`, `t2_defined`: the denominators required by the inverse construction
  are nonzero on `ϕ(F)`.
- `ϕ_of_t2_eq_x_y`: applying `ϕ` to the reconstructed parameter `t2` recovers the original point.


## References

See [bernstein2013a], Section 3.3, Theorem 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

/-- The fiber of `ϕ t` consists exactly of the two field elements `t` and `-t`.

This is part 1 of Theorem 3. The left side records `ϕ t = ϕ (-t)`; the right side says that no
field element distinct from both `t` and `-t` maps to `ϕ t`. -/
@[blueprint "thm:thm3-1"]
theorem ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages
  (t : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let ϕ_of_t := (ϕ t s_h1 s_h2 q_h1 q_h2 q_h3).val
  let ϕ_of_neg_t := (ϕ (-t) s_h1 s_h2 q_h1 q_h2 q_h3).val
  ϕ_of_t = ϕ_of_neg_t
  ↔ ¬(∃ (p : { n : F // n ≠ t ∧ n ≠ -t}), ϕ p.val s_h1 s_h2 q_h1 q_h2 q_h3 = ϕ_of_t) := by
    intro ϕ_of_t ϕ_of_neg_t
    constructor
    · intro h
      exact ϕ_preimages t s_h1 s_h2 q_h1 q_h2 q_h3
    · intro h
      exact ϕ_of_t_eq_ϕ_of_neg_t t s_h1 s_h2 q_h1 q_h2 q_h3

/-- Characterization of the image of `ϕ` by the three conditions in part 2 of Theorem 3.
For `P = ϕ t`, membership in `ϕ(F)` is equivalent to `ϕOverFProps s P`: `y + 1 ≠ 0`,
`(1 + ηr)² - 1` is a square, and the exceptional case `ηr = -2` has the specified `x`-coordinate.

Note: Original statement does not read like an iff. Only the proof explanation
makes this more concrete.
-/
@[blueprint "thm:thm3-2"]
theorem P_props_iff_P_in_ϕOverF_of_P
  (t : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := ϕ t s_h1 s_h2 q_h1 q_h2 q_h3
  ϕOverFProps s P ↔ P.val ∈ ϕOverF s_h1 s_h2 q_h1 q_h2 q_h3 := by
    intro P
    constructor
    · exact P_in_ϕOverF_of_P_props s_h1 s_h2 q_h1 q_h2 q_h3 P
    · exact P_props_of_P_in_ϕOverF t s_h1 s_h2 q_h1 q_h2 q_h3

/-- The explicit inverse formula in part 3 of Theorem 3 recovers a point in `ϕ(F)`.

Starting with `P = ϕ t`, the definitions `X2`, `z`, `u2`, and `t2` reproduce the paper's
quantities `X̄`, `z`, `ū`, and `t̄`; evaluating `ϕ (t2 s P q)` returns the coordinates of `P`. -/
@[blueprint "thm:thm3-3"]
theorem ϕ_of_t2_eq_x_y
  -- Fix t ∈ F_q
  (t : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  -- Define (x, y) = ϕ(t)
  let P := (ϕ t s_h1 s_h2 q_h1 q_h2 q_h3).val
  let x_of_t := P.1
  let y_of_t := P.2
  -- t2 defined (and used to build ϕ(t2))
  let t' := t2 s P q
  let ϕ_of_t' := (ϕ t' s_h1 s_h2 q_h1 q_h2 q_h3).val
  ϕ_of_t' = (x_of_t, y_of_t) := by
    intro P x_of_P y_of_P t' ϕ_of_t'
    unfold x_of_P y_of_P P ϕ
    simp only []
    split
    · rename_i h
      exact ϕ_of_t2_eq_x_y_main_case ⟨t, h⟩ s_h1 s_h2 q_h1 q_h2 q_h3
    · rename_i h
      exact ϕ_of_t2_eq_x_y_base_case ⟨t, by grind⟩ s_h1 s_h2 q_h1 q_h2 q_h3

/-- The denominator `2 * (y + 1)` in the inverse construction is nonzero on `ϕ(F)`.
This supplies the definedness of `η`, and hence of `X2`, in part 3 of Theorem 3. -/
@[blueprint "thm:X2_defined"]
theorem X2_defined
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ ϕOverF s_h1 s_h2 q_h1 q_h2 q_h3})
  :
  let y := P.val.snd
  2 * (y + 1) ≠ 0 := by
    intro y
    have h1 : y + 1 ≠ 0 := by
      unfold y
      let h1_1 := P.prop
      unfold ϕOverF at h1_1
      rcases h1_1 with ⟨t, h1_2⟩
      unfold ϕ at h1_2
      by_cases h1_3 : t ≠ 1 ∧ t ≠ -1
      · grind [y_add_one_ne_zero ]
      · simp only [] at h1_2
        rw [dif_neg h1_3] at h1_2
        let h1_4 := congrArg Prod.snd h1_2
        rw [← h1_4]
        ring_nf
        exact two_ne_zero q_h1 q_h2 q_h3
    exact mul_ne_zero (two_ne_zero q_h1 q_h2 q_h3) h1

/-- The denominator `c²` occurring in the definition of `z` is nonzero. -/
@[blueprint "thm:z_defined"]
theorem z_defined
  (s_h1 : s ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : (c s)^2 ≠ 0 := c_pow_two_ne_zero s_h1 q_h1 q_h2 q_h3

/-- The denominator `1 + u2` in the reconstructed parameter `t2` is nonzero on `ϕ(F)`. -/
@[blueprint "thm:t2_defined"]
theorem t2_defined
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  (P : {p : F × F // p ∈ ϕOverF s_h1 s_h2 q_h1 q_h2 q_h3})
  :
  let u2_of_P := u2 s P.val q
  (1 + u2_of_P) ≠ 0 := one_add_u2_ne_zero s_h1 s_h2 q_h1 q_h2 q_h3 P

end Elligator.Elligator1
