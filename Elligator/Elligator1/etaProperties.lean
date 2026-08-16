/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Variables
public import Elligator.Elligator1.Map
public import Elligator.Elligator1.MapProperties

/-!
# η Properties

In this file we introduce some generally helpful lemmas for `η` as introduced in
`Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

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

end Elligator.Elligator1
