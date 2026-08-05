/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Basic

/-!
# s Variable Properties

In this file we introduce some generally helpful lemmas for `s` as introduced
in `Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}

omit [Fintype F] in
lemma s_pow_two_ne_two (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  : s^2 ≠ 2 := by
  have h1 : s^2 - 2 ≠ 0 := by
    intro h
    rw [h] at sq_ne_pm_two
    norm_num at sq_ne_pm_two
  intro h
  rw [h] at h1
  norm_num at h1

omit [Fintype F] in
lemma s_pow_two_ne_neg_two (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : s^2 ≠ -2 := by
  have h1 : s^2 + 2 ≠ 0 := by
    intro h
    rw [h] at sq_ne_pm_two
    norm_num at sq_ne_pm_two
  intro h
  rw [h] at h1
  norm_num at h1

end Elligator.Elligator1
