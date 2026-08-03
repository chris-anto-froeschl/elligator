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

See [bernstein2013a] chapter 3.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

@[blueprint "lemma:η_eq_zero"]
lemma η_eq_zero
  (t : { t : F // t = 1 ∨ t = -1})
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  :
  let P := (ϕ t.val s_h1 s_h2 q_h1 q_h2 q_h3).val
  let η := η P
  η = 0 := by
    intro P η
    unfold η Elligator1.η
    let y := P.2
    change (y - 1) / (2 * (y + 1)) = 0
    unfold y P
    rw [ϕ_of_t_eq_zero_one t s_h1 s_h2 q_h1 q_h2 q_h3]
    simp

end Elligator.Elligator1
