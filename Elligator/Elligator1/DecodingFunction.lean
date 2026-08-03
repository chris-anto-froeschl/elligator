/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.Elligator1.Map

/-!
# DecodingFunction

This file exposes the total field-to-curve map from Definition 2 of the Elligator paper under the
name `DecodingFunction`. The underlying construction is `ϕ`: it maps `t = ±1` to `(0, 1)` and,
for every other `t`, returns the coordinates constructed in Theorem 1.

## Main results

- `DecodingFunction`: the Elligator 1 decoding map `F → F × F`, obtained from the curve-valued
  map `ϕ` by forgetting its proof of curve membership.

## References

See [bernstein2013a] chapter 3.2, Definition 2.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

/--
Original: Chapter "3.2 The map": Definition 2
-/
@[blueprint
  (title := "The Map")
  (statement := /--
  Definition 2. In the situation of Theorem 1, the decoding function for the complete Edwards curve
  $E : x^2 + y^2 = 1 + d x^2 y^2$ is the function $\varphi : \mathbb{F}_q \to E(\mathbb{F}_q)$
  defined as follows:
  $$
  \varphi(\pm 1) = (0, 1);
  $$
  if $t \notin \{\pm 1\}$ then
  $$
  \varphi(t) = (x, y).
  $$

  Original: Chapter "3.2 The map": Definition 2
  -/)]
noncomputable def DecodingFunction
  (t : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (q_h1 : Fintype.card F = q)
  (q_h2 : IsPrimePow q)
  (q_h3 : q % 4 = 3)
  : F × F := ϕ t s_h1 s_h2 q_h1 q_h2 q_h3

end Elligator.Elligator1
