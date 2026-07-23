/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
import Mathlib
import Architect
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
--import Elligator.Elligator1.Variables
import Elligator.Elligator1.Map

/-!
# Decoding Function

In this file we define the decoding function of Elligator 1.

## References

See [bernstein2013a] chapter 3 definition 2.
-/

namespace Elligator.Elligator1

-- Original-Reference: Definition 2
section DecodingFunction

variable {F : Type*} [Field F] [Fintype F]
variable {s : F} (s_h2 : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
variable {q : ℕ} (q_h1 : Fintype.card F = q) (q_h2 : IsPrimePow q) (q_h3 : q % 4 = 3)

/--
Original: Chapter "3.2 The map": Definition 2
-/
@[blueprint
  (title := "The Map")
  (statement := /--
  Definition 2. In the situation of Theorem 1, the decoding function for the complete Edwards curve
  $E : x^2 + y^2 = 1 + d x^2 y^2$
  is the function $\varphi : \mathbb{F}_q \to E(\mathbb{F}_q)$ defined as follows:
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

end DecodingFunction

end Elligator.Elligator1
