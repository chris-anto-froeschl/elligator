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

* `DecodingFunction`: the Elligator 1 decoding map `F → F × F`, obtained from the curve-valued
  map `ϕ` by forgetting its proof of curve membership.

## References

See [Bernstein2013a], Section 3.2, Definition 2.
-/

@[expose] public section

namespace Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

/-- The decoding function for the complete Edwards curve -/
@[blueprint
  (title := "Coordinates of the decoding function")
  (statement := /--
  In the situation of Theorem 1, the decoding function for the complete Edwards curve
  $E : x ^ 2 + y ^ 2 = 1 + d x ^ 2 y ^ 2$ is the function $\varphi :
  \mathbb{F}_q \to E(\mathbb{F}_q)$ with
  $$
  \varphi(\pm 1) = (0, 1), \qquad \varphi(t) = (x, y) \text{ for } t \notin \{\pm 1\}.
  $$
  Here $\varphi$ is regarded as a map $\mathbb{F}_q \to \mathbb{F}_q \times \mathbb{F}_q$,
  forgetting the proof that the image lies on $E$.
  -/)]
def DecodingFunction (t : F)
  (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) : F × F :=
  ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod

end Elligator.Elligator1
