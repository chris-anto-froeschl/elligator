/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Elligator.LegendreSymbol

/-!
# Elligator 1 Variables

In this file we introduce all the independent variables introduced in the definition of Elligator 1.

## References

See [bernstein2013a], Section 3.
-/

@[expose] public section

namespace Elligator.Elligator1

open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- c(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:c"
  (title := "The curve parameter $c$")
  (statement := /--
  Let $q$ be a prime power congruent to $3$ modulo $4$, and let $s$ be a nonzero element of
  $\mathbb{F}_q$ with $(s^2 - 2)(s^2 + 2) \neq 0$. Define
  $$
  c = 2/s^2 .
  $$
  -/)]
def c (s : F) : F := 2 / s^2

/-- r(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:r"
  (title := "The curve parameter $r$")
  (statement := /--
  With $c = 2/s^2$ as above, define
  $$
  r = c + 1/c .
  $$
  -/)]
def r (s : F) : F :=
  let c := c s;
  c + 1 / c

/-- d(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:d"
  (title := "The Edwards curve coefficient $d$")
  (statement := /--
  With $c = 2/s^2$ as above, define
  $$
  d = -(c + 1)^2/(c - 1)^2 ,
  $$
  the coefficient of the complete Edwards curve $E : x^2 + y^2 = 1 + d x^2 y^2$.
  -/)]
def d (s : F) : F :=
  let c := c s;
  -(c + 1)^2 / (c - 1)^2

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
  let t := t.val;
  (1 - t) / (1 + t)

/-- v(t, s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:v"
  (title := "The auxiliary quantity $v$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$, with $u$ and $r$ as above, define
  $$
  v = u^5 + (r^2 - 2)u^3 + u .
  $$
  -/)]
def v (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
  let u := u t
  let r := r s
  u^5 + (r^2 - 2) * u^3 + u

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
  Y = (\chi(v)v)^{(q+1)/4} \chi(v) \chi(u^2 + 1/c^2) .
  $$
  -/)]
def Y (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) (q : ℕ) : F :=
  let u := u t
  let c := c s
  let v := v t s
  ((χ v) * v)^((q + 1) / 4) * (χ v) * χ (u^2 + 1 / c^2)

/-- x(t, s) is a function defined in the paper. It is the x-coordinate of the point on the curve.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:x"
  (title := "The curve coordinate $x$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$, with $c$, $X$ and $Y$ as above, define
  $$
  x = (c - 1)sX(1 + X)/Y .
  $$
  -/)]
def x (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) (q : ℕ) : F :=
  let c := c s
  let X := X t s
  let Y := Y t s q
  (c - 1) * s * X * (1 + X) / Y

/-- y(t, s) is a function defined in the paper. It is the y-coordinate of the point on the curve.

Original:, Section "3.2 The map": Theorem 1
-/
@[blueprint "def:y"
  (title := "The curve coordinate $y$")
  (statement := /--
  For $t \in \mathbb{F}_q \setminus \{\pm 1\}$, with $r$ and $X$ as above, define
  $$
  y = (rX - (1 + X)^2)/(rX + (1 + X)^2) .
  $$
  -/)]
def y (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
  let r := r s
  let X := X t s
  (r * X - (1 + X)^2) / (r * X + (1 + X)^2)

/-- η(s, q, point) is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:η"
  (title := "The inversion quantity $\\eta$")
  (statement := /--
  For a point $(x, y)$ of $E(\mathbb{F}_q)$ with $y + 1 \neq 0$, define
  $$
  \eta = \frac{y - 1}{2(y + 1)} .
  $$
  -/)]
def η (P : F × F) : F :=
  let y := P.snd
  (y - 1) / (2 * (y + 1))

/-- Xbar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:Xbar"
  (title := "The reconstructed coordinate $\\bar X$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\eta$ as above, define
  $$
  \bar X = -(1 + \eta r) + ((1 + \eta r)^2 - 1)^{(q+1)/4} .
  $$
  -/)]
def Xbar (s : F) (P : F × F) (q : ℕ) : F :=
  let η := η P
  let r := r s
  (-(1 + η * r) + ((1 + η * r)^2 - 1)^((q + 1) / 4))

/-- z is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:z"
  (title := "The inversion sign $z$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\bar X$ as above, define
  $$
  z = \chi\bigl((c - 1)s\bar X(1 + \bar X)x(\bar X^2 + 1/c^2)\bigr) .
  $$
  -/)]
def z (s : F) (P : F × F) (q : ℕ) : F :=
  let x := P.fst
  let c := c s
  let Xbar := Xbar s P q
  let a := (c - 1) * s * Xbar * (1 + Xbar) * x * (Xbar^2 + 1 / c^2)
  χ a

/-- ubar is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:ubar"
  (title := "The reconstructed quantity $\\bar u$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $z$ and $\bar X$ as above, define
  $$
  \bar u = z\bar X .
  $$
  -/)]
def ubar (s : F) (P : F × F) (q : ℕ) : F :=
  let Xbar := Xbar s P q
  let z := z s P q
  z * Xbar

/-- t2 is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
@[blueprint "def:t2"
  (title := "The reconstructed preimage $\\bar t$")
  (statement := /--
  For a point $(x, y) \in \varphi(\mathbb{F}_q)$, with $\bar u$ as above, define
  $$
  \bar t = (1 - \bar u)/(1 + \bar u) .
  $$
  -/)]
def t2 (s : F) (P : F × F) (q : ℕ) : F :=
  let ubar := ubar s P q
  (1 - ubar) / (1 + ubar)

/-- `b q` is `⌊log₂ q⌋`, the number of bits needed.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
@[blueprint "def:b"
  (title := "The string length $b$")
  (statement := /--
  For a prime $q$, define the length of the encoded bit strings as
  $$
  b = \lfloor \log_2 q \rfloor .
  $$
  -/)]
def b (q : ℕ) : ℕ := Nat.log 2 q

/-- Convert a bit vector (τ₀, τ₁, ..., τ_{b-1}) to a natural number via binary
expansion: bitsToNat(τ) = Σᵢ τᵢ · 2^i.
-/
@[blueprint "def:bitsToNat"
  (title := "Binary value of a bit string")
  (statement := /--
  A bit string $(\tau_0, \tau_1, \ldots, \tau_{n-1}) \in \{0,1\}^n$ has binary value
  $$
  \sum_i \tau_i 2^i \in \mathbb{Z}_{\geq 0} .
  $$
  -/)]
def bitsToNat {n : ℕ} (τ : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if τ i then 2^(i : ℕ) else 0

/-- `σ` interprets a bit vector `(τ₀, τ₁, …, τ_{b−1})` as the field element
`∑ᵢ τᵢ · 2ⁱ ∈ Fq`. This is the standard binary-to-integer conversion followed by casting into `F`.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
@[blueprint "def:σ"
  (title := "The string-to-field map $\\sigma$")
  (statement := /--
  Define $\sigma : \{0,1\}^b \to \mathbb{F}_q$ by
  $$
  \sigma(\tau_0, \tau_1, \ldots, \tau_{b-1}) = \sum_i \tau_i 2^i .
  $$
  -/)]
def σ {q : ℕ} (τ : Fin (@b q) → Bool) : F := (bitsToNat τ : F)

/-- S = σ⁻¹({0, 1, 2, ..., (q-1)/2}), the set of bit vectors whose binary value
falls in the lower half {0, 1, ..., (q-1)/2} of F_q.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
@[blueprint "def:S"
  (title := "The admissible string set $S$")
  (statement := /--
  Define the set of admissible bit strings as
  $$
  S = \sigma^{-1}(\{0, 1, 2, \ldots, (q-1)/2\}) ,
  $$
  i.e. the strings whose binary value lies in the lower half of $\mathbb{F}_q$.
  -/)]
def S {q : ℕ} : Finset (Fin (@b q) → Bool) :=
  Finset.univ.filter (fun τ => (bitsToNat τ) ≤ (q - 1) / 2)

end Elligator.Elligator1
