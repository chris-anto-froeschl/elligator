import Mathlib
import Architect
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
--import Elligator.Elligator1.Variables
import Elligator.Elligator1.Map

namespace Elligator.Elligator1

-- Original-Reference: Definition 2
section DecodingFunction

variable {F : Type*} [Field F] [Fintype F]
variable {s : F} (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

/-- In the situation of Theorem 1, the decoding function for the complete
Edwards curve E : x² + y² = 1 + dx²y² is the function ϕ : Fq → E(Fq) defined as follows: ϕ(±1) = (0, 1); if t ∉ {±1} then ϕ(t) = (x, y).

Original: Chapter "3.2 The map": Definition 2
-/
@[blueprint "def:def2"]
noncomputable def DecodingFunction
  (t : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F × F := ϕ t s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
