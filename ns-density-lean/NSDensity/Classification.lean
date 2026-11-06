import NSDensity.Constructions
import NSDensity.ESArithmetic

/-!
The explicit forward classification interface. `NS n q` denotes the mathematical
predicate for a nonstandard nondegenerate irreducible cyclic code. It is a
predicate parameter: the coding-theoretic classification itself is not re-proved.
The initial families and every construction condition are spelled out below.

For an upper bound we harmlessly include the exceptional primitive pair (3,2)
and the arithmetic equally-spaced case of length 4. Thus the interface is a
weaker, directly applicable consequence of the cited FHLX classification.
-/

namespace NSDensity

inductive InitialFamily (p a e : ℕ) : Prop
  | dual (he : e = 1) (ha : a.Prime) (ha5 : 5 ≤ a)
      (hord : orderOf (p : ZMod a) = a - 1) : InitialFamily p a e
  | primitive (m : ℕ) (hm : 2 ≤ m) (ha : a = p ^ (e * m) - 1) :
      InitialFamily p a e
  | ovoid (ha : a = (p ^ e - 1) * (p ^ (2 * e) + 1)) : InitialFamily p a e
  | golay_binary (hp : p = 2) (ha : a = 23) (he : e = 1) : InitialFamily p a e
  | golay_ternary (hp : p = 3) (ha : a = 11) (he : e = 1) : InitialFamily p a e
  | equally_spaced (h : EquallySpaced (p ^ e) a) : InitialFamily p a e

def Initial (p a e : ℕ) : Prop :=
  0 < a ∧ 0 < e ∧ Nat.Coprime (p ^ e) a ∧ InitialFamily p a e

/-- The permitted external FHLX input: every actual exceptional pair has a path
from one of the listed families, with the four construction types made explicit. -/
def FHLXInput (NS : ℕ → ℕ → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n f : ℕ, 0 < n → Nat.Coprime p n → 0 < f →
    NS n (p ^ f) → ∃ a e : ℕ, Initial p a e ∧
      Relation.ReflTransGen (ClassificationStep p) (a, e) (n, f)

def ExceptionalLengths (NS : ℕ → ℕ → Prop) (p : ℕ) : Set ℕ :=
  {n | 0 < n ∧ Nat.Coprime p n ∧ ∃ f : ℕ, 0 < f ∧ NS n (p ^ f)}

end NSDensity
