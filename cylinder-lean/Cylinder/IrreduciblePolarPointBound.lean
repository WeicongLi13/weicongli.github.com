module

public import Cylinder.FrobeniusPlaneIrreducible
public import Cylinder.PolarIntersectionBound

/-!
# The actual rational-point bound for a nonlinear irreducible plane curve

Self-polar exclusion derives relative primality from irreducibility and
the degree bound. The complete-intersection and first-jet calculation
then gives the factor two, including singular rational points.
-/

@[expose] public section
noncomputable section

namespace Cylinder.IrreduciblePolarPointBound

open MvPolynomial Cylinder.FrobeniusPolar Cylinder.JetEvaluation Cylinder.HilbertEvaluation

variable {K I : Type*} [Field K] [IsAlgClosed K] [Fintype I]

theorem rational_point_bound (p n : ℕ) [Fact p.Prime] [CharP K p]
    (Q : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (hfixed : ∀ i, FrobeniusFixed p (v i))
    (hzero : ∀ i, eval (v i) Q = 0) :
    2 * Fintype.card I ≤ n * (n + p - 1) :=
  PolarIntersectionBound.rational_polar_point_bound_of_coprime p n (by omega) Q hQ
    hirr.ne_zero (FrobeniusPlaneIrreducible.polar_relPrime p n Q hQ hirr hn hnp)
    v hv hsep hfixed hzero

end Cylinder.IrreduciblePolarPointBound

end
