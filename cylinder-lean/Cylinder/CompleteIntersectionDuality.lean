module

public import Cylinder.ResidualQuotientPieces

/-! The actual homogeneous residual quotient represents finite point
relations, with the complementary degree proved from the actual affine
complete-intersection algebra. -/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionDuality

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionFiltered Cylinder.AffinePointEvaluation
open Cylinder.AffineEvaluationDuality Cylinder.FiniteEvaluationDuality
open Cylinder.CurvePolarLocal Cylinder.PlaneHomogenization
open Cylinder.HomogeneousCompleteIntersection Cylinder.ResidualEvaluation Cylinder.ResidualQuotientPieces
open scoped Classical

variable {K I : Type*} [Field K] [Fintype I]

/-- The manuscript's degree-j relation space is the actual residual
homogeneous quotient in degree e+t-3-j, in its nonnegative range. -/
def relationResidualEquiv (F G : HomRing (K := K)) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hge : homogeneousComponent t (dehomogenize G) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G)))
    (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) (dehomogenize F) = 0)
    (hgv : ∀ i, eval (v i) (dehomogenize G) = 0)
    (j : ℕ) (hj : j < e + t - 2) :
    coefficientRelations v j ≃ₗ[K] ResidualQuotientPiece F G v (e + t - 2 - j - 1) :=
  (affineEvaluationDuality (dehomogenize F) (dehomogenize G) e t he ht hf hg hfe hge hcop
    v hv hfv hgv j hj).symm.trans
      (residualQuotientEquiv F G e t (e + t - 2 - j - 1) hF hG hf hg hfe hcop v hfv hgv).symm

#print axioms relationResidualEquiv

end Cylinder.CompleteIntersectionDuality

end
