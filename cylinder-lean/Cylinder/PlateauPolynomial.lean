module

public import Cylinder.PlanePlateauTheorem

/-!
# The plateau factor for arbitrary low-degree ideal elements

For a homogeneous saturated ideal, the constructed curve factor divides the
entire polynomial, by applying the actual plateau theorem to its homogeneous
components. This is the literal low-degree-element conclusion of `lem:plateau`.
-/

@[expose] public section
noncomputable section
namespace Cylinder.PlateauPolynomial
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.SaturatedPlaneLine
open Cylinder.NumericCharacterSequence
variable {K : Type*} [Field K] [Infinite K]
local instance : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

theorem plane_plateau (J : Ideal (PlaneRing K)) (hJ : Saturated J)
    (hhom : J.IsHomogeneous (Forms K)) (z q c : ℕ)
    (hz : Cylinder.PlanePlateau.InitialDegree J z) (hq : z - 1 ≤ q) (hc : 0 < c)
    (h0 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) q = c)
    (h1 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) (q + 1) = c) :
    ∃ G : PlaneRing K, G ≠ 0 ∧ G.IsHomogeneous c ∧ G.totalDegree = c ∧
      ∀ P : PlaneRing K, P ∈ J → P.totalDegree ≤ q + 1 → G ∣ P := by
  obtain ⟨G, hG0, hG, hdegree, hlow⟩ :=
    Cylinder.PlanePlateauTheorem.plane_plateau J hJ z q c hz hq hc h0 h1
  refine ⟨G, hG0, hG, hdegree, ?_⟩
  intro P hPJ hPd
  rw [← sum_homogeneousComponent P]
  apply Finset.dvd_sum
  intro n hn
  exact hlow n _ (homogeneousComponent_mem n P)
    (homogeneousComponent_mem_of_mem hhom hPJ n)
    (by have := Finset.mem_range.mp hn; omega)

end Cylinder.PlateauPolynomial
end
