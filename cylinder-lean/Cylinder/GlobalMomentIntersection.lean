module

public import Cylinder.GlobalMomentCofactors
public import Cylinder.IntersectionIndependent

/-! Evaluation relations vanishing on the exclusive components are zero
in every degree at least s-2, on the actual rational direction set. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentIntersection

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.PlaneCurveFactors Cylinder.MinimumEquationComponentSets
open Cylinder.DirectionComponentDecomposition Cylinder.GlobalMomentSupport
open Cylinder.DirectionCurveBounds Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction

variable (p : ℕ) [Fact p.Prime]

theorem actual_intersection_relation_zero (D : Finset (PlanePoint (ZMod p))) (s : ℕ)
    (hs : InitialDegree (representatives (embedding p) D) s)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hsq : Squarefree F) (hzero : ∀ P ∈ D, eval P.rep F = 0)
    (c : D → CurveField p) (d : ℕ) (hd : s - 2 ≤ d)
    (hrel : PowerEvaluationRelation.Relation (representatives (embedding p) D) c d)
    (hvanish : ∀ G ∈ factors F, ∀ P : D, P.val ∈ componentPoints D F G → c P = 0) : c = 0 := by
  let FI : factors F → PlaneRing (CurveField p) := fun G => MvPolynomial.map (embedding p) G.val
  let e : factors F → ℕ := fun G => G.val.totalDegree
  have habs : ∀ G : factors F, Irreducible (FI G) := fun G =>
    MinimumEquationAbsoluteFactors.factors_absolutely_irreducible p D s
      ((RationalMinimumEquation.initialDegree_iff (embedding p) D s).mp hs)
      F hF hF0 hzero G.val G.property
  have hcop : Pairwise (fun G Q : factors F => IsRelPrime (FI G) (FI Q)) := by
    intro G Q hGQ
    apply (habs G).isRelPrime_iff_not_dvd.mpr
    intro hdiv
    have hbase : G.val ∣ Q.val := PolynomialDivisibilityDescent.dvd_of_mapped_dvd
      (L := CurveField p) G.val Q.val hdiv
    have hrelprime := factors_pairwise_relPrime F G.property Q.property
      (fun h => hGQ (Subtype.ext h))
    exact (factor_irreducible F G.val G.property).not_isUnit (hrelprime dvd_rfl hbase)
  have he : ∀ G, 0 < e G := fun G => positive_degree_of_irreducible G.val
    (factor_irreducible F G.val G.property)
  have hhom : ∀ G, (FI G).IsHomogeneous (e G) := fun G =>
    (factor_homogeneous F s hF hF0 G.val G.property).map _
  have hsum : (∑ G, e G) = s := by
    change (∑ G : factors F, G.val.totalDegree) = s
    rw [Finset.sum_coe_sort, MinimumEquationComponentSets.factors_degree_sum_eq F hF0 hsq,
      hF.totalDegree hF0]
  have hJ : ∀ P : Support c,
      IntersectionZeroSet.OnMultipleComponents FI (representatives (embedding p) D P.val) := by
    intro P
    have hPJ : P.val.val ∈ intersectionPoints D F := by
      apply Finset.mem_sdiff.mpr
      refine ⟨P.val.property, ?_⟩
      intro hPU
      obtain ⟨G, hG, hPG⟩ := Finset.mem_biUnion.mp hPU
      exact P.property (hvanish G hG P.val hPG)
    obtain ⟨G, hG, Q, hQ, hGQ, hGzero, hQzero⟩ :=
      intersectionPoints_multiple D F hF0 hzero P.val.val hPJ
    refine ⟨⟨G, hG⟩, ⟨Q, hQ⟩, (fun h => hGQ (congrArg Subtype.val h)), ?_, ?_⟩
    · change eval (representatives (embedding p) D P.val) (MvPolynomial.map (embedding p) G) = 0
      rw [MinimumEquationComponents.eval_mapped_cofactor, hGzero, map_zero]
    · change eval (representatives (embedding p) D P.val) (MvPolynomial.map (embedding p) Q) = 0
      rw [MinimumEquationComponents.eval_mapped_cofactor, hQzero, map_zero]
  have hind := IntersectionIndependent.independent_intersection_representatives FI e he hhom
    (fun G => (habs G).ne_zero) hcop (fun P : Support c => representatives (embedding p) D P.val)
    (fun P => representatives_nonzero _ _ P.val)
    (support_representatives_distinct _ c (representatives_distinct _ _)) hJ d (by rwa [hsum])
  exact support_eq_zero_of_independent (representatives (embedding p) D) c d hrel hind

end Cylinder.GlobalMomentIntersection

end
