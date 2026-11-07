import Cylinder.MainTheorem
import Cylinder.RedeiTheorem
import Cylinder.FinalPlaneSums
import Cylinder.AffineProjection
import Cylinder.EmptyPlaneChart
import Cylinder.ProjectivePlaneCap
import Cylinder.EmptyLineBound
import Cylinder.ProjectiveBalance
import Cylinder.DualLineBalance
import Cylinder.ProjectiveCover
import Cylinder.ProjectiveCoplanarity
import Cylinder.ProjectiveBlackLine
import Cylinder.ProjectiveLineCap
import Cylinder.ProductProposition
import Cylinder.OriginalPointCharacter
import Cylinder.ActualIdealCharacter
import Cylinder.IntegerCharacterFormulas
import Cylinder.FinalGapCharacter
import Cylinder.GapRelations
import Cylinder.ActualCharacterBoundsAllSets
import Cylinder.OriginalSchemeBezout
import Cylinder.CompleteIntersectionPointBound
import Cylinder.FinalCurvePointBound
import Cylinder.FrobeniusPolarBound
import Cylinder.ProjectiveVandermonde
import Cylinder.SimpleBlackWeights
import Cylinder.ExactRayMomentsTheorem
import Cylinder.ExactRayMomentsSupportedProduct
import Cylinder.DirectionExcess
import Cylinder.DirectionCurveProposition
import Cylinder.MinimumEquationAbsoluteFactors
import Cylinder.MinimumEquationReduced
import Cylinder.DirectionCurveComponentBounds
import Cylinder.FinalGlobalMoments
import Cylinder.FinalAssociatedChart
import Cylinder.ProjectiveNormalizedDuality
import Cylinder.CompleteIntersectionSupport
import Cylinder.BinaryFormLemma
import Cylinder.PlanePlateauTheorem
import Cylinder.PlateauPolynomial
import Cylinder.PolynomialPoles
import Cylinder.FinalLocalCurveTheorem
import Cylinder.NumericalObstruction
import Cylinder.ComponentInterpolationAll
import Cylinder.ComponentInterpolation
import Cylinder.IntersectionIntegerIndependent
import Cylinder.BMMTheorem
import Cylinder.FinalConsequences
import Cylinder.FinalExceptionalDirections
import Cylinder.WhiteQuadricLift
import Cylinder.WhiteQuadricResidual
import Cylinder.WhiteQuadricCoordinates
import Cylinder.MomentQuadric
import Cylinder.FinalFactorFourier
import Cylinder.FinalFirstMoment
import Cylinder.RedeiInterpolation
import Cylinder.RedeiFactorPlaneCounts
import Cylinder.ProjectiveCylinderTheorem
import Cylinder.ArbitraryProjectionModel
import Cylinder.ProjectionTransportVandermonde
import Cylinder.ManuscriptProjectionBounds
import Cylinder.ManuscriptExceptionalDirections
import Cylinder.ArbitraryMoments
import Cylinder.ArbitraryMomentPrescribed
import Cylinder.MomentProductCoordinates
import Cylinder.MomentProductActual
import Cylinder.ManuscriptMomentTheorems

/-! Entry points corresponding to the numbered results of finalfinal.tex.
This file imports only the manuscript's proof dependency closure.
Some assertions are assembled from several declarations, listed together.
Coordinate models and choices of representatives are explained in their modules.
Manuscript SHA-256: 73a7eb8e529123aaf37ce139248ca5847ec3e1ec9061241e022a9ea7b47f8b2e.
To reproduce with the pinned toolchain and dependencies:
  lake exe cache get
  lake build FinalFinal
  lake env lean FinalFinalAudit.lean
-/

-- Theorem 1.1 (thm:main).
#check Cylinder.MainTheorem.cylinder_of_plane_divisibility
-- The unnumbered projective form following Theorem 1.1: arbitrary original
-- projective set and infinity plane, and actual concurrent projective lines.
#check Cylinder.ProjectiveSetChart.inverseEmbed_chartSet
#check Cylinder.ProjectiveCylinderTheorem.projective_strongCylinder
-- Theorem 1.2 (thm:redei).
#check Cylinder.Redei.coordinate_factorization
#check Cylinder.Redei.redei_factorization

-- Lemma 3.1 (lem:KMNS-polynomial).
#check Cylinder.FinalPlaneSums.weighted_polynomial_sum
#check Cylinder.FinalPlaneSums.reduced_totalDegree_le
-- Lemma 3.2 (lem:projection).
#check Cylinder.AffineProjection.noncylinder_projection
-- Lemma 3.3 (lem:infinity).
#check Cylinder.EmptyPlaneChart.empty_plane_as_infinity
-- Lemma 3.4 (lem:planecap).
#check Cylinder.EmptyLineBound.emptyQuotientLines_card_le_in_affine_coordinates
#check Cylinder.ProjectivePlaneCap.dual_plane_white_card_le
-- Lemma 3.5 (lem:incidence).
#check Cylinder.ProductIntersection.white_card_lower_bound
#check Cylinder.ProjectiveBalance.sum_black_weight
#check Cylinder.ProjectiveBalance.sum_black_energy
#check Cylinder.DualLineBalance.line_balance
#check Cylinder.ProjectiveBalance.black_nonempty
#check Cylinder.ProjectiveBalance.white_card_upper_bound
-- Lemma 3.6 (lem:cylinder_property).
#check Cylinder.ProjectiveCover.exists_white_through_outside
#check Cylinder.ProjectiveCoplanarity.whiteCoplanar_iff_isCylinder
#check Cylinder.ProjectiveBlackLine.isCylinder_of_blackCollinear
-- Lemma 3.7 (lem:linecap).
#check Cylinder.ProjectiveLineCap.mixed_cap
#check Cylinder.ProjectiveLineCap.line_white_card_le_half
#check Cylinder.ProjectiveLineCap.black_weight_add_one_le_half
#check Cylinder.ProjectiveLineCap.black_weight_le
-- Proposition 3.8 (prop:product).
#check Cylinder.ProductProposition.scaled_product_and_full_support_relation

-- Proposition 4.1 (prop:character-source).
#check Cylinder.ActualIdealCharacter.character_formulas
#check Cylinder.IntegerCharacterFormulas.integerDefect_eq_relations
#check Cylinder.IntegerCharacterFormulas.integerDefect_character_formula
#check Cylinder.IntegerCharacterFormulas.last_positive_degree
#check Cylinder.OriginalPointCharacter.numerical_character
#check Cylinder.OriginalPointCharacter.cohomologyOne_eq_relations
-- Proposition 4.2 (prop:gap-source).
#check Cylinder.FinalGapCharacter.projective_gap_character_prefix
-- Lemma 4.3 (lem:gap).
#check Cylinder.PlaneGap.gap_data
#check Cylinder.GapRelations.full_support_gap_bound
-- Proposition 4.4 (prop:relationbound).
#check Cylinder.ActualCharacterBoundsAllSets.projective_full_support_character_bounds
-- Proposition 4.5 (prop:bezout-source).
#check Cylinder.OriginalSchemeBezout.bezout
#check Cylinder.CompleteIntersectionPointBound.projective_cardinal_bound
-- Proposition 4.6 (prop:CV).
#check Cylinder.FinalCurvePointBound.carlin_voloch
-- Lemma 4.7 (lem:polar).
#check Cylinder.FrobeniusPolarBound.prime_field_card_le_half
-- Lemma 4.8 (lem:bootstrap).
#check Cylinder.ProjectionTransportVandermonde.ray_card_lower_bound
#check Cylinder.ArbitraryProjectionModel.actual_unique_intersection
#check Cylinder.ArbitraryProjectionModel.planeSetEquiv
#check Cylinder.ArbitraryProjectionModel.planeRay_card
#check Cylinder.ArbitraryProjectionModel.planeEquivForChart_map
#check Cylinder.ArbitraryProjectionModel.exists_actual_model
#check Cylinder.ProjectiveVandermonde.ray_card_lower_bound
-- Proposition 4.9 (prop:simple).
#check Cylinder.SimpleBlackWeights.simple_black_points
-- Proposition 4.10 (prop:exactmoments).
#check Cylinder.ManuscriptMomentTheorems.exact_and_global_moments
#check Cylinder.ManuscriptMomentTheorems.all_moment_relations
#check Cylinder.ArbitraryMoments.exact_moments
#check Cylinder.ArbitraryMoments.first_moment_relation
#check Cylinder.ArbitraryMoments.evaluation_relation
#check Cylinder.ArbitraryMoments.all_moment_relations_over_field
#check Cylinder.ArbitraryMomentPrescribed.all_moment_relations
#check Cylinder.ArbitraryMoments.prescribed_coordinates
#check Cylinder.ArbitraryMoments.prescribed_representatives
#check Cylinder.MomentProductCoordinates.product_identity_iff
#check Cylinder.MomentProductCoordinates.power_identity_iff
#check Cylinder.MomentProductCoordinates.white_factor
#check Cylinder.ExactRayMomentsTheorem.exists_product_exact_moments
#check Cylinder.ExactRayMomentsTheorem.weight_one_full_support_direction_relation
#check Cylinder.ExactRayMomentsSupportedProduct.supported_balanced_product_exact_moments
-- Corollary 4.11 (cor:excess).
#check Cylinder.ManuscriptProjectionBounds.excess
#check Cylinder.DirectionExcess.direction_excess_bounds
-- Proposition 4.12 (prop:window).
#check Cylinder.ManuscriptProjectionBounds.window
#check Cylinder.DirectionCurveProposition.direction_curve
-- Lemma 4.13 (lem:window-components).
#check Cylinder.ManuscriptProjectionBounds.components
#check Cylinder.DirectionCurveProposition.direction_curve_with_components
#check Cylinder.MinimumEquationAbsoluteFactors.factors_absolutely_irreducible
#check Cylinder.MinimumEquationReduced.squarefree_of_initialDegree
#check Cylinder.MinimumEquationAbsoluteFactors.factor_irreducible_after_extension
#check Cylinder.DirectionCurveComponentBounds.component_bounds

-- Theorem 5.1 (thm:globalmoments).
#check Cylinder.ManuscriptMomentTheorems.exact_and_global_moments
#check Cylinder.ArbitraryMoments.global_moments_unique
#check Cylinder.ArbitraryMoments.global_moments_reindexed
#check Cylinder.FinalGlobalMoments.global_moments_unique_prime
#check Cylinder.FinalGlobalMoments.global_moments
-- Proposition 5.2 (prop:associatedgraded).
#check Cylinder.FinalAssociatedChart.associatedgraded
#check Cylinder.FinalAssociatedGraded.multiplication_filtered_classes
#check Cylinder.FinalAssociatedGraded.degree_preserving
#check Cylinder.FinalAssociatedChart.associatedgraded_degree_range
-- Lemma 5.3 (lem:ci).
#check Cylinder.ProjectiveNormalizedDuality.exists_normalized_duality
#check Cylinder.ProjectiveNormalizedDuality.normalized_duality_multiply
-- Corollary 5.4 (cor:ciindependence).
#check Cylinder.CompleteIntersectionSupport.independent_complete_intersection_points
-- Lemma 5.5 (lem:binary).
#check Cylinder.BinaryFormLemma.binary_lemma
-- Lemma 5.6 (lem:plateaufactor).
#check Cylinder.PlanePlateauTheorem.plane_plateau
#check Cylinder.PlateauPolynomial.plane_plateau
-- Lemma 5.7 (lem:poles).
#check Cylinder.PolynomialPoles.finite_common_denominator_polynomial_bounds
-- Lemma 5.8 (lem:momentplateau), with the manuscript's 4m+2 bound.
#check Cylinder.FinalLocalCurveTheorem.local_curve_interpolation
-- Lemma 5.9 (lem:numeric).
#check Cylinder.Numerical.numerical_obstruction
-- Proposition 5.10 (prop:componentmoments).
#check Cylinder.ManuscriptMomentTheorems.component_moments
#check Cylinder.ArbitraryMoments.component_moments_over_field
#check Cylinder.ArbitraryMomentPrescribed.component_moments
#check Cylinder.ComponentInterpolationAll.exists_actual_component_forms
#check Cylinder.ComponentInterpolation.component_interpolation_given_residues
-- Lemma 5.11 (lem:intersectionindependence).
#check Cylinder.IntersectionIntegerIndependent.projective_intersection_integer_relations_eq_bot

-- Theorem 6.1 (thm:hyperfocused).
#check Cylinder.BMMTheorem.bmm_classification
-- Lemma 6.2 (lem:nocap).
#check Cylinder.FinalConsequences.exists_three_collinear_white
-- Proposition 6.3 (prop:noquadric).
#check Cylinder.FinalConsequences.quadric_vanishing_implies_zero
-- Lemma 6.4 (lem:exceptionindependence).
#check Cylinder.ManuscriptExceptionalDirections.independent
#check Cylinder.ManuscriptExceptionalDirections.relation_space_eq_bot
#check Cylinder.FinalExceptionalDirections.exceptional_directions_independent
#check Cylinder.FinalExceptionalDirections.exceptional_direction_relation_space_eq_bot
-- Proposition 6.5 (prop:liftquadric).
#check Cylinder.WhiteQuadricLift.white_quadric_lift
#check Cylinder.WhiteQuadricResidual.white_residual_empty_given_moments
#check Cylinder.MomentQuadric.quadric_nonzero
#check Cylinder.WhiteQuadricCoordinates.coordinate_quadric_to_original

-- Lemma 7.1 (lem:factorfourier).
#check Cylinder.FinalFactorFourier.uniform_projection_dichotomy
-- Lemma 7.2 (lem:firstmoment).
#check Cylinder.FinalFirstMoment.exists_nonzero_moment
-- Lemma 7.3 (lem:momentvector).
#check Cylinder.Redei.interpolation_radial
-- Proposition 7.4 (prop:factorpdivisible).
#check Cylinder.Redei.pDivisible_of_spanning_factor
