module

public import Cylinder.LocalResidualRepresentatives
public import Cylinder.LocalCharacterData
public import Cylinder.ResidualChartSaturation

/-! The actual residual Hilbert plateau is derived from the actual numerical
character and the low-degree residue isomorphism. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.LocalResidualHilbert
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.PlaneBinaryReduction Cylinder.LocalResidualRepresentatives
open Cylinder.LocalCharacterData Cylinder.ComponentCharacterNumeric
open Cylinder.HilbertCharacterFormulas Cylinder.NumericalIdealFormula
open Cylinder.NumericCharacterSequence Cylinder.ResidualChartSaturation

variable {K : Type*} [Field K] [Infinite K]

theorem actual_residual_saturated (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K)) :
    SaturatedPlaneLine.Saturated (ResidualIdeal F G D) := by
  have hL := PlaneCoordinateInverse.chartCoordinates_symm_homogeneous c.a c.b c.ha c.hb
    (X (none : Option (Fin 2))) 1 (isHomogeneous_X K none)
  exact (equations_residual_saturated c.coordinates F G e t
    (PlaneLineCoordinates.chartCoordinates_homogeneous c.a c.b c.ha c.hb F e hF)
    (PlaneLineCoordinates.chartCoordinates_homogeneous c.a c.b c.ha c.hb G t hG)
    hgood.degreeF hgood.degreeG hgood.topF hgood.topcop hL).2 _

theorem residual_hilbert_and_relation (c : Chart K) (F G : PlaneRing K) (e t d β q : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (hdegree : (e : ℤ) + t - 3 - d = β) (hqd : q ≤ d)
    (hqne : β + q < e) (hqnt : β + q < t) :
    Cylinder.PlanePlateau.quotientHilbert (ResidualIdeal F G D) (β + q) +
      finrank K (PlaneRelationSpaces.relationSpace (fun P : D => c.normalizedPoint P.val) (d - q)) =
        triangular (β + q + 1) := by
  have hr := relation_finrank_eq_residual_piece c F G e t he ht hF hG hgood D hpoints
    (d - q) (β + q) (by omega) hqne hqnt
  have hh := Cylinder.PlanePlateau.quotient_dimension (ResidualIdeal F G D) (β + q)
  rw [ActualIdealCharacter.forms_dimension, ← hr] at hh
  exact hh

theorem first_differences_of_three_sums (H : ℕ → ℕ) (n r c : ℕ) (hrn : r ≤ n)
    (h₀ : H n + triangular (r + 1) = triangular (n + 1) + c)
    (h₁ : H (n + 1) + triangular (r + 2) = triangular (n + 2) + c)
    (h₂ : H (n + 2) + triangular (r + 3) = triangular (n + 3) + c) :
    firstDifference H (n + 1) = n - r ∧ firstDifference H (n + 2) = n - r := by
  have hn₁ : triangular (n + 2) = triangular (n + 1) + n + 2 := by
    rw [show n + 2 = (n + 1) + 1 by omega, triangular]
    omega
  have hn₂ : triangular (n + 3) = triangular (n + 2) + n + 3 := by
    rw [show n + 3 = (n + 2) + 1 by omega, triangular]
    omega
  have hr₁ : triangular (r + 2) = triangular (r + 1) + r + 2 := by
    rw [show r + 2 = (r + 1) + 1 by omega, triangular]
    omega
  have hr₂ : triangular (r + 3) = triangular (r + 2) + r + 3 := by
    rw [show r + 3 = (r + 2) + 1 by omega, triangular]
    omega
  constructor
  · change H (n + 1) - H n = n - r
    omega
  · change H (n + 2) - H (n + 1) = n - r
    omega

theorem actual_residual_first_differences (c : Chart K) (F G : PlaneRing K) (e t d β m : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K)) [Nonempty D]
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (hdegree : (e : ℤ) + t - 3 - d = β) (het : e ≤ t)
    (hm : 0 < m) (hmβ : m ≤ β) (hsmall : 4 * m + 2 < e)
    (hβ : β + 2 * m + 2 ≤ e - 2) (hd : 2 * e ≤ d)
    (hv : ∀ P : D, c.normalizedPoint P.val ≠ 0)
    (hsep : ProjectivelyDistinct (fun P : D => c.normalizedPoint P.val))
    (hs : InitialDegree (fun P : D => c.normalizedPoint P.val) e)
    (u : D → K) (hu : ∀ P, u P ≠ 0)
    (hrel : PowerEvaluationRelation.Relation (fun P : D => c.normalizedPoint P.val) u d)
    (hconn : ∀ i, 0 < i → i < e →
      numericalCharacter (fun P : D => c.normalizedPoint P.val) (i - 1) ≤
        numericalCharacter (fun P : D => c.normalizedPoint P.val) i + 1)
    (hplateau : ∀ r < 4,
      increment (numericalCharacter (fun P : D => c.normalizedPoint P.val)) d (3 * m + r) = m) :
    firstDifference (Cylinder.PlanePlateau.quotientHilbert (ResidualIdeal F G D)) (β + 2 * m + 1) = β - m ∧
      firstDifference (Cylinder.PlanePlateau.quotientHilbert (ResidualIdeal F G D)) (β + 2 * m + 2) = β - m := by
  let v := fun P : D => c.normalizedPoint P.val
  let C := ∑ i ∈ Finset.range (3 * m), (m - increment (numericalCharacter v) d i)
  have hform (q : ℕ) (hq₀ : 2 * m ≤ q) (hq₁ : q ≤ 2 * m + 2) :
      Cylinder.PlanePlateau.quotientHilbert (ResidualIdeal F G D) (β + q) +
        triangular (q + m + 1) = triangular (β + q + 1) + C := by
    have hdim := actual_relation_dimensions v hv hsep e d m hs u hu hrel hm hsmall hd hconn hplateau q hq₀ hq₁
    have hsum := residual_hilbert_and_relation c F G e t d β q he ht hF hG hgood D hpoints
      hdegree (by omega) (by omega) (by omega)
    change finrank K (PlaneRelationSpaces.relationSpace v (d - q)) + C = _ at hdim
    change Cylinder.PlanePlateau.quotientHilbert (ResidualIdeal F G D) (β + q) +
      finrank K (PlaneRelationSpaces.relationSpace v (d - q)) = _ at hsum
    omega
  have h₀ := hform (2 * m) (by omega) (by omega)
  have h₁ := hform (2 * m + 1) (by omega) (by omega)
  have h₂ := hform (2 * m + 2) (by omega) (by omega)
  have ha : 2 * m + m + 1 = 3 * m + 1 := by omega
  have hb : 2 * m + 1 + m + 1 = 3 * m + 2 := by omega
  have hc : 2 * m + 2 + m + 1 = 3 * m + 3 := by omega
  rw [ha] at h₀
  rw [hb, ← Nat.add_assoc] at h₁
  rw [hc, ← Nat.add_assoc] at h₂
  have hh := first_differences_of_three_sums
    (Cylinder.PlanePlateau.quotientHilbert (ResidualIdeal F G D)) (β + 2 * m) (3 * m) C
    (by omega) h₀ h₁ h₂
  have hdiff : β + 2 * m - 3 * m = β - m := by omega
  simpa only [hdiff, Nat.add_assoc] using hh

#print axioms actual_residual_saturated
#print axioms residual_hilbert_and_relation
#print axioms first_differences_of_three_sums
#print axioms actual_residual_first_differences

end Cylinder.LocalResidualHilbert
end
