module

public import Cylinder.PlaneLaurentTorusSubstitution
public import Cylinder.PlaneLaurentFractionPieces
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Actual exponent translation is multiplication by the corresponding
coordinate unit in the same torus localization. Literal homogeneous
polynomial fractions therefore have their original numerator and denominator. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.PlaneLaurentTorusFractions

open MvPolynomial Module Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentTripleBasis
open Cylinder.PlaneLaurentCommonTorus Cylinder.PlaneLaurentTorusSubstitution
open Cylinder.PlaneLaurentDenominatorClearing Cylinder.PlaneLaurentFractionPieces
open Cylinder.PlaneLaurentHomogeneous Cylinder.CommonTorusFractions
open Cylinder.TripleCoordinateLocalization Cylinder.ChartTorusEvaluation
open Cylinder.CoordinateChartLaurent Cylinder.CoordinateLaurentLocalization

variable (K : Type*) [Field K]

theorem commonPieceMap_shift (v w : ℤ) (I J : Finset (Fin 3)) (b : Exponent)
    (f : piece (K := K) v I) (g : piece (K := K) w J)
    (hw : w = v + totalDegree b) (hg : g.val = shift b f.val) :
    commonPieceMap K w J g =
      (((coordinateUnit K (some 0) ^ (b 1) : (TorusRing K)ˣ) : TorusRing K) *
        ((coordinateUnit K (some 1) ^ (b 2) : (TorusRing K)ˣ) : TorusRing K)) *
          commonPieceMap K v I f := by
  apply (productLaurentEquiv K).injective
  change productLaurentEquiv K ((productLaurentEquiv K).symm
    (tripleLaurentEquiv w (fullInclusion K w J g))) =
      productLaurentEquiv K ((_ * _) * (productLaurentEquiv K).symm
        (tripleLaurentEquiv v (fullInclusion K v I f)))
  rw [AlgEquiv.apply_symm_apply, map_mul, map_mul,
    coordinateUnit_image_zpow_zero, coordinateUnit_image_zpow_one, AlgEquiv.apply_symm_apply]
  have hm : (LaurentPolynomial.T (b 1) : tripleRing K) * LaurentPolynomial.C
      (LaurentPolynomial.T (b 2)) =
      AddMonoidAlgebra.single (b 1) (LaurentPolynomial.T (b 2) : LaurentPolynomial K) := by
    rw [LaurentPolynomial.single_eq_C_mul_T]
    exact mul_comm _ _
  rw [hm]
  ext d n
  rw [tripleLaurentEquiv_coeff]
  change g.val (PlaneLaurentTripleBasis.exponentOf w (d,n)) = _
  rw [hg, shift_coeff]
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, LaurentPolynomial.T, one_mul]
  rw [tripleLaurentEquiv_coeff]
  congr 1
  funext i
  fin_cases i <;>
    simp [PlaneLaurentTripleBasis.exponentOf, PlaneLaurentPieces.totalDegree, hw] <;> ring

def polynomialMapLinear : PlaneRing K →ₗ[K] TorusRing K where
  toFun := polynomialMap K
  map_add' := (polynomialMap K).map_add
  map_smul' c H := by
    rw [polynomialMap_eval₂, polynomialMap_eval₂]
    rw [MvPolynomial.smul_eq_C_mul, eval₂_mul, eval₂_C]
    exact (Algebra.smul_def c _).symm

theorem commonPieceMap_polynomial (v : ℤ) (f : piece (K := K) v ∅) :
    commonPieceMap K v ∅ f = polynomialMap K ((globalPieceEquivForms K v f).val) := by
  let b : Basis {a : Exponent // Allowed v ∅ a} K (piece (K := K) v ∅) :=
    (Finsupp.basisSingleOne).map
      (Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v ∅ a}).symm
  let rhs : piece (K := K) v ∅ →ₗ[K] TorusRing K :=
    (polynomialMapLinear K).comp
      ((integerForms K v).subtype.comp (globalPieceEquivForms K v).toLinearMap)
  suffices he : commonPieceMap K v ∅ = rhs by
    exact congrArg (fun L : piece (K := K) v ∅ →ₗ[K] TorusRing K => L f) he
  apply b.ext
  intro a
  have hb : (b a).val = Finsupp.single a.val (1 : K) := by
    exact Finsupp.supportedEquivFinsupp_symm_single _ a 1
  have hba : (Finsupp.supportedEquivFinsupp (M := K) (R := K)
      {a | Allowed v ∅ a}) (b a) = Finsupp.single a (1 : K) := by
    change (Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v ∅ a})
      ((Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v ∅ a}).symm
        (Finsupp.single a (1 : K))) = _
    exact LinearEquiv.apply_symm_apply _ _
  have hpoly : (globalPieceEquivForms K v (b a)).val =
      monomial (naturalExponent a.val) (1 : K) := by
    change ((AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {m : Monomial | (m.degree : ℤ) = v}).symm
        ((Finsupp.domLCongr (PlaneLaurentHomogeneous.exponentEquiv v))
          ((Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v ∅ a}) (b a)))).val = _
    rw [hba, Finsupp.domLCongr_single]
    apply AddMonoidAlgebra.coeff_injective
    change ((Finsupp.supportedEquivFinsupp (M := K) (R := K)
      {m : Monomial | (m.degree : ℤ) = v}).symm
        (Finsupp.single (PlaneLaurentHomogeneous.exponentEquiv v a) (1 : K))).val = _
    rw [Finsupp.supportedEquivFinsupp_symm_single]
    rfl
  change commonPieceMap K v ∅ (b a) =
    polynomialMap K ((globalPieceEquivForms K v (b a)).val)
  rw [commonPieceMap_single K v ∅ a.val (b a) hb, hpoly, polynomialMap_eval₂,
    eval₂_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_option, Fin.prod_univ_two]
  have hn₁ : 0 ≤ a.val 1 := a.property.2 1 (by simp)
  have hn₂ : 0 ≤ a.val 2 := a.property.2 2 (by simp)
  simp only [← coordinateUnit_value, coordinateUnit_none, Units.val_one, one_pow, one_mul]
  change _ = (coordinateUnit K (some 0) : TorusRing K) ^ (a.val 1).toNat *
    (coordinateUnit K (some 1) : TorusRing K) ^ (a.val 2).toNat
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    ← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg hn₁, Int.toNat_of_nonneg hn₂]

theorem negativeDenominator_vector_units {G : Type*} [CommGroup G] (x y : G)
    (i j : Fin 3) (a b : ℕ) :
    x ^ (negativeDenominator i j a b 1) * y ^ (negativeDenominator i j a b 2) =
      ![1,x,y] i ^ (-(a : ℤ)) * ![1,x,y] j ^ (-(b : ℤ)) := by
  fin_cases i <;> fin_cases j <;>
    simp [negativeDenominator, zpow_sub, zpow_neg, mul_comm]

theorem coordinateUnit_as_vector (i : Cylinder.CoordinateChartPermutation.Index) :
    coordinateUnit K i = ![1, coordinateUnit K (some 0), coordinateUnit K (some 1)]
      (coordinateNumber i) := by
  cases i with
  | none => simpa [coordinateNumber] using coordinateUnit_none K
  | some i => fin_cases i <;> rfl

theorem negativeDenominator_units (i j : Cylinder.CoordinateChartPermutation.Index) (a b : ℕ) :
    coordinateUnit K (some 0) ^
        (negativeDenominator (coordinateNumber i) (coordinateNumber j) a b 1) *
      coordinateUnit K (some 1) ^
        (negativeDenominator (coordinateNumber i) (coordinateNumber j) a b 2) =
      coordinateUnit K i ^ (-(a : ℤ)) * coordinateUnit K j ^ (-(b : ℤ)) := by
  rw [coordinateUnit_as_vector K i, coordinateUnit_as_vector K j]
  exact negativeDenominator_vector_units (coordinateUnit K (some 0))
    (coordinateUnit K (some 1)) (coordinateNumber i) (coordinateNumber j) a b

theorem commonPieceMap_fractionPiece (d : ℤ)
    (i j : Cylinder.CoordinateChartPermutation.Index) (a b : ℕ)
    (f : piece (K := K) d ∅) :
    commonPieceMap K (d - a - b) {coordinateNumber i, coordinateNumber j}
      (fractionPiece d (coordinateNumber i) (coordinateNumber j) a b f) =
      ((coordinateUnit K i ^ (-(a : ℤ)) * coordinateUnit K j ^ (-(b : ℤ)) : (TorusRing K)ˣ) :
        TorusRing K) * polynomialMap K (globalPieceEquivForms K d f).val := by
  rw [commonPieceMap_shift K d (d-a-b) ∅ {coordinateNumber i, coordinateNumber j}
    (negativeDenominator (coordinateNumber i) (coordinateNumber j) a b) f _
      (by rw [negativeDenominator_degree]; ring) rfl]
  rw [← Units.val_mul, negativeDenominator_units, commonPieceMap_polynomial]

theorem commonPieceMap_polynomialFractionPiece (d a b : ℕ)
    (i j : Cylinder.CoordinateChartPermutation.Index)
    (H : PlaneRing K) (hH : H.IsHomogeneous d) :
    commonPieceMap K ((d : ℤ) - a - b) {coordinateNumber i, coordinateNumber j}
      (polynomialFractionPiece d a b (coordinateNumber i) (coordinateNumber j) H hH) =
      ((coordinateUnit K i ^ (-(a : ℤ)) * coordinateUnit K j ^ (-(b : ℤ)) : (TorusRing K)ˣ) :
        TorusRing K) * polynomialMap K H := by
  rw [polynomialFractionPiece, commonPieceMap_fractionPiece]
  congr 2
  exact congrArg Subtype.val ((globalPieceEquivForms K (d : ℤ)).apply_symm_apply _)

end Cylinder.PlaneLaurentTorusFractions

end
