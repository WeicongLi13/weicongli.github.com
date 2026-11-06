module

public import Cylinder.PlaneLaurentCommonTorus
public import Cylinder.ChartTorusEvaluation

/-! Literal homogeneous Laurent monomials and normalized coordinate
substitution in the actual common torus localization. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentTorusSubstitution

open MvPolynomial Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentChartBasis
open Cylinder.PlaneLaurentTripleBasis Cylinder.CoordinateChartLaurent
open Cylinder.CoordinateLaurentLocalization Cylinder.CommonTorusFractions
open Cylinder.TripleCoordinateLocalization Cylinder.ChartTorusEvaluation
open Cylinder.PlaneLaurentCommonTorus

variable (K : Type*) [Field K]

@[simp] theorem chartExponent_zero (v : ℤ) (m : Fin 2 →₀ ℕ) :
    PlaneLaurentChartBasis.exponentOf v m 0 = v - (m 0 : ℤ) - m 1 := rfl

@[simp] theorem chartExponent_one (v : ℤ) (m : Fin 2 →₀ ℕ) :
    PlaneLaurentChartBasis.exponentOf v m 1 = (m 0 : ℤ) := rfl

@[simp] theorem chartExponent_two (v : ℤ) (m : Fin 2 →₀ ℕ) :
    PlaneLaurentChartBasis.exponentOf v m 2 = (m 1 : ℤ) := rfl

theorem chartPolynomialEquiv_symm_monomial (v : ℤ) (m : Fin 2 →₀ ℕ) (c : K) :
    ((chartPolynomialEquiv v).symm (monomial m c)).val =
      Finsupp.single (PlaneLaurentChartBasis.exponentOf v m) c := by
  change ((Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v {0} a}).symm
    (((Finsupp.domLCongr (PlaneLaurentChartBasis.exponentEquiv v)) : _ ≃ₗ[K] _).symm
      (Finsupp.single m c))).val = _
  rw [Finsupp.domLCongr_symm, Finsupp.domLCongr_single,
    Finsupp.supportedEquivFinsupp_symm_single]
  rfl

theorem tripleLaurentEquiv_single (v : ℤ) (a : Exponent) (ha : Allowed v {0,1,2} a)
    (c : K) (s : piece (K := K) v {0,1,2}) (hs : s.val = Finsupp.single a c) :
    tripleLaurentEquiv v s = AddMonoidAlgebra.single (a 1)
      (AddMonoidAlgebra.single (a 2) c) := by
  ext d n
  rw [tripleLaurentEquiv_coeff, hs]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  have he : a = PlaneLaurentTripleBasis.exponentOf v (d,n) ↔ a 1 = d ∧ a 2 = n := by
    constructor
    · intro h
      exact ⟨congrArg (fun z : Exponent => z 1) h, congrArg (fun z : Exponent => z 2) h⟩
    · rintro ⟨h₁,h₂⟩
      funext i
      have hd : a 0 + a 1 + a 2 = v := ha.1
      fin_cases i
      · change a 0 = v-d-n
        omega
      · exact h₁
      · exact h₂
  by_cases h₁ : a 1 = d <;> by_cases h₂ : a 2 = n <;>
    simp [he, h₁, h₂, -LaurentPolynomial.single_eq_C_mul_T]

theorem overlapToTriple_T (d : ℤ) :
    overlapToTriple K (LaurentPolynomial.T d) = LaurentPolynomial.T d := by
  ext n
  rw [overlapToTriple_coeff]
  by_cases h : d = n <;> simp [h]

theorem overlapToTriple_C (p : coefficientRing K) :
    overlapToTriple K (LaurentPolynomial.C p) =
      LaurentPolynomial.C (Polynomial.toLaurent (MvPolynomial.uniqueAlgEquiv K (Fin 1) p)) := by
  ext n
  rw [overlapToTriple_coeff]
  by_cases h : n = 0 <;> simp [h]

theorem productLaurentEquiv_X_zero :
    productLaurentEquiv K (algebraMap (AffineRing K) (TorusRing K) (X 0)) =
      LaurentPolynomial.T 1 := by
  rw [← firstToProduct_algebraMap, productLaurentEquiv_firstToProduct]
  change overlapToTriple K (Cylinder.CoordinateTwistOverlap.localizationEquiv K
    (algebraMap (AffineRing K) (Cylinder.CoordinateTwistOverlap.affineLocalization K) (X 0))) = _
  rw [Cylinder.CoordinateTwistOverlap.localizationEquiv_algebraMap,
    MvPolynomial.finSuccEquiv_X_zero, Polynomial.toLaurent_X, overlapToTriple_T]

theorem productLaurentEquiv_X_one :
    productLaurentEquiv K (algebraMap (AffineRing K) (TorusRing K) (X 1)) =
      LaurentPolynomial.C (LaurentPolynomial.T 1) := by
  rw [← firstToProduct_algebraMap, productLaurentEquiv_firstToProduct]
  change overlapToTriple K (Cylinder.CoordinateTwistOverlap.localizationEquiv K
    (algebraMap (AffineRing K) (Cylinder.CoordinateTwistOverlap.affineLocalization K) (X 1))) = _
  rw [secondCoordinate_image, overlapToTriple_C]
  simp [MvPolynomial.uniqueAlgEquiv_apply, Polynomial.toLaurent_X]

def tUnit (R : Type*) [CommRing R] : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

theorem tUnit_zpow (R : Type*) [CommRing R] (n : ℤ) :
    ((tUnit R ^ n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = LaurentPolynomial.T n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add, Units.val_mul, ih, zpow_one]
    change (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial R) * LaurentPolynomial.T 1 = _
    rw [← LaurentPolynomial.T_add]
  | pred n ih =>
    rw [zpow_sub, Units.val_mul, ih, zpow_one]
    change (LaurentPolynomial.T (-(n : ℤ)) : LaurentPolynomial R) * LaurentPolynomial.T (-1) = _
    rw [← LaurentPolynomial.T_add]
    congr 1

theorem map_unit_zpow {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u : Aˣ) (n : ℤ) :
    f ((u ^ n : Aˣ) : A) = ((Units.map f.toMonoidHom u ^ n : Bˣ) : B) := by
  exact congrArg Units.val ((Units.map f.toMonoidHom).map_zpow u n)

theorem coordinateUnit_none : coordinateUnit K none = 1 := by
  apply Units.ext
  rw [coordinateUnit_value]
  simp [polynomialMap]

theorem coordinateUnit_image_zero :
    Units.map (productLaurentEquiv K).toRingHom.toMonoidHom (coordinateUnit K (some 0)) =
      tUnit (LaurentPolynomial K) := by
  apply Units.ext
  change productLaurentEquiv K (coordinateUnit K (some 0) : TorusRing K) = _
  rw [coordinateUnit_value]
  simp only [polynomialMap, RingHom.comp_apply, Cylinder.CurvePolarLocal.dehomogenize_X_some]
  exact productLaurentEquiv_X_zero K

theorem coordinateUnit_image_one :
    Units.map (productLaurentEquiv K).toRingHom.toMonoidHom (coordinateUnit K (some 1)) =
      Units.map LaurentPolynomial.C.toMonoidHom (tUnit K) := by
  apply Units.ext
  change productLaurentEquiv K (coordinateUnit K (some 1) : TorusRing K) = _
  rw [coordinateUnit_value]
  simp only [polynomialMap, RingHom.comp_apply, Cylinder.CurvePolarLocal.dehomogenize_X_some]
  exact productLaurentEquiv_X_one K

theorem coordinateUnit_image_zpow_zero (n : ℤ) :
    productLaurentEquiv K ((coordinateUnit K (some 0) ^ n : (TorusRing K)ˣ) : TorusRing K) =
      LaurentPolynomial.T n := by
  change (productLaurentEquiv K).toRingHom
    ((coordinateUnit K (some 0) ^ n : (TorusRing K)ˣ) : TorusRing K) = _
  rw [map_unit_zpow (productLaurentEquiv K).toRingHom, coordinateUnit_image_zero, tUnit_zpow]

theorem coordinateUnit_image_zpow_one (n : ℤ) :
    productLaurentEquiv K ((coordinateUnit K (some 1) ^ n : (TorusRing K)ˣ) : TorusRing K) =
      LaurentPolynomial.C (LaurentPolynomial.T n) := by
  change (productLaurentEquiv K).toRingHom
    ((coordinateUnit K (some 1) ^ n : (TorusRing K)ˣ) : TorusRing K) = _
  rw [map_unit_zpow (productLaurentEquiv K).toRingHom, coordinateUnit_image_one,
    ← map_unit_zpow LaurentPolynomial.C (tUnit K) n, tUnit_zpow]

theorem commonPieceMap_single (v : ℤ) (I : Finset (Fin 3)) (a : Exponent)
    (s : piece (K := K) v I) (hs : s.val = Finsupp.single a (1 : K)) :
    commonPieceMap K v I s =
      ((coordinateUnit K (some 0) ^ (a 1) : (TorusRing K)ˣ) : TorusRing K) *
        ((coordinateUnit K (some 1) ^ (a 2) : (TorusRing K)ˣ) : TorusRing K) := by
  have ha : Allowed v {0,1,2} a := by
    apply (mem_piece_iff v {0,1,2} (fullInclusion K v I s).val).mp
      (fullInclusion K v I s).property a
    change s.val a ≠ 0
    rw [hs, Finsupp.single_eq_same]
    exact one_ne_zero
  apply (productLaurentEquiv K).injective
  change productLaurentEquiv K ((productLaurentEquiv K).symm
    (tripleLaurentEquiv v (fullInclusion K v I s))) = _
  rw [AlgEquiv.apply_symm_apply,
    tripleLaurentEquiv_single K v a ha 1 (fullInclusion K v I s) hs,
    map_mul, coordinateUnit_image_zpow_zero, coordinateUnit_image_zpow_one]
  simp only [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
  exact mul_comm _ _

theorem chartPiecePermutation_monomial (v : ℤ) (i : Cylinder.CoordinateChartPermutation.Index)
    (m : Fin 2 →₀ ℕ) :
    (chartPiecePermutation K v i ((chartPolynomialEquiv v).symm (monomial m (1 : K)))).val =
      Finsupp.single (Cylinder.PlaneLaurentPermutation.exponentEquiv (chartPermutation i)
        (PlaneLaurentChartBasis.exponentOf v m)) (1 : K) := by
  change Cylinder.PlaneLaurentPermutation.laurentEquiv (chartPermutation i)
    ((chartPolynomialEquiv v).symm (monomial m (1 : K))).val = _
  rw [chartPolynomialEquiv_symm_monomial]
  exact Finsupp.domLCongr_single _ _ _

theorem unit_identity_first {A : Type*} [CommRing A] (x y : Aˣ) (v : ℤ) (m n : ℕ) :
    x ^ (v - (m : ℤ) - n) * y ^ n = x ^ v * ((x⁻¹) ^ m * (x⁻¹ * y) ^ n) := by
  simp only [zpow_sub, zpow_natCast, mul_pow, inv_pow]
  ac_rfl

theorem unit_identity_second {A : Type*} [CommRing A] (x y : Aˣ) (v : ℤ) (m n : ℕ) :
    x ^ m * y ^ (v - (m : ℤ) - n) = y ^ v * ((y⁻¹ * x) ^ m * (y⁻¹) ^ n) := by
  simp only [zpow_sub, zpow_natCast, mul_pow, inv_pow]
  ac_rfl

theorem chartPolynomialMap_monomial (i : Cylinder.CoordinateChartPermutation.Index)
    (m : Fin 2 →₀ ℕ) (c : K) :
    chartPolynomialMap K i (monomial m c) = algebraMap K (TorusRing K) c *
      (normalizedValues K i 0 ^ m 0 * normalizedValues K i 1 ^ m 1) := by
  change eval₂ _ _ (monomial m c) = _
  rw [eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]

theorem commonPieceMap_chartMonomial (v : ℤ) (i : Cylinder.CoordinateChartPermutation.Index)
    (m : Fin 2 →₀ ℕ) :
    commonPieceMap K v {coordinateNumber i}
      (chartPiecePermutation K v i ((chartPolynomialEquiv v).symm (monomial m (1 : K)))) =
        ((coordinateUnit K i ^ v : (TorusRing K)ˣ) : TorusRing K) *
          chartPolynomialMap K i (monomial m (1 : K)) := by
  rw [commonPieceMap_single K v {coordinateNumber i} _ _
    (chartPiecePermutation_monomial K v i m), chartPolynomialMap_monomial, map_one, one_mul]
  have h₀ := coordinateUnit_value K (some 0)
  have h₁ := coordinateUnit_value K (some 1)
  have hn := coordinateUnit_value K none
  cases i with
  | none =>
    simp [chartPermutation, coordinateNumber, Cylinder.PlaneLaurentPermutation.exponentEquiv,
      normalizedValues, coordinateUnit_none, ← h₀, ← h₁]
  | some i =>
    fin_cases i
    · simpa [chartPermutation, coordinateNumber, Cylinder.PlaneLaurentPermutation.exponentEquiv,
        normalizedValues, ← h₀, ← h₁, ← hn,
        coordinateUnit_none, Equiv.swap_apply_def,
        Units.val_pow_eq_pow_val, Units.val_mul, zpow_natCast]
        using congrArg Units.val (unit_identity_first (coordinateUnit K (some 0))
          (coordinateUnit K (some 1)) v (m 0) (m 1))
    · simpa [chartPermutation, coordinateNumber, Cylinder.PlaneLaurentPermutation.exponentEquiv,
        normalizedValues, ← h₀, ← h₁, ← hn,
        coordinateUnit_none, Equiv.swap_apply_def,
        Units.val_pow_eq_pow_val, Units.val_mul, zpow_natCast]
        using congrArg Units.val (unit_identity_second (coordinateUnit K (some 0))
          (coordinateUnit K (some 1)) v (m 0) (m 1))

theorem chartPolynomialMap_smul (i : Cylinder.CoordinateChartPermutation.Index)
    (c : K) (f : AffineRing K) :
    chartPolynomialMap K i (c • f) = c • chartPolynomialMap K i f := by
  change eval₂ _ _ (c • f) = _
  rw [MvPolynomial.smul_eq_C_mul, eval₂_mul, eval₂_C]
  exact (Algebra.smul_def c _).symm

theorem commonPieceMap_chartPolynomial (v : ℤ) (i : Cylinder.CoordinateChartPermutation.Index)
    (f : AffineRing K) :
    commonPieceMap K v {coordinateNumber i}
      (chartPiecePermutation K v i ((chartPolynomialEquiv v).symm f)) =
        ((coordinateUnit K i ^ v : (TorusRing K)ˣ) : TorusRing K) *
          chartPolynomialMap K i f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    have hc : monomial m c = c • monomial m (1 : K) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, map_smul, commonPieceMap_chartMonomial,
      chartPolynomialMap_smul, mul_smul_comm]
  | add f g hf hg =>
    simp only [map_add, hf, hg, mul_add]

end Cylinder.PlaneLaurentTorusSubstitution

end
