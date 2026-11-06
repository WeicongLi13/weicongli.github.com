module

public import Cylinder.PlanePlateau
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Actual specialization of coprime plane systems

The results in this file derive nonvanishing of an actual resultant from
relative primality. No generic-line gcd preservation is assumed.
-/

@[expose] public section
noncomputable section

namespace Cylinder.GenericPlaneLine
open scoped Polynomial

section FractionField
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    [IsIntegrallyClosed R]
variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- Monicity permits actual common divisors over the fraction field to descend.
Thus relatively prime integral polynomials remain coprime there. -/
theorem fraction_coprime_of_monic {f g : R[X]} (hf : f.Monic)
    (hfg : IsRelPrime f g) :
    IsCoprime (f.map (algebraMap R F)) (g.map (algebraMap R F)) := by
  classical
  apply IsRelPrime.isCoprime
  intro d hdf hdg
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (hf.map (algebraMap R F)).ne_zero hdf
  have hdn : (normalize d).Monic := monic_normalize hd0
  have hdnf : normalize d ∣ f.map (algebraMap R F) := normalize_dvd_iff.mpr hdf
  have hdng : normalize d ∣ g.map (algebraMap R F) := normalize_dvd_iff.mpr hdg
  obtain ⟨D, hD⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F hf hdnf
  rw [hdn.leadingCoeff, C_1, mul_one] at hD
  have hDm : D.Monic := by
    apply (IsFractionRing.injective R F).monic_map_iff.mpr
    rw [hD]
    exact hdn
  have hDf : D ∣ f := hDm.isPrimitive.dvd_of_fraction_map_dvd_fraction_map (by rwa [hD])
  have hDg : D ∣ g := hDm.isPrimitive.dvd_of_fraction_map_dvd_fraction_map (by rwa [hD])
  have hunit : IsUnit (normalize d) := by
    rw [← hD]
    exact (hfg hDf hDg).map (Polynomial.mapRingHom (algebraMap R F))
  exact (associated_normalize d).isUnit_iff.mpr hunit

include F in
/-- The resultant used to select a line is nonzero because the two actual
polynomials have no nonunit common divisor. -/
theorem resultant_ne_zero_of_monic {f g : R[X]} (hf : f.Monic)
    (hfg : IsRelPrime f g) : f.resultant g ≠ 0 := by
  have hc := fraction_coprime_of_monic F hf hfg
  have hn : (f.map (algebraMap R F)).resultant (g.map (algebraMap R F)) ≠ 0 := by
    intro hz
    exact (resultant_eq_zero_iff.mp hz).2 hc
  have he : (f.map (algebraMap R F)).resultant (g.map (algebraMap R F)) =
      algebraMap R F (f.resultant g) := by
    simp only [natDegree_map_eq_of_injective (IsFractionRing.injective R F),
      resultant_map_map]
  intro hz
  apply hn
  rw [he, hz, map_zero]

end FractionField

section Specialization
open Polynomial
variable {R K : Type*} [CommRing R] [Field K]

/-- Nonvanishing of the actual integral resultant produces a Bezout identity
after coefficient specialization; degrees need not be preserved. -/
theorem specialization_coprime {f g : R[X]} (hf : f.Monic) (φ : R →+* K)
    (hr : φ (f.resultant g) ≠ 0) : IsCoprime (f.map φ) (g.map φ) := by
  by_cases hdeg : f.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hf hdeg
    simpa only [Polynomial.map_one] using (isCoprime_one_left : IsCoprime 1 (g.map φ))
  obtain ⟨p, q, _, _, he⟩ := exists_mul_add_mul_eq_C_resultant
    f g le_rfl le_rfl (Or.inl hdeg)
  have hmap : f.map φ * p.map φ + g.map φ * q.map φ = C (φ (f.resultant g)) := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
      using congrArg (Polynomial.map φ) he
  refine ⟨C (φ (f.resultant g))⁻¹ * p.map φ,
    C (φ (f.resultant g))⁻¹ * q.map φ, ?_⟩
  calc
    _ = C (φ (f.resultant g))⁻¹ * (f.map φ * p.map φ + g.map φ * q.map φ) := by ring
    _ = 1 := by rw [hmap, ← C_mul, inv_mul_cancel₀ hr, C_1]

end Specialization

section MvSpecialization
variable {K σ : Type*} [Field K] [Infinite K]

/-- An actual nonzero parameter polynomial has a nonvanishing evaluation. -/
theorem exists_eval_ne_zero (P : MvPolynomial σ K) (hP : P ≠ 0) :
    ∃ w : σ → K, MvPolynomial.eval w P ≠ 0 := by
  by_contra! h
  apply hP
  apply MvPolynomial.funext
  intro w
  simpa using h w

/-- Coprime polynomials in a monic coordinate admit an actual specialization
that preserves coprimality and avoids a prescribed nonzero parameter equation. -/
theorem exists_specialization_coprime
    (f g : (MvPolynomial σ K)[X]) (hf : f.Monic) (hfg : IsRelPrime f g)
    (A : MvPolynomial σ K) (hA : A ≠ 0) :
    ∃ w : σ → K, MvPolynomial.eval w A ≠ 0 ∧
      IsCoprime (f.map (MvPolynomial.eval w)) (g.map (MvPolynomial.eval w)) := by
  have hr : f.resultant g ≠ 0 :=
    resultant_ne_zero_of_monic (FractionRing (MvPolynomial σ K)) hf hfg
  obtain ⟨w, hw⟩ := exists_eval_ne_zero (f.resultant g * A) (mul_ne_zero hr hA)
  rw [map_mul, mul_ne_zero_iff] at hw
  exact ⟨w, hw.2, specialization_coprime hf (MvPolynomial.eval w) hw.1⟩

end MvSpecialization

section BinaryCoprimality
open Polynomial
variable {K : Type*} [Field K]
open Cylinder.BinaryHomogenization

/-- A Bezout identity on the affine chart, together with actual nonvanishing
at the point at infinity, rules out every common homogeneous factor. -/
theorem binary_relPrime_of_dehomogenize_coprime
    (F G : MvPolynomial (Fin 2) K) (m n : ℕ)
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hinf : MvPolynomial.eval ![1, 0] F ≠ 0)
    (hc : IsCoprime (dehomogenize F) (dehomogenize G)) : IsRelPrime F G := by
  obtain ⟨a, b, hab⟩ := hc
  let N := a.natDegree + m + b.natDegree + n
  have hm : m ≤ N := by dsimp [N]; omega
  have hn : n ≤ N := by dsimp [N]; omega
  have ham : a.natDegree ≤ N - m := by dsimp [N]; omega
  have hbn : b.natDegree ≤ N - n := by dsimp [N]; omega
  have hfrec : homogenize (dehomogenize F) m = F :=
    homogenize_eq_of_isHomogeneous hF rfl
  have hgrec : homogenize (dehomogenize G) n = G :=
    homogenize_eq_of_isHomogeneous hG rfl
  have ha : homogenize (a * dehomogenize F) N = homogenize a (N - m) * F := by
    have h := homogenize_mul a (dehomogenize F) ham (dehomogenize_natDegree_le hF)
    rw [Nat.sub_add_cancel hm, hfrec] at h
    exact h
  have hb : homogenize (b * dehomogenize G) N = homogenize b (N - n) * G := by
    have h := homogenize_mul b (dehomogenize G) hbn (dehomogenize_natDegree_le hG)
    rw [Nat.sub_add_cancel hn, hgrec] at h
    exact h
  have hbezout : homogenize a (N - m) * F + homogenize b (N - n) * G =
      MvPolynomial.X 1 ^ N := by
    simpa only [homogenize_add, ha, hb, homogenize_one]
      using congrArg (fun P : K[X] => homogenize P N) hab
  have hyF : IsRelPrime (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) F := by
    apply MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd.mpr
    rintro ⟨Q, hQ⟩
    apply hinf
    rw [hQ, map_mul]
    simp
  intro D hDF hDG
  have hDy : D ∣ MvPolynomial.X 1 ^ N := by
    rw [← hbezout]
    exact dvd_add (dvd_mul_of_dvd_right hDF _) (dvd_mul_of_dvd_right hDG _)
  exact (hyF.symm.of_dvd_left hDF).pow_right dvd_rfl hDy

end BinaryCoprimality

section PlaneCoordinates
variable {K : Type*} [Field K]
open MvPolynomial
open Cylinder.HilbertEvaluation

/-- A concrete invertible triangular coordinate substitution. -/
def triangularMap (p : Fin 3 → K) : PlaneRing K →ₐ[K] PlaneRing K :=
  MvPolynomial.aeval ![C (p 0) * X 0, X 1 + C (p 1) * X 0, X 2 + C (p 2) * X 0]

def triangularInverseParameters (p : Fin 3 → K) : Fin 3 → K :=
  ![(p 0)⁻¹, -(p 1) * (p 0)⁻¹, -(p 2) * (p 0)⁻¹]

@[simp] theorem triangularMap_X (p : Fin 3 → K) (i : Fin 3) :
    triangularMap p (X i) =
      ![C (p 0) * X 0, X 1 + C (p 1) * X 0, X 2 + C (p 2) * X 0] i := by
  simp [triangularMap]

@[simp] theorem triangularMap_C (p : Fin 3 → K) (c : K) :
    triangularMap p (C c) = C c := (triangularMap p).commutes c

theorem triangularMap_X_zero (p : Fin 3 → K) : triangularMap p (X 0) = C (p 0) * X 0 := by simp
theorem triangularMap_X_one (p : Fin 3 → K) : triangularMap p (X 1) = X 1 + C (p 1) * X 0 := by simp
theorem triangularMap_X_two (p : Fin 3 → K) : triangularMap p (X 2) = X 2 + C (p 2) * X 0 := by simp

theorem triangular_inverse_left (p : Fin 3 → K) (hp : p 0 ≠ 0) :
    (triangularMap (triangularInverseParameters p)).comp (triangularMap p) =
      AlgHom.id K (PlaneRing K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  fin_cases i
  · change triangularMap (triangularInverseParameters p) (triangularMap p (X (0 : Fin 3))) = X 0
    rw [triangularMap_X_zero, map_mul, triangularMap_C, triangularMap_X_zero]
    change C (p 0) * (C (p 0)⁻¹ * X 0) = X 0
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hp, C_1, one_mul]
  · change triangularMap (triangularInverseParameters p) (triangularMap p (X (1 : Fin 3))) = X 1
    rw [triangularMap_X_one, map_add, triangularMap_X_one, map_mul,
      triangularMap_C, triangularMap_X_zero]
    change X 1 + C (-(p 1) * (p 0)⁻¹) * X 0 + C (p 1) * (C (p 0)⁻¹ * X 0) = X 1
    simp only [C_mul, C_neg]
    ring
  · change triangularMap (triangularInverseParameters p) (triangularMap p (X (2 : Fin 3))) = X 2
    rw [triangularMap_X_two, map_add, triangularMap_X_two, map_mul,
      triangularMap_C, triangularMap_X_zero]
    change X 2 + C (-(p 2) * (p 0)⁻¹) * X 0 + C (p 2) * (C (p 0)⁻¹ * X 0) = X 2
    simp only [C_mul, C_neg]
    ring

theorem triangular_inverse_right (p : Fin 3 → K) (hp : p 0 ≠ 0) :
    (triangularMap p).comp (triangularMap (triangularInverseParameters p)) =
      AlgHom.id K (PlaneRing K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  fin_cases i
  · change triangularMap p (triangularMap (triangularInverseParameters p) (X (0 : Fin 3))) = X 0
    rw [triangularMap_X_zero, map_mul, triangularMap_C, triangularMap_X_zero]
    change C (p 0)⁻¹ * (C (p 0) * X 0) = X 0
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hp, C_1, one_mul]
  · change triangularMap p (triangularMap (triangularInverseParameters p) (X (1 : Fin 3))) = X 1
    rw [triangularMap_X_one, map_add, triangularMap_X_one, map_mul,
      triangularMap_C, triangularMap_X_zero]
    change X 1 + C (p 1) * X 0 + C (-(p 1) * (p 0)⁻¹) * (C (p 0) * X 0) = X 1
    rw [← mul_assoc, ← C_mul]
    have hs : -(p 1) * (p 0)⁻¹ * p 0 = -(p 1) := by rw [mul_assoc, inv_mul_cancel₀ hp, mul_one]
    rw [hs, C_neg]
    ring
  · change triangularMap p (triangularMap (triangularInverseParameters p) (X (2 : Fin 3))) = X 2
    rw [triangularMap_X_two, map_add, triangularMap_X_two, map_mul,
      triangularMap_C, triangularMap_X_zero]
    change X 2 + C (p 2) * X 0 + C (-(p 2) * (p 0)⁻¹) * (C (p 0) * X 0) = X 2
    rw [← mul_assoc, ← C_mul]
    have hs : -(p 2) * (p 0)⁻¹ * p 0 = -(p 2) := by rw [mul_assoc, inv_mul_cancel₀ hp, mul_one]
    rw [hs, C_neg]
    ring

/-- The change of coordinates is an actual algebra equivalence. -/
def triangularEquiv (p : Fin 3 → K) (hp : p 0 ≠ 0) : PlaneRing K ≃ₐ[K] PlaneRing K where
  toFun := triangularMap p
  invFun := triangularMap (triangularInverseParameters p)
  left_inv P := AlgHom.congr_fun (triangular_inverse_left p hp) P
  right_inv P := AlgHom.congr_fun (triangular_inverse_right p hp) P
  map_mul' := map_mul (triangularMap p)
  map_add' := map_add (triangularMap p)
  commutes' := (triangularMap p).commutes

theorem triangularMap_homogeneous (p : Fin 3 → K) (F : PlaneRing K) (d : ℕ)
    (hF : F.IsHomogeneous d) : (triangularMap p F).IsHomogeneous d := by
  have hlinear (i : Fin 3) :
      (![C (p 0) * X 0, X 1 + C (p 1) * X 0, X 2 + C (p 2) * X 0] i : PlaneRing K).IsHomogeneous 1 := by
    fin_cases i
    · simpa using (isHomogeneous_C (Fin 3) (p 0)).mul (isHomogeneous_X K 0)
    · exact (isHomogeneous_X K 1).add (by simpa using (isHomogeneous_C (Fin 3) (p 1)).mul (isHomogeneous_X K 0))
    · exact (isHomogeneous_X K 2).add (by simpa using (isHomogeneous_C (Fin 3) (p 2)).mul (isHomogeneous_X K 0))
  simpa only [triangularMap, one_mul] using hF.aeval _ hlinear

theorem triangularMap_eval_origin (p : Fin 3 → K) (F : PlaneRing K) :
    eval (Fin.cons 1 0) (triangularMap p F) = eval p F := by
  have he : (eval (Fin.cons 1 0)).comp (triangularMap p).toRingHom = eval p := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [triangularMap]
    · intro i
      fin_cases i <;> simp [triangularMap]
      rfl
  exact RingHom.congr_fun he F

theorem exists_triangular_nonvanishing [Infinite K] (F : PlaneRing K) (hF : F ≠ 0) :
    ∃ p : Fin 3 → K, p 0 ≠ 0 ∧ eval (Fin.cons 1 0) (triangularMap p F) ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_eval_ne_zero (F * X (0 : Fin 3)) (mul_ne_zero hF (X_ne_zero _))
  rw [map_mul, eval_X, mul_ne_zero_iff] at hp
  exact ⟨p, hp.2, by rw [triangularMap_eval_origin]; exact hp.1⟩

end PlaneCoordinates

section PencilRestriction
variable {K : Type*} [Field K]
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.BinaryHomogenization

/-- The actual restriction to a line of the pencil through the coordinate point e0. -/
def pencilRestriction (w : Fin 2 → K) : PlaneRing K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval ![X 0, C (w 0) * X 1, C (w 1) * X 1]

@[simp] theorem pencilRestriction_X (w : Fin 2 → K) (i : Fin 3) :
    pencilRestriction w (X i) = ![X 0, C (w 0) * X 1, C (w 1) * X 1] i := by
  simp [pencilRestriction]

@[simp] theorem pencilRestriction_C (w : Fin 2 → K) (c : K) :
    pencilRestriction w (C c) = C c := (pencilRestriction w).commutes c

theorem pencilRestriction_surjective (w : Fin 2 → K) (hw : w 0 ≠ 0) :
    Function.Surjective (pencilRestriction w) := by
  let R : MvPolynomial (Fin 2) K →ₐ[K] PlaneRing K :=
    MvPolynomial.aeval ![X 0, C (w 0)⁻¹ * X 1]
  have he : (pencilRestriction w).comp R = AlgHom.id K (MvPolynomial (Fin 2) K) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [R]
    · change pencilRestriction w (R (X 1)) = X 1
      simp only [R, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [map_mul, pencilRestriction_C, pencilRestriction_X]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hw, C_1, one_mul]
  intro P
  exact ⟨R P, AlgHom.congr_fun he P⟩

theorem pencilRestriction_homogeneous (w : Fin 2 → K) (F : PlaneRing K) (d : ℕ)
    (hF : F.IsHomogeneous d) : (pencilRestriction w F).IsHomogeneous d := by
  have hlinear (i : Fin 3) :
      (![X 0, C (w 0) * X 1, C (w 1) * X 1] i : MvPolynomial (Fin 2) K).IsHomogeneous 1 := by
    fin_cases i
    · exact isHomogeneous_X K 0
    · simpa using (isHomogeneous_C (Fin 2) (w 0)).mul (isHomogeneous_X K 1)
    · simpa using (isHomogeneous_C (Fin 2) (w 1)).mul (isHomogeneous_X K 1)
  simpa only [pencilRestriction, one_mul] using hF.aeval _ hlinear

theorem pencil_dehomogenize (w : Fin 2 → K) (F : PlaneRing K) :
    dehomogenize (pencilRestriction w F) =
      (MvPolynomial.finSuccEquiv K 2 F).map (MvPolynomial.eval w) := by
  have he : dehomogenize.toRingHom.comp (pencilRestriction w).toRingHom =
      (Polynomial.mapRingHom (MvPolynomial.eval w)).comp
        (MvPolynomial.finSuccEquiv K 2).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [pencilRestriction, dehomogenize, MvPolynomial.finSuccEquiv_apply]
    · intro i
      have h1 : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X (1 : Fin 3)) =
          Polynomial.C (MvPolynomial.X (0 : Fin 2)) :=
        MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2) (j := 0)
      have h2 : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X (2 : Fin 3)) =
          Polynomial.C (MvPolynomial.X (1 : Fin 2)) :=
        MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2) (j := 1)
      fin_cases i <;> simp [pencilRestriction, dehomogenize,
        MvPolynomial.finSuccEquiv_X_zero, h1, h2]
  exact RingHom.congr_fun he F

theorem pencil_eval_infinity (w : Fin 2 → K) (F : PlaneRing K) :
    eval ![1, 0] (pencilRestriction w F) = eval (Fin.cons 1 0) F := by
  have he : (eval ![1, 0]).comp (pencilRestriction w).toRingHom =
      eval (Fin.cons 1 0) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [pencilRestriction]
    · intro i
      fin_cases i <;> simp [pencilRestriction]
      rfl
  exact RingHom.congr_fun he F

theorem nested_natDegree_le (F : PlaneRing K) (d : ℕ) (hF : F.IsHomogeneous d) :
    (MvPolynomial.finSuccEquiv K 2 F).natDegree ≤ d := by
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree F 0).trans hF.totalDegree_le

/-- The top coefficient in the first coordinate is precisely evaluation at e0. -/
theorem nested_top_coefficient (F : PlaneRing K) (d : ℕ) (hF : F.IsHomogeneous d) :
    (MvPolynomial.finSuccEquiv K 2 F).coeff d = C (eval (Fin.cons 1 0) F) := by
  have htop : ((MvPolynomial.finSuccEquiv K 2 F).coeff d).totalDegree = 0 := by
    exact Nat.eq_zero_of_le_zero (hF.finSuccEquiv_coeff_isHomogeneous d 0 (by omega)).totalDegree_le
  have hc := totalDegree_eq_zero_iff_eq_C.mp htop
  have aux : ∀ i ∈ Finset.range d,
      constantCoeff ((MvPolynomial.finSuccEquiv K 2 F).coeff i) = 0 := by
    intro i hi
    have hid : i < d := Finset.mem_range.mp hi
    apply (hF.finSuccEquiv_coeff_isHomogeneous i (d - i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    omega
  have hdeg : (MvPolynomial.finSuccEquiv K 2 F).natDegree < d + 1 :=
    Nat.lt_succ_of_le (nested_natDegree_le F d hF)
  have heval : eval (Fin.cons 1 0) F = constantCoeff ((MvPolynomial.finSuccEquiv K 2 F).coeff d) := by
    simp_rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map, Polynomial.eval_eq_sum_range' hdeg,
      eval_zero, one_pow, mul_one, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]
  rw [hc]
  exact congrArg C heval.symm

end PencilRestriction

section CoprimePlaneLine
variable {K : Type*} [Field K]
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.BinaryHomogenization

/-- Ring equivalences preserve actual relative primality. -/
theorem relPrime_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) {f g : A} (h : IsRelPrime f g) : IsRelPrime (e f) (e g) := by
  intro D hDf hDg
  have hf : e.symm D ∣ f := by
    apply (map_dvd_iff e).mp
    simpa using hDf
  have hg : e.symm D ∣ g := by
    apply (map_dvd_iff e).mp
    simpa using hDg
  have hu := (h hf hg).map e.toMonoidHom
  simpa using hu

/-- Once the coordinate point is outside the first curve, an actual line of
its pencil preserves coprimality of the two homogeneous forms. -/
theorem exists_coprime_pencil [Infinite K]
    (F G : PlaneRing K) (m n : ℕ) (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hinf : eval (Fin.cons 1 0) F ≠ 0) (hfg : IsRelPrime F G)
    (A : MvPolynomial (Fin 2) K) (hA : A ≠ 0) :
    ∃ w : Fin 2 → K, w 0 ≠ 0 ∧ eval w A ≠ 0 ∧
      IsRelPrime (pencilRestriction w F) (pencilRestriction w G) := by
  let f := MvPolynomial.finSuccEquiv K 2 F
  let g := MvPolynomial.finSuccEquiv K 2 G
  let c := eval (Fin.cons 1 0) F
  let f' := Polynomial.C (MvPolynomial.C c⁻¹) * f
  have hf' : f'.Monic := by
    apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one m
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (nested_natDegree_le F m hF)
    · change (Polynomial.C (MvPolynomial.C c⁻¹) * f).coeff m = 1
      rw [Polynomial.coeff_C_mul]
      rw [nested_top_coefficient F m hF, ← MvPolynomial.C_mul]
      simp only [c, inv_mul_cancel₀ hinf, MvPolynomial.C_1]
  have hfg' : IsRelPrime f' g := by
    have hnested := relPrime_ringEquiv (MvPolynomial.finSuccEquiv K 2).toRingEquiv hfg
    have hu : IsUnit (Polynomial.C (MvPolynomial.C c⁻¹ : MvPolynomial (Fin 2) K)) := by
      apply IsUnit.map Polynomial.C
      apply IsUnit.map MvPolynomial.C
      exact (inv_ne_zero hinf).isUnit
    exact (associated_unit_mul_left f (Polynomial.C (MvPolynomial.C c⁻¹)) hu).symm.isRelPrime_left hnested
  obtain ⟨w, hw, hc⟩ := exists_specialization_coprime f' g hf' hfg'
    (A * X (0 : Fin 2)) (mul_ne_zero hA (X_ne_zero _))
  rw [map_mul, eval_X, mul_ne_zero_iff] at hw
  have hcop : IsCoprime (f.map (eval w)) (g.map (eval w)) := by
    change IsCoprime ((Polynomial.C (MvPolynomial.C c⁻¹) * f).map (eval w)) _ at hc
    rw [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.eval_C] at hc
    exact (isCoprime_mul_unit_left_left (Polynomial.isUnit_C.mpr (inv_ne_zero hinf).isUnit) _ _).mp hc
  refine ⟨w, hw.2, hw.1, ?_⟩
  apply binary_relPrime_of_dehomogenize_coprime _ _ m n
    (pencilRestriction_homogeneous w F m hF) (pencilRestriction_homogeneous w G n hG)
  · rwa [pencil_eval_infinity]
  · simpa only [pencil_dehomogenize] using hcop

/-- A nondegenerate actual plane-line restriction obtained by two concrete
coordinate substitutions. -/
def lineRestriction (p : Fin 3 → K) (w : Fin 2 → K) :
    PlaneRing K →ₐ[K] MvPolynomial (Fin 2) K :=
  (pencilRestriction w).comp (triangularMap p)

theorem lineRestriction_surjective (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) : Function.Surjective (lineRestriction p w) :=
  (pencilRestriction_surjective w hw).comp (triangularEquiv p hp).surjective

theorem lineRestriction_homogeneous (p : Fin 3 → K) (w : Fin 2 → K)
    (F : PlaneRing K) (d : ℕ) (hF : F.IsHomogeneous d) :
    (lineRestriction p w F).IsHomogeneous d :=
  pencilRestriction_homogeneous w _ d (triangularMap_homogeneous p F d hF)

/-- Two actual relatively prime plane forms admit a surjective homogeneous
line restriction whose binary images have no nonunit common factor. -/
theorem exists_coprime_line [Infinite K]
    (F G : PlaneRing K) (m n : ℕ) (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hF0 : F ≠ 0) (hfg : IsRelPrime F G) :
    ∃ p : Fin 3 → K, ∃ w : Fin 2 → K,
      p 0 ≠ 0 ∧ w 0 ≠ 0 ∧ Function.Surjective (lineRestriction p w) ∧
        IsRelPrime (lineRestriction p w F) (lineRestriction p w G) := by
  obtain ⟨p, hp0, hpF⟩ := exists_triangular_nonvanishing F hF0
  obtain ⟨w, hw0, _, hcop⟩ := exists_coprime_pencil (triangularMap p F) (triangularMap p G)
    m n (triangularMap_homogeneous p F m hF) (triangularMap_homogeneous p G n hG)
    hpF (relPrime_ringEquiv (triangularEquiv p hp0).toRingEquiv hfg) 1 one_ne_zero
  exact ⟨p, w, hp0, hw0, lineRestriction_surjective p w hp0 hw0, hcop⟩

end CoprimePlaneLine

end Cylinder.GenericPlaneLine
end
