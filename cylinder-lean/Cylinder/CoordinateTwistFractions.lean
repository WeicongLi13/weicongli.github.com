module

public import Cylinder.CoordinateLaurentLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Span.Basic
public import Lean.Elab.Tactic.Omega

/-! Actual degree-v homogeneous fractions inside the coordinate
localization. Their span is identified with the corresponding weighted
Laurent-monomial module, using the genuine localization equivalence. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.CoordinateTwistFractions

open Cylinder.CoordinateLaurentLocalization MvPolynomial

set_option autoImplicit false

variable (K : Type*) [CommRing K]

def localizationAlgEquiv : CoordinateLocalization K ≃ₐ[K] LaurentChart K where
  __ := localizationEquiv K
  commutes' a := by
    change localizationEquiv K (algebraMap K (CoordinateLocalization K) a) =
      algebraMap K (LaurentChart K) a
    rw [IsScalarTower.algebraMap_apply K (PlaneRing K) (CoordinateLocalization K),
      localizationEquiv_algebraMap]
    change Polynomial.toLaurent (MvPolynomial.optionEquivLeft K (Fin 2) (MvPolynomial.C a)) = _
    rw [MvPolynomial.optionEquivLeft_C, Polynomial.toLaurent_C]
    rfl

/-- A fixed actual denominator gives a linear numerator map. -/
def fractionLinear (n : ℕ) : PlaneRing K →ₗ[K] CoordinateLocalization K where
  toFun p := IsLocalization.mk' (CoordinateLocalization K) p
    (⟨MvPolynomial.X none ^ n, n, rfl⟩ : Submonoid.powers (MvPolynomial.X none : PlaneRing K))
  map_add' p q := by
    let den : Submonoid.powers (MvPolynomial.X none : PlaneRing K) :=
      ⟨MvPolynomial.X none ^ n, n, rfl⟩
    change IsLocalization.mk' (CoordinateLocalization K) (p + q) den =
      IsLocalization.mk' (CoordinateLocalization K) p den +
        IsLocalization.mk' (CoordinateLocalization K) q den
    rw [IsLocalization.mk'_eq_mul_mk'_one (p + q) den,
      IsLocalization.mk'_eq_mul_mk'_one p den,
      IsLocalization.mk'_eq_mul_mk'_one q den, map_add, add_mul]
  map_smul' a p := by
    let den : Submonoid.powers (MvPolynomial.X none : PlaneRing K) :=
      ⟨MvPolynomial.X none ^ n, n, rfl⟩
    change IsLocalization.mk' (CoordinateLocalization K) (a • p) den =
      a • IsLocalization.mk' (CoordinateLocalization K) p den
    rw [IsLocalization.mk'_eq_mul_mk'_one (a • p) den,
      IsLocalization.mk'_eq_mul_mk'_one p den]
    change (IsScalarTower.toAlgHom K (PlaneRing K) (CoordinateLocalization K)) (a • p) * _ =
      a • ((IsScalarTower.toAlgHom K (PlaneRing K) (CoordinateLocalization K)) p * _)
    rw [map_smul, smul_mul_assoc]

def homogeneousFractions (v : ℤ) : Set (CoordinateLocalization K) :=
  {z | ∃ (m n : ℕ) (p : PlaneRing K), (m : ℤ) - n = v ∧ p.IsHomogeneous m ∧
    z = fractionLinear K n p}

/-- The local degree-v module is defined by actual homogeneous
polynomial fractions, independently of a Laurent coefficient model. -/
def twistPiece (v : ℤ) : Submodule K (CoordinateLocalization K) :=
  Submodule.span K (homogeneousFractions K v)

def monomialFractions (v : ℤ) : Set (CoordinateLocalization K) :=
  {z | ∃ (m : Option (Fin 2) →₀ ℕ) (n : ℕ) (a : K), (m.degree : ℤ) - n = v ∧
    z = fractionLinear K n (MvPolynomial.monomial m a)}

theorem homogeneousFraction_mem_monomialSpan (v : ℤ) (m n : ℕ) (p : PlaneRing K)
    (hd : (m : ℤ) - n = v) (hp : p.IsHomogeneous m) :
    fractionLinear K n p ∈ Submodule.span K (monomialFractions K v) := by
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hds
  have hdeg : d.degree = m := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hds) (hp.coeff_eq_zero h)
  apply Submodule.subset_span
  exact ⟨d, n, p.coeff d, by simpa only [hdeg] using hd, rfl⟩

theorem twistPiece_eq_monomialSpan (v : ℤ) :
    twistPiece K v = Submodule.span K (monomialFractions K v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨m, n, p, hd, hp, rfl⟩
    exact homogeneousFraction_mem_monomialSpan K v m n p hd hp
  · apply Submodule.span_le.mpr
    rintro z ⟨m, n, a, hd, rfl⟩
    apply Submodule.subset_span
    exact ⟨m.degree, n, MvPolynomial.monomial m a, hd,
      MvPolynomial.isHomogeneous_monomial a rfl, rfl⟩

theorem degree_first_add_some (m : Option (Fin 2) →₀ ℕ) :
    m.degree = m none + m.some.degree := by
  change m.sum (fun _ n => n) = m none + m.some.sum (fun _ n => n)
  exact m.sum_option_index (fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)

def weightedLaurentMonomials (v : ℤ) : Set (LaurentChart K) :=
  {z | ∃ (m : Fin 2 →₀ ℕ) (d : ℤ) (a : K), d + (m.degree : ℤ) = v ∧
    z = LaurentPolynomial.C (MvPolynomial.monomial m a) * LaurentPolynomial.T d}

def weightedLaurentPiece (v : ℤ) : Submodule K (LaurentChart K) :=
  Submodule.span K (weightedLaurentMonomials K v)

theorem image_monomialFractions (v : ℤ) :
    (localizationAlgEquiv K).toLinearMap '' monomialFractions K v = weightedLaurentMonomials K v := by
  ext z
  constructor
  · rintro ⟨x, ⟨m, n, a, hd, rfl⟩, rfl⟩
    refine ⟨m.some, (m none : ℤ) - n, a, ?_, ?_⟩
    · have hdeg := degree_first_add_some m
      omega
    · exact localizationEquiv_monomialFraction K m a n
  · rintro ⟨m, d, a, hd, rfl⟩
    let q : Option (Fin 2) →₀ ℕ := m.optionElim d.toNat
    let n : ℕ := (-d).toNat
    have hqnone : q none = d.toNat := by simp [q]
    have hqsome : q.some = m := by simp [q]
    have hqdeg : q.degree = d.toNat + m.degree := by
      rw [degree_first_add_some, hqnone, hqsome]
    refine ⟨fractionLinear K n (MvPolynomial.monomial q a), ?_, ?_⟩
    · exact ⟨q, n, a, by dsimp [n]; omega, rfl⟩
    · change localizationEquiv K (IsLocalization.mk' (CoordinateLocalization K)
        (MvPolynomial.monomial q a)
        (⟨MvPolynomial.X none ^ n, n, rfl⟩ : Submonoid.powers (MvPolynomial.X none : PlaneRing K))) = _
      rw [localizationEquiv_monomialFraction, hqsome, hqnone]
      have he : (d.toNat : ℤ) - n = d := by dsimp [n]; omega
      rw [he]

theorem map_twistPiece (v : ℤ) :
    (twistPiece K v).map (localizationAlgEquiv K).toLinearMap = weightedLaurentPiece K v := by
  rw [twistPiece_eq_monomialSpan, Submodule.map_span, image_monomialFractions]
  rfl

/-- The module of actual homogeneous fractions is genuinely linearly
equivalent to the weighted Laurent module; neither side is assumed to
be a twisting-sheaf section module. -/
def twistLaurentEquiv (v : ℤ) : twistPiece K v ≃ₗ[K] weightedLaurentPiece K v :=
  (localizationAlgEquiv K).toLinearEquiv.ofSubmodules _ _ (map_twistPiece K v)

end Cylinder.CoordinateTwistFractions

end
