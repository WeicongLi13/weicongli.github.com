module

public import Cylinder.AffineLinePolynomial
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Dehomogenizing binary forms

Setting the second variable equal to one is a linear equivalence from
binary forms of degree `d` to univariate polynomials of degree at most
`d`. Multiplication by the two binary variables becomes multiplication
by `X` and the identity. These are the actual coordinate operations used
in Lemma `lem:binary`.
-/

@[expose] public section

noncomputable section

namespace Cylinder.BinaryHomogenization

open MvPolynomial

variable {K : Type*} [Field K]

def dehomogenize : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, 1]

theorem dehomogenize_eq_linePolynomial (P : MvPolynomial (Fin 2) K) :
    dehomogenize P = AffineLinePolynomial.linePolynomial P ![0, 1] ![1, 0] := by
  have hhom : (dehomogenize (K := K)).toRingHom =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun i => AffineLinePolynomial.affineLinear (![0, 1] i) (![1, 0] i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [dehomogenize]
    · intro i
      fin_cases i <;> simp [dehomogenize, AffineLinePolynomial.affineLinear]
  exact congrArg (fun f : MvPolynomial (Fin 2) K →+* Polynomial K => f P) hhom

theorem dehomogenize_natDegree_le {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) : (dehomogenize P).natDegree ≤ d := by
  rw [dehomogenize_eq_linePolynomial]
  exact (AffineLinePolynomial.linePolynomial_degree_le _ _ _).trans hP.totalDegree_le

/-- The precise finite-degree linear equivalence behind dehomogenization. -/
def homogeneousDegreeEquiv (d : ℕ) :
    homogeneousSubmodule (Fin 2) K d ≃ₗ[K] Polynomial.degreeLE K d where
  toFun P := ⟨dehomogenize P.val, Polynomial.mem_degreeLE.mpr
    (Polynomial.natDegree_le_iff_degree_le.mp
      (dehomogenize_natDegree_le ((mem_homogeneousSubmodule _ _).mp P.property)))⟩
  invFun f := ⟨Polynomial.homogenize f.val d,
    (mem_homogeneousSubmodule _ _).mpr (Polynomial.isHomogeneous_homogenize f.val)⟩
  left_inv P := by
    apply Subtype.ext
    exact Polynomial.homogenize_eq_of_isHomogeneous
      ((mem_homogeneousSubmodule _ _).mp P.property) rfl
  right_inv f := by
    apply Subtype.ext
    exact Polynomial.aeval_homogenize_X_one f.val
      (Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp f.property))
  map_add' P Q := by
    apply Subtype.ext
    exact map_add dehomogenize P.val Q.val
  map_smul' c P := by
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, map_smul, RingHom.id_apply]

@[simp] theorem dehomogenize_mul_X_zero (P : MvPolynomial (Fin 2) K) :
    dehomogenize (MvPolynomial.X 0 * P) = Polynomial.X * dehomogenize P := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_mul_X_one (P : MvPolynomial (Fin 2) K) :
    dehomogenize (MvPolynomial.X 1 * P) = dehomogenize P := by
  simp [dehomogenize]

theorem dehomogenize_injective_on_homogeneous (d : ℕ)
    {P Q : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (heq : dehomogenize P = dehomogenize Q) : P = Q := by
  have hP' := Polynomial.homogenize_eq_of_isHomogeneous hP (p := dehomogenize P) rfl
  have hQ' := Polynomial.homogenize_eq_of_isHomogeneous hQ (p := dehomogenize Q) rfl
  rw [← hP', ← hQ', heq]

end Cylinder.BinaryHomogenization

end
