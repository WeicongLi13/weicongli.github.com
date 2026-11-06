module

public import Cylinder.ProjectiveDualityMultiplication
public import Cylinder.IntegerRepresentativeRelations

/-! Complete-intersection duality for any chosen normalization of the original points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectiveNormalizedDuality

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.ProjectiveIntegerRelations Cylinder.ProjectiveCompleteIntersectionDuality
open Cylinder.ProjectiveDualityMultiplication Cylinder.IntegerRepresentativeRelations

variable {K : Type*} [Field K]

def normalizedBy (ell : Module.Dual K (Fin 3 → K)) (D : Finset (PlanePointModel.Plane K)) :
    D → Fin 3 → K := fun P => (ell P.val.rep)⁻¹ • P.val.rep

def normalizedRelations (ell : Module.Dual K (Fin 3 → K))
    (D : Finset (PlanePointModel.Plane K)) (j : ℤ) : Submodule K (D → K) :=
  integerRelations (normalizedBy ell D) j

def normalizationScale (c : Chart K) (ell : Module.Dual K (Fin 3 → K))
    (D : Finset (PlanePointModel.Plane K)) : D → K := fun P => c.line P.val.rep / ell P.val.rep

theorem normalizationScale_ne_zero (c : Chart K) (ell : Module.Dual K (Fin 3 → K))
    (D : Finset (PlanePointModel.Plane K)) (hc : ∀ P : D, c.line P.val.rep ≠ 0)
    (hell : ∀ P : D, ell P.val.rep ≠ 0) : ∀ P, normalizationScale c ell D P ≠ 0 :=
  fun P => div_ne_zero (hc P) (hell P)

theorem normalization_points (c : Chart K) (ell : Module.Dual K (Fin 3 → K))
    (D : Finset (PlanePointModel.Plane K)) (hc : ∀ P : D, c.line P.val.rep ≠ 0)
    (hell : ∀ P : D, ell P.val.rep ≠ 0) :
    (fun P : D => normalizationScale c ell D P • c.normalizedPoint P.val) = normalizedBy ell D := by
  funext P
  change (c.line P.val.rep / ell P.val.rep) • ((c.line P.val.rep)⁻¹ • P.val.rep) =
    (ell P.val.rep)⁻¹ • P.val.rep
  rw [smul_smul]
  congr 1
  field_simp [hc P, hell P]

theorem normalizedBy_line (ell : Module.Dual K (Fin 3 → K))
    (D : Finset (PlanePointModel.Plane K)) (hell : ∀ P : D, ell P.val.rep ≠ 0) (P : D) :
    ell (normalizedBy ell D P) = 1 := by
  change ell ((ell P.val.rep)⁻¹ • P.val.rep) = 1
  rw [map_smul]
  exact inv_mul_cancel₀ (hell P)

def normalizationEquiv (c : Chart K) (ell : Module.Dual K (Fin 3 → K))
    (D : Finset (PlanePointModel.Plane K)) (hc : ∀ P : D, c.line P.val.rep ≠ 0)
    (hell : ∀ P : D, ell P.val.rep ≠ 0) (j : ℤ) :
    originalRelations c D j ≃ₗ[K] normalizedRelations ell D j :=
  (representativeRelationsEquiv (fun P : D => c.normalizedPoint P.val)
    (normalizationScale c ell D) (normalizationScale_ne_zero c ell D hc hell) j).trans
      (LinearEquiv.ofEq _ _ (congrArg (fun v => integerRelations v j)
        (normalization_points c ell D hc hell)))

def normalizedRelationResidualEquiv (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (ell : Module.Dual K (Fin 3 → K)) (hell : ∀ P : D, ell P.val.rep ≠ 0) (j : ℤ) :
    normalizedRelations ell D j ≃ₗ[K] OriginalResidualQuotient F G D ((e : ℤ) + t - 3 - j) :=
  (normalizationEquiv c ell D (point_line_ne_zero c F G e t hgood D hpoints) hell j).symm.trans
    (projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints j)

def normalizedCoefficientMultiplication (c : Chart K) (ell : Module.Dual K (Fin 3 → K))
    (D : Finset (PlanePointModel.Plane K)) (hc : ∀ P : D, c.line P.val.rep ≠ 0)
    (hell : ∀ P : D, ell P.val.rep ≠ 0) (j : ℤ) (u : ℕ)
    (Q : PlaneRing K) (hQ : Q.IsHomogeneous u) :
    normalizedRelations ell D j →ₗ[K] normalizedRelations ell D (j - u) :=
  (normalizationEquiv c ell D hc hell (j - u)).toLinearMap.comp
    ((originalCoefficientMultiplication c D hc j u Q hQ).comp
      (normalizationEquiv c ell D hc hell j).symm.toLinearMap)

theorem normalizedCoefficientMultiplication_apply (c : Chart K) (ell : Module.Dual K (Fin 3 → K))
    (D : Finset (PlanePointModel.Plane K)) (hc : ∀ P : D, c.line P.val.rep ≠ 0)
    (hell : ∀ P : D, ell P.val.rep ≠ 0) (j : ℤ) (u : ℕ)
    (Q : PlaneRing K) (hQ : Q.IsHomogeneous u) (a : normalizedRelations ell D j) (P : D) :
    (normalizedCoefficientMultiplication c ell D hc hell j u Q hQ a).val P =
      a.val P * eval (normalizedBy ell D P) Q := by
  let b := (normalizationEquiv c ell D hc hell j).symm a
  have hb : coefficientScale (normalizationScale c ell D)
      (normalizationScale_ne_zero c ell D hc hell) j b.val = a.val := by
    exact congrArg Subtype.val ((normalizationEquiv c ell D hc hell j).apply_symm_apply a)
  have hm : (originalCoefficientMultiplication c D hc j u Q hQ b).val =
      fun P => b.val P * eval (c.normalizedPoint P.val) Q :=
    funext (originalCoefficientMultiplication_apply c D hc j u Q hQ b)
  change coefficientScale (normalizationScale c ell D)
    (normalizationScale_ne_zero c ell D hc hell) (j - u)
    (originalCoefficientMultiplication c D hc j u Q hQ b).val P = _
  rw [hm]
  have h := rescaling_multiplication (fun P : D => c.normalizedPoint P.val)
    (normalizationScale c ell D) (normalizationScale_ne_zero c ell D hc hell) j u Q hQ b.val
  have hp : ∀ i : D, normalizationScale c ell D i • c.normalizedPoint i.val = normalizedBy ell D i :=
    fun i => congrFun (normalization_points c ell D hc hell) i
  simp only [hp, hb] at h
  exact congrFun h P

theorem normalized_duality_multiply (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (ell : Module.Dual K (Fin 3 → K)) (hell : ∀ P : D, ell P.val.rep ≠ 0)
    (j : ℤ) (u : ℕ) (Q : PlaneRing K) (hQ : Q.IsHomogeneous u)
    (a : OriginalResidualQuotient F G D ((e : ℤ) + t - 3 - j)) :
    (normalizedRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints ell hell (j - u)).symm
      (originalResidualMultiplication c F G D _ _ u (by ring) Q hQ a) =
    normalizedCoefficientMultiplication c ell D (point_line_ne_zero c F G e t hgood D hpoints)
      hell j u Q hQ
      ((normalizedRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints ell hell j).symm a) := by
  let hc := point_line_ne_zero c F G e t hgood D hpoints
  change normalizationEquiv c ell D hc hell (j - u)
      ((projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints (j - u)).symm
        (originalResidualMultiplication c F G D _ _ u (by ring) Q hQ a)) =
    normalizationEquiv c ell D hc hell (j - u)
      (originalCoefficientMultiplication c D hc j u Q hQ
        ((normalizationEquiv c ell D hc hell j).symm
          (normalizationEquiv c ell D hc hell j
            ((projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints j).symm a))))
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (normalizationEquiv c ell D hc hell (j - u))
    (projective_duality_multiply c F G e t he ht hF hG hgood D hpoints j u Q hQ a)

theorem exists_normalized_duality [Infinite K] (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G)
    (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (ell : Module.Dual K (Fin 3 → K)) (hell : ∀ P : D, ell P.val.rep ≠ 0) :
    ∃ c : Chart K, GoodChart c F G e t ∧
      (∀ P : D, ell (normalizedBy ell D P) = 1) ∧
      Nonempty (∀ j : ℤ, normalizedRelations ell D j ≃ₗ[K]
        OriginalResidualQuotient F G D ((e : ℤ) + t - 3 - j)) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  exact ⟨c, hgood, normalizedBy_line ell D hell,
    ⟨fun j => normalizedRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints ell hell j⟩⟩

end Cylinder.ProjectiveNormalizedDuality

end
