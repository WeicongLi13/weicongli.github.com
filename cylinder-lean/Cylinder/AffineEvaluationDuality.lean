module

public import Cylinder.FiniteEvaluationDuality

/-! Actual finite-point coefficient relations are identified with the
filtered annihilator in the real affine complete-intersection algebra.
The point evaluation is proved surjective by genuine interpolation. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineEvaluationDuality

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionFiltered Cylinder.AffinePointEvaluation
open Cylinder.FiniteEvaluationDuality Cylinder.AffineFilteredDuality
open Cylinder.AffineResidueFunctional Cylinder.FrobeniusAnnihilator
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

def coefficientRelationMap (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) (j : ℕ) :
    coefficientRelations v j →ₗ[K] relationSpace f g (pointIdeal f g v hf hg) j :=
  ((((evaluation f g v hf hg).toLinearMap.dualMap).comp coefficientDualMap).comp
    (coefficientRelations v j).subtype).codRestrict _ (by
      intro c
      change (evaluation f g v hf hg).toLinearMap.dualMap (coefficientDualMap c.val) ∈
        relationSpace f g (pointIdeal f g v hf hg) j
      constructor
      · apply (Submodule.mem_dualAnnihilator _).mpr
        intro a ha
        have hzero : evaluation f g v hf hg a = 0 := ha
        change coefficientDualMap c.val (evaluation f g v hf hg a) = 0
        rw [hzero, map_zero]
      · apply (Submodule.mem_dualAnnihilator _).mpr
        intro a ha
        obtain ⟨P, hP, hPa⟩ := (mem_filteredPiece f g j a).mp ha
        rw [← hPa]
        exact (mem_coefficientRelations v j c.val).mp c.property P hP)

theorem coefficientRelationMap_injective (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hv : Function.Injective v)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) (j : ℕ) :
    Function.Injective (coefficientRelationMap f g v hf hg j) := by
  intro c d hcd
  apply Subtype.ext
  apply coefficientDualMap_injective
  apply LinearMap.dualMap_injective_of_surjective
    (f := (evaluation f g v hf hg).toLinearMap) (evaluation_surjective f g v hv hf hg)
  exact congrArg Subtype.val hcd

theorem coefficientRelationMap_surjective (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hv : Function.Injective v)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) (j : ℕ) :
    Function.Surjective (coefficientRelationMap f g v hf hg j) := by
  intro L
  have hLrange : L.val ∈ LinearMap.range (evaluation f g v hf hg).toLinearMap.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _
      (evaluation_surjective f g v hv hf hg), ← pointIdeal_restrict_eq_kernel]
    exact L.property.1
  obtain ⟨F, hFL⟩ := hLrange
  obtain ⟨c, hcF⟩ := coefficientDualMap_surjective F
  have hcm : c ∈ coefficientRelations v j := by
    apply (mem_coefficientRelations v j c).mpr
    intro P hP
    have hmem := (mem_filteredPiece f g j _).mpr ⟨P, hP, rfl⟩
    have hz := (Submodule.mem_dualAnnihilator L.val).mp L.property.2 _ hmem
    rw [← hFL, ← hcF] at hz
    exact hz
  refine ⟨⟨c, hcm⟩, ?_⟩
  apply Subtype.ext
  change (evaluation f g v hf hg).toLinearMap.dualMap (coefficientDualMap c) = L.val
  rw [hcF]
  exact hFL

def coefficientRelationEquiv (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hv : Function.Injective v)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) (j : ℕ) :
    coefficientRelations v j ≃ₗ[K] relationSpace f g (pointIdeal f g v hf hg) j :=
  LinearEquiv.ofBijective (coefficientRelationMap f g v hf hg j)
    ⟨coefficientRelationMap_injective f g v hv hf hg j,
      coefficientRelationMap_surjective f g v hv hf hg j⟩

/-- Finite-point degree-j relations and the actual complementary filtered
annihilator are linearly isomorphic. The surjectivity and pairing inputs
are both proved for these actual objects. -/
def affineEvaluationDuality (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) f = 0) (hgv : ∀ i, eval (v i) g = 0)
    (j : ℕ) (hj : j < e + t - 2) :
    ↥((pointIdeal f g v hfv hgv).annihilator.restrictScalars K ⊓
      filteredPiece f g (e + t - 2 - j - 1)) ≃ₗ[K] coefficientRelations v j :=
  (filteredAnnihilatorEquivRelations f g e t he ht hf hg hfe hge hcop
    (pointIdeal f g v hfv hgv) j hj).trans (coefficientRelationEquiv f g v hv hfv hgv j).symm

theorem duality_formula (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) f = 0) (hgv : ∀ i, eval (v i) g = 0)
    (j : ℕ) (hj : j < e + t - 2)
    (a : ↥((pointIdeal f g v hfv hgv).annihilator.restrictScalars K ⊓
      filteredPiece f g (e + t - 2 - j - 1))) (b : QuotientRing f g) :
    residueFunctional f g e t he ht hf hg hfe hge hcop (a.val * b) =
      ∑ i, (affineEvaluationDuality f g e t he ht hf hg hfe hge hcop v hv hfv hgv j hj a).val i *
        evaluation f g v hfv hgv b i := by
  have h := (coefficientRelationEquiv f g v hv hfv hgv j).apply_symm_apply
    (filteredAnnihilatorEquivRelations f g e t he ht hf hg hfe hge hcop
      (pointIdeal f g v hfv hgv) j hj a)
  have hval := congrArg Subtype.val h
  change (evaluation f g v hfv hgv).toLinearMap.dualMap
      (coefficientDualMap (affineEvaluationDuality f g e t he ht hf hg hfe hge hcop v hv hfv hgv j hj a).val) =
    multiplicationPairing (residueFunctional f g e t he ht hf hg hfe hge hcop) a.val at hval
  exact (congrArg (fun F : Dual K (QuotientRing f g) => F b) hval).symm

#print axioms coefficientRelationEquiv
#print axioms affineEvaluationDuality
#print axioms duality_formula

end Cylinder.AffineEvaluationDuality

end
