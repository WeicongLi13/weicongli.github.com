module

public import Cylinder.CompleteIntersectionFrobenius

/-! A proved Frobenius multiplication pairing identifies the actual ideal
annihilator with the dual of the actual quotient. The complete-intersection
wrapper obtains its pairing from the preceding construction. -/

@[expose] public section
noncomputable section

namespace Cylinder.FrobeniusAnnihilator

open Module
open scoped Classical

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

def multiplicationPairing (ρ : A →ₗ[K] K) : A →ₗ[K] A →ₗ[K] K where
  toFun a :=
    { toFun := fun b => ρ (a * b)
      map_add' := by intro b c; rw [mul_add, map_add]
      map_smul' := by intro k b; simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    change ρ ((a + b) * c) = ρ (a * c) + ρ (b * c)
    rw [add_mul, map_add]
  map_smul' := by
    intro k a
    apply LinearMap.ext
    intro b
    change ρ (k • a * b) = k • ρ (a * b)
    rw [smul_mul_assoc, map_smul]

theorem annihilator_eq_orthogonal (ρ : A →ₗ[K] K)
    (hp : (multiplicationPairing ρ).IsPerfPair) (J : Ideal A) :
    J.annihilator.restrictScalars K =
      (J.restrictScalars K).dualAnnihilator.comap (multiplicationPairing ρ) := by
  ext a
  constructor
  · intro ha
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro b hb
    change ρ (a * b) = 0
    have hab := Submodule.mem_annihilator.mp ha b hb
    change a * b = 0 at hab
    rw [hab, map_zero]
  · intro ha
    have horth : ∀ b ∈ J, ρ (a * b) = 0 :=
      (Submodule.mem_dualAnnihilator _).mp ha
    apply Submodule.mem_annihilator.mpr
    intro b hb
    change a * b = 0
    apply hp.bijective_left.injective
    apply LinearMap.ext
    intro c
    change ρ ((a * b) * c) = ρ (0 * c)
    rw [mul_assoc, zero_mul, map_zero]
    exact horth (b * c) (J.mul_mem_right c hb)

def orthogonalEquiv (ρ : A →ₗ[K] K)
    (hp : (multiplicationPairing ρ).IsPerfPair) (J : Ideal A) :
    ((J.restrictScalars K).dualAnnihilator.comap (multiplicationPairing ρ)) ≃ₗ[K]
      (J.restrictScalars K).dualAnnihilator :=
  LinearEquiv.ofBijective ((multiplicationPairing ρ).submoduleComap
    (J.restrictScalars K).dualAnnihilator) ⟨by
      intro a b hab
      apply Subtype.ext
      exact hp.bijective_left.injective (congrArg Subtype.val hab),
    LinearMap.submoduleComap_surjective_of_surjective _ _ hp.bijective_left.surjective⟩

/-- This is an isomorphism of actual vector spaces, rather than an equality
of their dimensions. -/
def annihilatorEquivDualQuotient (ρ : A →ₗ[K] K)
    (hp : (multiplicationPairing ρ).IsPerfPair) (J : Ideal A) :
    J.annihilator.restrictScalars K ≃ₗ[K] Dual K (A ⧸ J) :=
  ((LinearEquiv.ofEq _ _ (annihilator_eq_orthogonal ρ hp J)).trans
    (orthogonalEquiv ρ hp J)).trans
      (Submodule.dualQuotEquivDualAnnihilator (J.restrictScalars K)).symm

theorem annihilatorEquivDualQuotient_apply_mk (ρ : A →ₗ[K] K)
    (hp : (multiplicationPairing ρ).IsPerfPair) (J : Ideal A)
    (a : J.annihilator.restrictScalars K) (b : A) :
    annihilatorEquivDualQuotient ρ hp J a (Ideal.Quotient.mk J b) = ρ (a.val * b) := rfl

open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionFrobenius

/-- The pairing assumption is discharged by the actual homogeneous
complete-intersection algebra. -/
def completeIntersectionAnnihilatorEquiv (F G : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : MvPolynomial.IsHomogeneous F e) (hG : MvPolynomial.IsHomogeneous G t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G)
    (J : Ideal (QuotientRing F G)) :
    J.annihilator.restrictScalars K ≃ₗ[K] Dual K (QuotientRing F G ⧸ J) :=
  annihilatorEquivDualQuotient (residueFunctional F G e t he ht hF hG hF0 hcop)
    (residuePairing_isPerfPair F G e t he ht hF hG hF0 hG0 hcop) J

#print axioms annihilatorEquivDualQuotient
#print axioms completeIntersectionAnnihilatorEquiv

end Cylinder.FrobeniusAnnihilator

end
