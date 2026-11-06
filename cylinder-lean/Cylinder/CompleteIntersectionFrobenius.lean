module

public import Cylinder.CompleteIntersectionPerfectPairing

/-! The actual homogeneous binary quotient is a Frobenius algebra. The
functional reads its top homogeneous component and the multiplication
pairing is proved perfect on the whole finite quotient. -/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionFrobenius

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.CompleteIntersectionSocle
open Cylinder.CompleteIntersectionAdjoint Cylinder.CompleteIntersectionPerfectPairing
open scoped Classical BigOperators

variable {K : Type*} [Field K]

local instance : GradedAlgebra (BinaryForms K) := MvPolynomial.gradedAlgebra

theorem equationsIdeal_homogeneous (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    (equationsIdeal F G).IsHomogeneous (BinaryForms K) := by
  apply Ideal.homogeneous_span
  intro P hP
  rcases hP with rfl | hP
  · exact ⟨e, hF⟩
  · have hPG : P = G := Set.mem_singleton_iff.mp hP
    subst P
    exact ⟨t, hG⟩

def componentMap (F G : BinaryRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    QuotientRing F G →ₗ[K] QuotientRing F G :=
  ((equationsIdeal F G).restrictScalars K).liftQ
    ((Ideal.Quotient.mkₐ K (equationsIdeal F G)).toLinearMap.comp
      (homogeneousComponent d)) (by
      intro P hP
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact homogeneousComponent_mem_of_mem (equationsIdeal_homogeneous F G e t hF hG) hP d)

theorem componentMap_mk (F G : BinaryRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (P : BinaryRing K) :
    componentMap F G e t d hF hG (Ideal.Quotient.mk (equationsIdeal F G) P) =
      Ideal.Quotient.mk (equationsIdeal F G) (homogeneousComponent d P) := rfl

def componentToPiece (F G : BinaryRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    QuotientRing F G →ₗ[K] quotientPiece F G d :=
  (componentMap F G e t d hF hG).codRestrict _ (by
    intro z
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨homogeneousComponent d P, homogeneousComponent_isHomogeneous d P⟩, rfl⟩)

def residueFunctional (F G : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    QuotientRing F G →ₗ[K] K :=
  (topCoordinate F G e t he ht hF hG hF0 hcop).toLinearMap.comp
    (componentToPiece F G e t (e + t - 2) hF hG)

def residuePairing (F G : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    QuotientRing F G →ₗ[K] QuotientRing F G →ₗ[K] K where
  toFun a :=
    { toFun := fun b => residueFunctional F G e t he ht hF hG hF0 hcop (a * b)
      map_add' := by intro b c; rw [mul_add, map_add]
      map_smul' := by intro k b; simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    change residueFunctional F G e t he ht hF hG hF0 hcop ((a + b) * c) =
      residueFunctional F G e t he ht hF hG hF0 hcop (a * c) +
      residueFunctional F G e t he ht hF hG hF0 hcop (b * c)
    rw [add_mul, map_add]
  map_smul' := by
    intro k a
    apply LinearMap.ext
    intro b
    change residueFunctional F G e t he ht hF hG hF0 hcop (k • a * b) =
      k • residueFunctional F G e t he ht hF hG hF0 hcop (a * b)
    rw [smul_mul_assoc, map_smul]

theorem exists_nonzero_component (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (P : BinaryRing K) (hPn : P ∉ equationsIdeal F G) :
    ∃ d : ℕ, homogeneousComponent d P ∉ equationsIdeal F G := by
  by_contra! h
  apply hPn
  rw [← sum_homogeneousComponent P]
  exact Ideal.sum_mem _ (fun d _ => h d)

theorem residuePairing_injective (F G : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) :
    Function.Injective (residuePairing F G e t he ht hF hG hF0 hcop) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra han
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hPn : P ∉ equationsIdeal F G := by
    intro hPI
    exact han (Ideal.Quotient.eq_zero_iff_mem.mpr hPI)
  obtain ⟨d, hd⟩ := exists_nonzero_component F G e t hF hG P hPn
  have hdeg : d ≤ e + t - 2 := by
    by_contra hn
    exact hd (homogeneous_high_mem_ideal F G e t d he ht hF hG hF0 hG0 hcop
      (homogeneousComponent d P) (homogeneousComponent_isHomogeneous d P) (by omega))
  obtain ⟨Q, hQ, hPQ⟩ := exists_top_product F G e t d hF hG hF0 hcop
    (homogeneousComponent d P) (homogeneousComponent_isHomogeneous d P) hd hdeg
  have hcomponent : homogeneousComponent (e + t - 2) (P * Q) =
      homogeneousComponent d P * Q := by
    have h := DirectSum.coe_decompose_mul_add_of_right_mem (BinaryForms K)
      (i := d) (j := e + t - 2 - d) (a := P) (b := Q) hQ
    have hsum : d + (e + t - 2 - d) = e + t - 2 := by omega
    rw [hsum] at h
    have hc (R : BinaryRing K) (n : ℕ) :
        (DirectSum.decompose (BinaryForms K) R n : BinaryRing K) = homogeneousComponent n R :=
      MvPolynomial.decomposition.decompose'_apply R n
    rw [hc, hc] at h
    exact h
  have hz := congrArg (fun f : QuotientRing F G →ₗ[K] K =>
    f (Ideal.Quotient.mk (equationsIdeal F G) Q)) ha
  change topCoordinate F G e t he ht hF hG hF0 hcop
    (componentToPiece F G e t (e + t - 2) hF hG
      (Ideal.Quotient.mk (equationsIdeal F G) P * Ideal.Quotient.mk (equationsIdeal F G) Q)) = 0 at hz
  have hpz := congrArg Subtype.val ((topCoordinate F G e t he ht hF hG hF0 hcop).injective
    (hz.trans (map_zero _).symm))
  change componentMap F G e t (e + t - 2) hF hG
    (Ideal.Quotient.mk (equationsIdeal F G) P * Ideal.Quotient.mk (equationsIdeal F G) Q) = 0 at hpz
  rw [← map_mul, componentMap_mk, hcomponent] at hpz
  exact hPQ (Ideal.Quotient.eq_zero_iff_mem.mp hpz)

/-- The Frobenius property holds on the actual finite quotient ring. -/
theorem residuePairing_isPerfPair (F G : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) :
    (residuePairing F G e t he ht hF hG hF0 hcop).IsPerfPair := by
  letI : FiniteDimensional K (QuotientRing F G) :=
    CompleteIntersectionFinite.quotient_finiteDimensional F G e t he ht hF hG hF0 hG0 hcop
  have hi := residuePairing_injective F G e t he ht hF hG hF0 hG0 hcop
  apply LinearMap.IsPerfPair.of_injective hi
  have hf : (residuePairing F G e t he ht hF hG hF0 hcop).flip =
      residuePairing F G e t he ht hF hG hF0 hcop := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change residueFunctional F G e t he ht hF hG hF0 hcop (b * a) =
      residueFunctional F G e t he ht hF hG hF0 hcop (a * b)
    rw [mul_comm]
  rw [hf]
  exact hi

#print axioms componentMap
#print axioms residuePairing_isPerfPair

end Cylinder.CompleteIntersectionFrobenius

end
