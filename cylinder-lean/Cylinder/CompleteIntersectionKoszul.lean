module

public import Cylinder.IntersectionResolution
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual two-generator Koszul resolution

Relative primality proves the complete relation module on `F,G`.
The quotient is the real ring `R/(F,G)`, and all three maps in its
Koszul resolution have their injectivity, kernels, and surjectivity
proved directly. No resolution or perfect pairing is assumed.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CompleteIntersectionKoszul

open Module
open scoped Classical

variable {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]

def equationsIdeal (F G : R) : Ideal R := Ideal.span ({F, G} : Set R)

abbrev QuotientRing (F G : R) := R ⧸ equationsIdeal F G

def generatorMap (F G : R) : (R × R) →ₗ[R] R where
  toFun A := A.1 * F + A.2 * G
  map_add' A B := by simp only [Prod.fst_add, Prod.snd_add, add_mul]; ring
  map_smul' c A := by simp [smul_eq_mul, mul_add, mul_assoc]

def koszulMap (F G : R) : R →ₗ[R] R × R where
  toFun c := (-G * c, F * c)
  map_add' c d := by simp [mul_add]
  map_smul' a c := by simp [smul_eq_mul, mul_left_comm]

theorem koszul_syzygy_iff (F G : R) (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (A B : R) :
    A * F + B * G = 0 ↔ ∃ c : R, A = -G * c ∧ B = F * c := by
  constructor
  · intro hrel
    have hBG : B * G = -(A * F) := eq_neg_of_add_eq_zero_right hrel
    have hFBG : F ∣ B * G := by rw [hBG]; exact dvd_neg.mpr (dvd_mul_left F A)
    obtain ⟨c, hB⟩ := hcop.dvd_of_dvd_mul_right hFBG
    rw [hB] at hrel
    have hAF : (A + G * c) * F = 0 := by convert hrel using 1 <;> ring
    have hA := (mul_eq_zero.mp hAF).resolve_right hF0
    refine ⟨c, ?_, hB⟩
    simpa only [neg_mul] using eq_neg_of_add_eq_zero_left hA
  · rintro ⟨c, rfl, rfl⟩
    ring

theorem generator_koszul_zero (F G c : R) : generatorMap F G (koszulMap F G c) = 0 := by
  change (-G * c) * F + (F * c) * G = 0
  ring

theorem koszulMap_injective (F G : R) (hF0 : F ≠ 0) : Function.Injective (koszulMap F G) := by
  intro c d hcd
  exact mul_left_cancel₀ hF0 (congrArg Prod.snd hcd)

theorem koszulMap_range_eq_kernel (F G : R) (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    LinearMap.range (koszulMap F G) = LinearMap.ker (generatorMap F G) := by
  ext A
  constructor
  · rintro ⟨c, rfl⟩
    exact generator_koszul_zero F G c
  · intro hA
    obtain ⟨c, hc1, hc2⟩ := (koszul_syzygy_iff F G hF0 hcop A.1 A.2).mp hA
    exact ⟨c, Prod.ext hc1.symm hc2.symm⟩

def kernelMap (F G : R) : R →ₗ[R] LinearMap.ker (generatorMap F G) :=
  (koszulMap F G).codRestrict _ (generator_koszul_zero F G)

theorem kernelMap_bijective (F G : R) (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    Function.Bijective (kernelMap F G) := by
  constructor
  · intro c d hcd
    exact koszulMap_injective F G hF0 (congrArg Subtype.val hcd)
  · intro A
    obtain ⟨c, hc1, hc2⟩ := (koszul_syzygy_iff F G hF0 hcop A.val.1 A.val.2).mp A.property
    exact ⟨c, Subtype.ext (Prod.ext hc1.symm hc2.symm)⟩

def kernelEquiv (F G : R) (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    R ≃ₗ[R] LinearMap.ker (generatorMap F G) :=
  LinearEquiv.ofBijective (kernelMap F G) (kernelMap_bijective F G hF0 hcop)

theorem kernel_free (F G : R) (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    Module.Free R (LinearMap.ker (generatorMap F G)) :=
  Module.Free.of_equiv (kernelEquiv F G hF0 hcop)

theorem kernel_finrank (F G : R) (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    finrank R (LinearMap.ker (generatorMap F G)) = 1 := by
  rw [← (kernelEquiv F G hF0 hcop).finrank_eq]
  exact Module.finrank_self R

theorem generatorMap_range_eq_ideal (F G : R) :
    LinearMap.range (generatorMap F G) = equationsIdeal F G := by
  ext z
  constructor
  · rintro ⟨A, rfl⟩
    exact Ideal.mem_span_pair.mpr ⟨A.1, A.2, rfl⟩
  · intro hz
    obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hz
    exact ⟨(A, B), hAB⟩

def quotientMap (F G : R) : R →ₗ[R] QuotientRing F G :=
  (Ideal.Quotient.mkₐ R (equationsIdeal F G)).toLinearMap

theorem quotientMap_kernel (F G : R) : LinearMap.ker (quotientMap F G) = equationsIdeal F G := by
  ext z
  change Ideal.Quotient.mk (equationsIdeal F G) z = 0 ↔ z ∈ equationsIdeal F G
  exact Ideal.Quotient.eq_zero_iff_mem

theorem quotientMap_surjective (F G : R) : Function.Surjective (quotientMap F G) :=
  Ideal.Quotient.mk_surjective

/-- Exactness of the real maps `0 → R → R² → R → R/(F,G) → 0`. -/
theorem actual_koszul_resolution (F G : R) (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    Function.Injective (koszulMap F G) ∧
      LinearMap.range (koszulMap F G) = LinearMap.ker (generatorMap F G) ∧
      LinearMap.range (generatorMap F G) = LinearMap.ker (quotientMap F G) ∧
      Function.Surjective (quotientMap F G) := by
  refine ⟨koszulMap_injective F G hF0, koszulMap_range_eq_kernel F G hF0 hcop, ?_,
    quotientMap_surjective F G⟩
  rw [quotientMap_kernel, generatorMap_range_eq_ideal]

theorem homogeneous_koszul_generator {K : Type*} [Field K]
    (F G : MvPolynomial (Fin 2) K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    ((koszulMap F G 1).1).IsHomogeneous t ∧ ((koszulMap F G 1).2).IsHomogeneous e := by
  simpa only [koszulMap, LinearMap.coe_mk, AddHom.coe_mk, mul_one] using And.intro hG.neg hF

#print axioms koszul_syzygy_iff
#print axioms actual_koszul_resolution
#print axioms kernel_finrank

end Cylinder.CompleteIntersectionKoszul

end
