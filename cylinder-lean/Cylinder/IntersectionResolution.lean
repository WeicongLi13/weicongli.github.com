module

public import Cylinder.FactorDegreeBound
public import Cylinder.HomogeneousDivision
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Ideal.Span

/-!
# The actual syzygies of the intersection generators

For a pairwise relatively prime family `F`, the generator indexed by `i`
is the product of all `F j` with `j ≠ i`. The relation map and its kernel
are actual linear maps and modules. No resolution or rank is assumed.
-/

@[expose] public section

noncomputable section

namespace Cylinder.IntersectionResolution

open Module
open scoped BigOperators Classical

variable {R I : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R] [Fintype I]

def cofactor (F : I → R) (i : I) : R := ∏ j ∈ Finset.univ.erase i, F j

def totalProduct (F : I → R) : R := ∏ i, F i

theorem cofactor_factor (F : I → R) (i : I) : F i * cofactor F i = totalProduct F :=
  Finset.mul_prod_erase _ _ (Finset.mem_univ i)

theorem cofactor_ne_zero (F : I → R) (hF : ∀ i, F i ≠ 0) (i : I) : cofactor F i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => hF j)

theorem totalProduct_ne_zero (F : I → R) (hF : ∀ i, F i ≠ 0) : totalProduct F ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => hF i)

theorem dvd_other_cofactor (F : I → R) (i j : I) (hij : i ≠ j) : F i ∣ cofactor F j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

theorem relPrime_cofactor (F : I → R) (hF : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (i : I) : IsRelPrime (F i) (cofactor F i) := by
  apply IsRelPrime.prod_right
  intro j hj
  exact hF (Ne.symm (Finset.mem_erase.mp hj).1)

def generationMap (F : I → R) : (I → R) →ₗ[R] R where
  toFun A := ∑ i, A i * cofactor F i
  map_add' A B := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a A := by simp [smul_eq_mul, mul_assoc, Finset.mul_sum]

def sumMap : (I → R) →ₗ[R] R where
  toFun C := ∑ i, C i
  map_add' C D := by simp [Finset.sum_add_distrib]
  map_smul' a C := by simp [smul_eq_mul, Finset.mul_sum]

theorem coefficient_dvd_of_relation (F A : I → R)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (hrel : generationMap F A = 0) (i : I) : F i ∣ A i := by
  have hsum : F i ∣ ∑ j, A j * cofactor F j := by
    change F i ∣ generationMap F A
    rw [hrel]
    exact dvd_zero _
  have hother : F i ∣ ∑ j ∈ Finset.univ.erase i, A j * cofactor F j := by
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_right (dvd_other_cofactor F i j
      (Ne.symm (Finset.mem_erase.mp hj).1)) _
  have hmain : F i ∣ A i * cofactor F i := by
    have hd := dvd_sub hsum hother
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hd
    simpa only [add_sub_cancel_left] using hd
  exact (relPrime_cofactor F hF i).dvd_of_dvd_mul_right hmain

theorem generationMap_diagonal (F C : I → R) :
    generationMap F (fun i => F i * C i) = totalProduct F * ∑ i, C i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (F i * C i) * cofactor F i = totalProduct F * C i
  rw [show (F i * C i) * cofactor F i = (F i * cofactor F i) * C i by ring,
    cofactor_factor]

/-- Reduction at each factor proves the actual full syzygy criterion. -/
theorem syzygy_iff (F A : I → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    generationMap F A = 0 ↔
      ∃ C : I → R, (∀ i, A i = F i * C i) ∧ ∑ i, C i = 0 := by
  constructor
  · intro hrel
    have hdiv := coefficient_dvd_of_relation F A hF hrel
    choose C hC using hdiv
    refine ⟨C, hC, ?_⟩
    have hA : A = fun i => F i * C i := funext hC
    rw [hA, generationMap_diagonal] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left (totalProduct_ne_zero F hF0)
  · rintro ⟨C, hC, hsum⟩
    rw [show A = (fun i => F i * C i) from funext hC, generationMap_diagonal, hsum, mul_zero]

abbrev ZeroSum (R I : Type*) [CommRing R] [Fintype I] :=
  LinearMap.ker (sumMap (R := R) (I := I))

def kernelFromZeroSum (F : I → R) : ZeroSum R I →ₗ[R] LinearMap.ker (generationMap F) where
  toFun C := ⟨fun i => F i * C.val i, by
    rw [LinearMap.mem_ker, generationMap_diagonal]
    have hc : (∑ i, C.val i) = 0 := C.property
    rw [hc, mul_zero]⟩
  map_add' C D := by ext i; simp [mul_add]
  map_smul' a C := by ext i; simp [smul_eq_mul, mul_left_comm]

theorem kernelFromZeroSum_bijective (F : I → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    Function.Bijective (kernelFromZeroSum F) := by
  constructor
  · intro C D hCD
    apply Subtype.ext
    funext i
    have hi := congrFun (congrArg Subtype.val hCD) i
    exact mul_left_cancel₀ (hF0 i) hi
  · intro A
    obtain ⟨C, hC, hsum⟩ := (syzygy_iff F A.val hF0 hF).mp A.property
    refine ⟨⟨C, hsum⟩, ?_⟩
    apply Subtype.ext
    exact (funext hC).symm

def kernelEquivZeroSum (F : I → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    ZeroSum R I ≃ₗ[R] LinearMap.ker (generationMap F) :=
  LinearEquiv.ofBijective (kernelFromZeroSum F) (kernelFromZeroSum_bijective F hF0 hF)

def zeroSumEquiv (R : Type*) [CommRing R] (n : ℕ) :
    (Fin n → R) ≃ₗ[R] ZeroSum R (Fin (n + 1)) where
  toFun T := ⟨Fin.cons (-(∑ i, T i)) T, by
    change (∑ i : Fin (n + 1), Fin.cons (-(∑ i, T i)) T i) = 0
    rw [Fin.sum_univ_succ]
    simp⟩
  invFun C := fun i => C.val i.succ
  left_inv T := rfl
  right_inv C := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero =>
      change -(∑ i : Fin n, C.val i.succ) = C.val 0
      have hc : (∑ i : Fin (n + 1), C.val i) = 0 := C.property
      rw [Fin.sum_univ_succ] at hc
      exact (eq_neg_of_add_eq_zero_left hc).symm
    | succ i => rfl
  map_add' T U := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases <;> simp [Finset.sum_add_distrib, neg_add_rev, add_comm]
  map_smul' a T := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases <;> simp [smul_eq_mul, Finset.mul_sum]

variable {n : ℕ}

def kernelEquiv (F : Fin (n + 1) → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    (Fin n → R) ≃ₗ[R] LinearMap.ker (generationMap F) :=
  (zeroSumEquiv R n).trans (kernelEquivZeroSum F hF0 hF)

def syzygyMap (F : Fin (n + 1) → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    (Fin n → R) →ₗ[R] (Fin (n + 1) → R) :=
  (LinearMap.ker (generationMap F)).subtype.comp (kernelEquiv F hF0 hF).toLinearMap

theorem syzygyMap_injective (F : Fin (n + 1) → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    Function.Injective (syzygyMap F hF0 hF) :=
  Subtype.val_injective.comp (kernelEquiv F hF0 hF).injective

theorem syzygyMap_range_eq_kernel (F : Fin (n + 1) → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    LinearMap.range (syzygyMap F hF0 hF) = LinearMap.ker (generationMap F) := by
  ext A
  constructor
  · rintro ⟨T, rfl⟩
    exact (kernelEquiv F hF0 hF T).property
  · intro hA
    refine ⟨(kernelEquiv F hF0 hF).symm ⟨A, hA⟩, ?_⟩
    exact congrArg Subtype.val ((kernelEquiv F hF0 hF).apply_symm_apply ⟨A, hA⟩)

def syzygyBasis (F : Fin (n + 1) → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    Basis (Fin n) R (LinearMap.ker (generationMap F)) :=
  (Pi.basisFun R (Fin n)).map (kernelEquiv F hF0 hF)

theorem kernel_free (F : Fin (n + 1) → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    Module.Free R (LinearMap.ker (generationMap F)) :=
  Module.Free.of_basis (syzygyBasis F hF0 hF)

theorem kernel_finrank (F : Fin (n + 1) → R) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j))) :
    Module.finrank R (LinearMap.ker (generationMap F)) = n := by
  simpa using Module.finrank_eq_card_basis (syzygyBasis F hF0 hF)

#print axioms syzygy_iff
#print axioms syzygyMap_range_eq_kernel
#print axioms kernel_finrank

end Cylinder.IntersectionResolution

end
