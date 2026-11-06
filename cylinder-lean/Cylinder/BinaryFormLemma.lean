module
public import Cylinder.BinarySubspace
public import Cylinder.BinaryHomogenization

/-!
# Actual binary homogeneous subspaces

This file transports growth of actual finite-dimensional univariate polynomial
subspaces through the proved homogenization equivalence. Its subspaces live in
the real ring `MvPolynomial (Fin 2) K`.
-/

@[expose] public section
noncomputable section
namespace Cylinder.BinaryFormLemma
open Module
open Cylinder.BinaryGrowth Cylinder.BinaryHomogenization
variable {K : Type*} [Field K]

abbrev BinaryRing (K : Type*) [Field K] := MvPolynomial (Fin 2) K

/-- Multiplication by a specified binary variable. -/
def mulVar (i : Fin 2) : BinaryRing K →ₗ[K] BinaryRing K :=
  LinearMap.mul K (BinaryRing K) (MvPolynomial.X i)

@[simp] theorem mulVar_apply (i : Fin 2) (P : BinaryRing K) :
    mulVar i P = MvPolynomial.X i * P := rfl

/-- The actual space `xU + yU`. -/
def expansion (U : Submodule K (BinaryRing K)) : Submodule K (BinaryRing K) :=
  U.map (mulVar 0) ⊔ U.map (mulVar 1)

theorem homogeneous_finiteDimensional (d : ℕ) :
    FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 2) K d) := by
  let : FiniteDimensional K (Polynomial.degreeLE K d) := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    infer_instance
  exact Module.Finite.of_injective (homogeneousDegreeEquiv d).toLinearMap
    (homogeneousDegreeEquiv d).injective

theorem finiteDimensional_of_homogeneous (U : Submodule K (BinaryRing K)) (d : ℕ)
    (hU : U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d) :
    FiniteDimensional K U := by
  let := homogeneous_finiteDimensional (K := K) d
  exact Submodule.finiteDimensional_of_le hU

theorem expansion_homogeneous (U : Submodule K (BinaryRing K)) (d : ℕ)
    (hU : U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d) :
    expansion U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K (d + 1) := by
  apply sup_le <;> intro P hP
  all_goals
    obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hP
    change (MvPolynomial.X _ * Q).IsHomogeneous (d + 1)
    convert (MvPolynomial.isHomogeneous_X K _).mul (hU hQ) using 1; omega

/-- Setting y=1 preserves dimension on a genuine homogeneous subspace. -/
theorem dehomogenize_finrank (U : Submodule K (BinaryRing K)) (d : ℕ)
    (hU : U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d) :
    finrank K ↥(U.map dehomogenize.toLinearMap) = finrank K U := by
  let f : U →ₗ[K] Polynomial K := dehomogenize.toLinearMap.comp U.subtype
  have hf : Function.Injective f := by
    intro P Q he
    apply Subtype.ext
    exact dehomogenize_injective_on_homogeneous d (hU P.property) (hU Q.property) he
  have hrange : LinearMap.range f = U.map dehomogenize.toLinearMap := by
    ext p
    simp only [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  rw [← hrange]
  exact LinearMap.finrank_range_of_inj hf

theorem dehomogenize_expansion (U : Submodule K (BinaryRing K)) :
    (expansion U).map dehomogenize.toLinearMap =
      U.map dehomogenize.toLinearMap ⊔
        (U.map dehomogenize.toLinearMap).map mulX := by
  have hzero : dehomogenize.toLinearMap.comp (mulVar (K := K) 0) =
      mulX.comp dehomogenize.toLinearMap := by
    apply LinearMap.ext
    intro P
    exact dehomogenize_mul_X_zero P
  have hone : dehomogenize.toLinearMap.comp (mulVar (K := K) 1) =
      dehomogenize.toLinearMap := by
    apply LinearMap.ext
    intro P
    exact dehomogenize_mul_X_one P
  rw [expansion, Submodule.map_sup, ← Submodule.map_comp, ← Submodule.map_comp,
    hzero, hone, Submodule.map_comp, sup_comm]

theorem dehomogenize_nonzero (U : Submodule K (BinaryRing K)) (d : ℕ)
    (hU : U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d) (hU0 : U ≠ ⊥) :
    U.map dehomogenize.toLinearMap ≠ ⊥ := by
  obtain ⟨P, hP, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  intro hz
  have hp : dehomogenize P ∈ U.map dehomogenize.toLinearMap :=
    Submodule.mem_map_of_mem hP
  rw [hz, Submodule.mem_bot] at hp
  apply hP0
  exact dehomogenize_injective_on_homogeneous d (hU hP)
    (MvPolynomial.isHomogeneous_zero (Fin 2) K d) (by simpa using hp)

/-- The growth assertion of the paper's binary-form lemma, for actual homogeneous polynomials. -/
theorem binary_growth (U : Submodule K (BinaryRing K)) (d : ℕ)
    (hU : U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d) (hU0 : U ≠ ⊥) :
    finrank K U + 1 ≤ finrank K (expansion U) := by
  let := finiteDimensional_of_homogeneous U d hU
  have hv := finrank_growth (U.map dehomogenize.toLinearMap)
    (dehomogenize_nonzero U d hU hU0)
  rw [dehomogenize_finrank U d hU, ← dehomogenize_expansion,
    dehomogenize_finrank (expansion U) (d + 1) (expansion_homogeneous U d hU)] at hv
  exact hv


/-- Dehomogenization maps the full homogeneous degree-d space onto the full
univariate space of degree at most d. -/
theorem dehomogenize_homogeneous (d : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 2) K d).map dehomogenize.toLinearMap =
      Polynomial.degreeLE K d := by
  apply le_antisymm
  · intro p hp
    obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hp
    exact Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp
      (dehomogenize_natDegree_le hP))
  · intro p hp
    refine Submodule.mem_map.mpr ⟨Polynomial.homogenize p d,
      Polynomial.isHomogeneous_homogenize p, ?_⟩
    exact Polynomial.aeval_homogenize_X_one p
      (Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hp))

/-- The homogeneous dehomogenization map determines its subspaces uniquely. -/
theorem submodule_eq_of_dehomogenize_eq (d : ℕ)
    (U V : Submodule K (BinaryRing K))
    (hU : U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d)
    (hV : V ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d)
    (he : U.map dehomogenize.toLinearMap = V.map dehomogenize.toLinearMap) : U = V := by
  apply le_antisymm
  · intro P hP
    have hp : dehomogenize P ∈ V.map dehomogenize.toLinearMap := by
      rw [← he]
      exact Submodule.mem_map_of_mem hP
    obtain ⟨Q, hQ, hQP⟩ := Submodule.mem_map.mp hp
    have heq : Q = P := dehomogenize_injective_on_homogeneous d (hV hQ) (hU hP) hQP
    exact heq ▸ hQ
  · intro P hP
    have hp : dehomogenize P ∈ U.map dehomogenize.toLinearMap := by
      rw [he]
      exact Submodule.mem_map_of_mem hP
    obtain ⟨Q, hQ, hQP⟩ := Submodule.mem_map.mp hp
    have heq : Q = P := dehomogenize_injective_on_homogeneous d (hU hQ) (hV hP) hQP
    exact heq ▸ hQ

/-- The actual subspace G times all binary forms of degree n. -/
def factorSpace (G : BinaryRing K) (n : ℕ) : Submodule K (BinaryRing K) :=
  (MvPolynomial.homogeneousSubmodule (Fin 2) K n).map (LinearMap.mul K (BinaryRing K) G)

theorem dehomogenize_factorSpace (G : BinaryRing K) (n : ℕ) :
    (factorSpace G n).map dehomogenize.toLinearMap =
      (Polynomial.degreeLE K n).map (LinearMap.mul K (Polynomial K) (dehomogenize G)) := by
  have hcomp : dehomogenize.toLinearMap.comp (LinearMap.mul K (BinaryRing K) G) =
      (LinearMap.mul K (Polynomial K) (dehomogenize G)).comp dehomogenize.toLinearMap := by
    apply LinearMap.ext
    intro P
    exact map_mul dehomogenize G P
  rw [factorSpace, ← Submodule.map_comp, hcomp, Submodule.map_comp, dehomogenize_homogeneous]

/-- Equality in binary growth forces a common homogeneous factor and the complete
space of degree-(r-1) binary forms. Here the natural-number degree `d+1-r`
expresses the paper's integer `d-r+1`, including the full-space case r=d+1. -/
theorem binary_equality (U : Submodule K (BinaryRing K)) (d : ℕ)
    (hU : U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d) (hU0 : U ≠ ⊥)
    (heq : finrank K (expansion U) = finrank K U + 1) :
    ∃ G : BinaryRing K, G ≠ 0 ∧ G.IsHomogeneous (d + 1 - finrank K U) ∧
      U = factorSpace G (finrank K U - 1) := by
  let := finiteDimensional_of_homogeneous U d hU
  let V := U.map dehomogenize.toLinearMap
  have hV0 : V ≠ ⊥ := dehomogenize_nonzero U d hU hU0
  have hVr : finrank K V = finrank K U := dehomogenize_finrank U d hU
  have hVd : V ≤ Polynomial.degreeLE K d := by
    intro p hp
    obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hp
    exact Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp
      (dehomogenize_natDegree_le (hU hP)))
  have hVe : finrank K ↥(V ⊔ V.map mulX) = finrank K V + 1 := by
    change finrank K ↥(U.map dehomogenize.toLinearMap ⊔
      (U.map dehomogenize.toLinearMap).map mulX) =
      finrank K ↥(U.map dehomogenize.toLinearMap) + 1
    rw [← dehomogenize_expansion,
      dehomogenize_finrank (expansion U) (d + 1) (expansion_homogeneous U d hU),
      dehomogenize_finrank U d hU]
    exact heq
  obtain ⟨g, hg0, hgd, hrd, hg⟩ := Cylinder.BinarySubspace.equality_factor_degree V hV0 hVe d hVd
  rw [hVr] at hgd hrd hg
  have hr : 0 < finrank K U := by
    by_contra hn
    exact hU0 (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hn))
  let G := Polynomial.homogenize g (d + 1 - finrank K U)
  have hG : G.IsHomogeneous (d + 1 - finrank K U) := Polynomial.isHomogeneous_homogenize g
  have hGde : dehomogenize G = g := Polynomial.aeval_homogenize_X_one g hgd
  have hG0 : G ≠ 0 := by
    intro hz
    apply hg0
    rw [← hGde, hz, map_zero]
  refine ⟨G, hG0, hG, ?_⟩
  have hS : factorSpace G (finrank K U - 1) ≤
      MvPolynomial.homogeneousSubmodule (Fin 2) K d := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hP
    change (G * Q).IsHomogeneous d
    have hsum : d + 1 - finrank K U + (finrank K U - 1) = d := by omega
    exact hsum ▸ hG.mul hQ
  apply submodule_eq_of_dehomogenize_eq d U _ hU hS
  rw [dehomogenize_factorSpace, hGde, ← Polynomial.degreeLT_succ_eq_degreeLE]
  have hrr : finrank K U - 1 + 1 = finrank K U := by omega
  rw [hrr]
  exact hg


/-- The full statement of Lemma `lem:binary`, with explicit dimension r and
an exact total-degree assertion for the nonzero common homogeneous factor. -/
theorem binary_lemma (U : Submodule K (BinaryRing K)) (d r : ℕ)
    (hU : U ≤ MvPolynomial.homogeneousSubmodule (Fin 2) K d) (hU0 : U ≠ ⊥)
    (hr : finrank K U = r) :
    r + 1 ≤ finrank K (expansion U) ∧
      (finrank K (expansion U) = r + 1 →
        ∃ G : BinaryRing K, G ≠ 0 ∧ G.IsHomogeneous (d + 1 - r) ∧
          G.totalDegree = d + 1 - r ∧ U = factorSpace G (r - 1)) := by
  constructor
  · simpa [hr] using binary_growth U d hU hU0
  · intro heq
    have he : finrank K (expansion U) = finrank K U + 1 := by simpa [hr] using heq
    obtain ⟨G, hG0, hG, hfac⟩ := binary_equality U d hU hU0 he
    refine ⟨G, hG0, ?_, ?_, ?_⟩
    · simpa [hr] using hG
    · simpa [hr] using hG.totalDegree hG0
    · simpa [hr] using hfac

end Cylinder.BinaryFormLemma




