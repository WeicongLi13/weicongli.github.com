module

public import Cylinder.IntersectionGradedResolution

/-!
# The actual intersection ideal zero set

Its cofactors vanish precisely at points on at least two components.
Consequently the presented ideal is contained in the true vanishing
ideal of every finite subset of those points. Independence in degree
`s-2` is not assumed or concluded here.
-/

@[expose] public section

noncomputable section

namespace Cylinder.IntersectionZeroSet

open MvPolynomial Cylinder.IntersectionResolution Cylinder.IntersectionGradedResolution
open scoped BigOperators Classical

variable {K I : Type*} [Field K] [Fintype I] [Nonempty I]

def OnMultipleComponents (F : I → MvPolynomial (Fin 3) K) (x : Fin 3 → K) : Prop :=
  ∃ i j : I, i ≠ j ∧ eval x (F i) = 0 ∧ eval x (F j) = 0

theorem eval_cofactor (F : I → MvPolynomial (Fin 3) K) (x : Fin 3 → K) (i : I) :
    eval x (cofactor F i) = ∏ j ∈ Finset.univ.erase i, eval x (F j) := map_prod _ _ _

theorem cofactors_vanish_iff (F : I → MvPolynomial (Fin 3) K) (x : Fin 3 → K) :
    (∀ i, eval x (cofactor F i) = 0) ↔ OnMultipleComponents F x := by
  constructor
  · intro h
    let i : I := Classical.choice (inferInstance : Nonempty I)
    obtain ⟨j, hj, hFj⟩ := Finset.prod_eq_zero_iff.mp ((eval_cofactor F x i) ▸ h i)
    obtain ⟨k, hk, hFk⟩ := Finset.prod_eq_zero_iff.mp ((eval_cofactor F x j) ▸ h j)
    exact ⟨j, k, Ne.symm (Finset.mem_erase.mp hk).1, hFj, hFk⟩
  · rintro ⟨i, j, hij, hFi, hFj⟩ k
    rw [eval_cofactor]
    by_cases hik : i = k
    · subst k
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hFj
    · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩) hFi

theorem ideal_vanish_iff_cofactors (F : I → MvPolynomial (Fin 3) K) (x : Fin 3 → K) :
    (∀ P ∈ componentIdeal F, eval x P = 0) ↔ ∀ i, eval x (cofactor F i) = 0 := by
  constructor
  · intro h i
    apply h
    exact ⟨Pi.single i 1, generationMap_single F i⟩
  · intro h P hP
    obtain ⟨A, hA⟩ := hP
    rw [← hA]
    change eval x (∑ i, A i * cofactor F i) = 0
    simp only [map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem ideal_zero_set_iff (F : I → MvPolynomial (Fin 3) K) (x : Fin 3 → K) :
    (∀ P ∈ componentIdeal F, eval x P = 0) ↔ OnMultipleComponents F x :=
  (ideal_vanish_iff_cofactors F x).trans (cofactors_vanish_iff F x)

theorem ideal_vanishes_on_finite_subset (F : I → MvPolynomial (Fin 3) K)
    (J : Finset (Fin 3 → K)) (hJ : ∀ x ∈ J, OnMultipleComponents F x) :
    ∀ P ∈ componentIdeal F, ∀ x ∈ J, eval x P = 0 := by
  intro P hP x hx
  exact (ideal_zero_set_iff F x).mpr (hJ x hx) P hP

#print axioms cofactors_vanish_iff
#print axioms ideal_vanishes_on_finite_subset

end Cylinder.IntersectionZeroSet

end
