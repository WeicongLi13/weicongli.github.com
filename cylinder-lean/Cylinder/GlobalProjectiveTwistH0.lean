module

public import Cylinder.GlobalTwistH0Charts
public import Cylinder.GlobalHomogeneousSections
public import Cylinder.GlobalTwistCoordinateFractionRepresentatives
public import Cylinder.HomogeneousFactors
public import Mathlib.Algebra.MvPolynomial.Division

/-! Global sections of the actual twisting sheaf are exactly the
original homogeneous polynomials. Two charts remove the denominator;
the other charts verify the value at every actual Proj point. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.CoordinateChartPermutation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalProjectiveTwistH0

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistCoordinateFractionRepresentatives Cylinder.ActualTorusGenericPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def onChart (v : ℤ) (s : sectionsSubmodule K v ⊤) (i : Option (Fin 2)) :
    Γ(twist K v, coordinateOpen K i) :=
  (twist K v).presheaf.map (homOfLE (show coordinateOpen K i ≤ ⊤ from le_top)).op s

theorem global_fractions_cross (v : ℤ) (s : sectionsSubmodule K v ⊤)
    (i j : Option (Fin 2)) (m n : ℕ) (H G : PlaneRing K)
    (hs : ∀ q : coordinateOpen K i, (onChart K v s i).val q = Localization.mk H
      ⟨X i ^ m, coordinate_power_avoids K i (coordinateOpen K i) le_rfl q m⟩)
    (ht : ∀ q : coordinateOpen K j, (onChart K v s j).val q = Localization.mk G
      ⟨X j ^ n, coordinate_power_avoids K j (coordinateOpen K j) le_rfl q n⟩) :
    H * X j ^ n = G * X i ^ m := by
  apply coordinate_fraction_cross_eq K i j m n H G
  exact (hs ⟨genericPoint K, genericPoint_mem_coordinateOpen K i⟩).symm.trans
    (ht ⟨genericPoint K, genericPoint_mem_coordinateOpen K j⟩)

theorem global_value_of_quotient (v : ℤ) (s : sectionsSubmodule K v ⊤)
    (i : Option (Fin 2)) (n : ℕ) (H P : PlaneRing K)
    (hs : ∀ q : coordinateOpen K i, (onChart K v s i).val q = Localization.mk H
      ⟨X i ^ n, coordinate_power_avoids K i (coordinateOpen K i) le_rfl q n⟩)
    (hHP : H = X i ^ n * P) (q : (⊤ : (plane K).Opens)) :
    s.val q = algebraMap (PlaneRing K) (FullLocal K q.val) P := by
  obtain ⟨j, hj⟩ := not_forall.mp
    (ProjectiveCompleteIntersectionCover.not_all_variables_mem q.val)
  let qj : coordinateOpen K j := ⟨q.val, hj⟩
  obtain ⟨d, k, G, hG, hdG, hg⟩ :=
    exists_coordinate_fraction K j v (onChart K v s j)
  have hcross := global_fractions_cross K v s i j n k H G hs hg
  have he : P * X j ^ k = G := by
    apply mul_left_cancel₀ (pow_ne_zero n (X_ne_zero i))
    calc
      _ = (X i ^ n * P) * X j ^ k := by ring
      _ = H * X j ^ k := by rw [hHP]
      _ = G * X i ^ n := hcross
      _ = _ := mul_comm _ _
  calc
    s.val q = (onChart K v s j).val qj := rfl
    _ = Localization.mk G
      ⟨X j ^ k, coordinate_power_avoids K j (coordinateOpen K j) le_rfl qj k⟩ := hg qj
    _ = Localization.mk P (1 : q.val.asHomogeneousIdeal.toIdeal.primeCompl) :=
      fraction_eq_of_cross_mul K q.val G P _ _ (by
        change G * 1 = P * X j ^ k
        simpa only [mul_one] using he.symm)
    _ = _ := Localization.mk_one_eq_algebraMap P

theorem coordinate_powers_relPrime (i j : Option (Fin 2)) (hij : i ≠ j) (m n : ℕ) :
    IsRelPrime (X i ^ m : PlaneRing K) (X j ^ n) := by
  have hc : IsRelPrime (X i : PlaneRing K) (X j) :=
    (MvPolynomial.X_prime (i := i) (R := K)).irreducible.isRelPrime_iff_not_dvd.mpr
      (by simpa using hij)
  exact hc.pow

theorem polynomialSection_surjective (v : ℤ) :
    Function.Surjective (GlobalHomogeneousSections.polynomialSection K v) := by
  intro s
  obtain ⟨m, n, H, hH, hdH, hs⟩ := exists_coordinate_fraction K none v (onChart K v s none)
  obtain ⟨d, k, G, hG, hdG, hg⟩ := exists_coordinate_fraction K (some 0) v
    (onChart K v s (some 0))
  have hcross := global_fractions_cross K v s none (some 0) n k H G hs hg
  have hdvd : (X none ^ n : PlaneRing K) ∣ H * X (some 0) ^ k := by
    rw [hcross]
    exact dvd_mul_left _ _
  obtain ⟨P, hHP⟩ :=
    (coordinate_powers_relPrime K none (some 0) (by simp) n k).dvd_of_dvd_mul_right hdvd
  by_cases hP : P = 0
  · refine ⟨0, ?_⟩
    rw [map_zero]
    apply Subtype.ext
    funext q
    change (0 : FullLocal K q.val) = s.val q
    have he := global_value_of_quotient K v s none n H P hs hHP q
    simpa only [hP, map_zero] using he.symm
  · have hX : (X none ^ n : PlaneRing K) ≠ 0 := pow_ne_zero n (X_ne_zero none)
    have hprod : (X none ^ n * P).IsHomogeneous m := hHP ▸ hH
    have hdeg : n + P.totalDegree = m := by
      have he := hprod.totalDegree (mul_ne_zero hX hP)
      rw [totalDegree_mul_of_isDomain hX hP,
        (isHomogeneous_X_pow none n).totalDegree hX] at he
      exact he
    have hv : 0 ≤ v := by omega
    have hh := HomogeneousFactors.quotient_homogeneous (X none ^ n) P m hX hprod
    rw [(isHomogeneous_X_pow none n).totalDegree hX] at hh
    have hPform : P ∈ PlaneLaurentHomogeneous.integerForms K v := by
      change P ∈ (if 0 ≤ v then homogeneousSubmodule (Option (Fin 2)) K v.toNat else ⊥)
      rw [ite_eq_left hv]
      change P.IsHomogeneous v.toNat
      convert hh using 1
      omega
    refine ⟨⟨P, hPform⟩, ?_⟩
    apply Subtype.ext
    funext q
    exact (global_value_of_quotient K v s none n H P hs hHP q).symm

def polynomialSectionEquiv (v : ℤ) :
    PlaneLaurentHomogeneous.integerForms K v ≃ₗ[K] sectionsSubmodule K v ⊤ :=
  LinearEquiv.ofBijective (GlobalHomogeneousSections.polynomialSection K v)
    ⟨GlobalHomogeneousSections.polynomialSection_injective K v, polynomialSection_surjective K v⟩

theorem polynomialSectionEquiv_apply (v : ℤ)
    (H : PlaneLaurentHomogeneous.integerForms K v) (q : (⊤ : (plane K).Opens)) :
    (polynomialSectionEquiv K v H).val q =
      algebraMap (PlaneRing K) (FullLocal K q.val) H.val := rfl

def sectionsEquivForms (v : ℤ) :
    sectionsSubmodule K v ⊤ ≃ₗ[K] PlaneLaurentHomogeneous.integerForms K v :=
  (polynomialSectionEquiv K v).symm

instance global_sections_finiteDimensional (v : ℤ) :
    FiniteDimensional K (sectionsSubmodule K v ⊤) :=
  Module.Finite.of_surjective (GlobalHomogeneousSections.polynomialSection K v)
    (polynomialSection_surjective K v)

theorem global_sections_finrank (v : ℤ) :
    Module.finrank K (sectionsSubmodule K v ⊤) =
      Module.finrank K (PlaneLaurentHomogeneous.integerForms K v) :=
  (polynomialSectionEquiv K v).symm.finrank_eq

theorem global_sections_zero_of_negative (v : ℤ) (hv : v < 0)
    (s : sectionsSubmodule K v ⊤) : s = 0 := by
  apply (sectionsEquivForms K v).injective
  rw [map_zero]
  apply Subtype.ext
  have hbot : PlaneLaurentHomogeneous.integerForms K v = ⊥ := by
    simp only [PlaneLaurentHomogeneous.integerForms, ite_eq_right (not_le.mpr hv)]
  exact (Submodule.mem_bot K).mp (hbot ▸ (sectionsEquivForms K v s).property)

end Cylinder.GlobalProjectiveTwistH0
end
