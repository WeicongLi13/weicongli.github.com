module

public import Cylinder.GlobalTwistPairSections

/-! Actual twisting-sheaf sections on a two-chart intersection have
literal homogeneous polynomial numerators and coordinate-power
denominators, with the original integer degree balance. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.GlobalTwistPairSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistPairFractionRepresentatives

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistPairSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem pairOpen_le_second (i j : Option (Fin 2)) : pairOpen K i j ≤ coordinateOpen K j := by
  rw [pairOpen_eq]
  exact inf_le_right

theorem coordinate_product_avoids (i j : Option (Fin 2)) (q : pairOpen K i j) (a b : ℕ) :
    X i ^ a * X j ^ b ∉ q.val.asHomogeneousIdeal :=
  q.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
    (coordinate_power_avoids K i (pairOpen K i j) (pairOpen_le_first K i j) q a)
    (coordinate_power_avoids K j (pairOpen K i j) (pairOpen_le_second K i j) q b)

theorem exists_pair_fraction (i j : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, pairOpen K i j)) :
    ∃ (m a b : ℕ) (H : PlaneRing K), H.IsHomogeneous m ∧ (m : ℤ) - a - b = v ∧
      ∀ q : pairOpen K i j, s.val q = Localization.mk H
        ⟨X i ^ a * X j ^ b, coordinate_product_avoids K i j q a b⟩ := by
  obtain ⟨c, rfl⟩ := (sectionLinearEquiv K i j v).surjective s
  obtain ⟨k, H, hH, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading K) (product_homogeneous K i j) c
  refine ⟨v.toNat + k * 2, (-v).toNat + k, k, X i ^ v.toNat * H, ?_, by omega, ?_⟩
  · exact (isHomogeneous_X_pow i v.toNat).mul (by simpa using hH)
  · intro q
    refine (sectionLinearEquiv_fraction K i j v k H hH q).trans ?_
    apply congrArg (Localization.mk (X i ^ v.toNat * H))
    apply Subtype.ext
    change X i ^ (-v).toNat * (X i * X j) ^ k = X i ^ ((-v).toNat + k) * X j ^ k
    rw [mul_pow, pow_add]
    ring

end Cylinder.GlobalTwistPairFractionRepresentatives
end
