import Cylinder.SmallPrimeCases
import Cylinder.CylinderOfBMMCondition
import Cylinder.CylinderNecessity

/-! All prime cases of the cylinder argument, with the remaining BMM
classification retained as an explicit hypothesis in the large cases. -/

namespace Cylinder.ConditionalMain

theorem strongCylinderConjecture_of_bmm (p : ℕ) [Fact p.Prime]
    (hBMM : 11 ≤ p → WhitePlaneBMMCondition.BMMClassification p) :
    Geometry.StrongCylinderConjecture p := by
  by_cases hp : 11 ≤ p
  · exact CylinderOfBMMCondition.strongCylinderConjecture_of_bmm p hp (hBMM hp)
  · exact SmallPrimeCases.strongCylinderConjecture_below_eleven p (by omega)

theorem cylinder_iff_pDivisible_of_bmm (p : ℕ) [Fact p.Prime]
    (hBMM : 11 ≤ p → WhitePlaneBMMCondition.BMMClassification p)
    (S : Finset (Geometry.Point p)) (hcard : S.card = p ^ 2) :
    Geometry.IsCylinder p S ↔ Geometry.PDivisible p S :=
  ⟨fun h => Geometry.cylinder_pDivisible p h,
    fun h => strongCylinderConjecture_of_bmm p hBMM S hcard h⟩

end Cylinder.ConditionalMain
