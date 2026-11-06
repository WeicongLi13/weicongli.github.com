import Cylinder.SmallPrimeGeometry
import Cylinder.PrimeTwoGeometry
import Cylinder.PrimeThreeGeometry

namespace Cylinder.SmallPrimeCases

theorem strongCylinderConjecture_below_eleven (p : ℕ) [Fact p.Prime] (hp : p < 11) :
    Geometry.StrongCylinderConjecture p := by
  have hprime := (Fact.out : p.Prime)
  interval_cases p <;> first
    | exact PrimeTwoGeometry.strongCylinderConjecture_two
    | exact PrimeThreeGeometry.strongCylinderConjecture_three
    | exact SmallPrimeGeometry.strongCylinderConjecture_five
    | exact SmallPrimeGeometry.strongCylinderConjecture_seven
    | (exfalso; revert hprime; decide)

end Cylinder.SmallPrimeCases
