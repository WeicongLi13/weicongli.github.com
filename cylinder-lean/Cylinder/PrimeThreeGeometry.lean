module

public import Cylinder.ProjectiveLineCap

/-!
# The strong cylinder conjecture at prime order three

The geometric line cap makes a noncylinder impossible at this order.
This uses the proved incidence and projection lemmas, without finite
subset enumeration or additional mathematical assumptions.
-/

@[expose] public section

namespace Cylinder.PrimeThreeGeometry

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem strongCylinderConjecture_three : Geometry.StrongCylinderConjecture 3 := by
  intro S hcard hS
  exact ProjectiveLineCap.isCylinder_of_prime_le_three 3 hcard hS (by decide)

#print axioms strongCylinderConjecture_three

end Cylinder.PrimeThreeGeometry
