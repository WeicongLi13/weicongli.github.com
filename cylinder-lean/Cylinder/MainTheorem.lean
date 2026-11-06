import Cylinder.BMMTheorem
import Cylinder.ConditionalMain

/-! The strong cylinder theorem for every prime. No classification or
other mathematical statement remains as a hypothesis. -/

namespace Cylinder.MainTheorem

theorem strongCylinderConjecture (p : ℕ) [Fact p.Prime] :
    Geometry.StrongCylinderConjecture p :=
  ConditionalMain.strongCylinderConjecture_of_bmm p
    (fun _ => BMMTheorem.bmm_classification p)

theorem cylinder_iff_pDivisible (p : ℕ) [Fact p.Prime]
    (S : Finset (Geometry.Point p)) (hcard : S.card = p ^ 2) :
    Geometry.IsCylinder p S ↔ Geometry.PDivisible p S :=
  ⟨fun h => Geometry.cylinder_pDivisible p h,
    fun h => strongCylinderConjecture p S hcard h⟩

theorem cylinder_of_plane_divisibility (p : ℕ) [Fact p.Prime]
    (S : Finset (Geometry.Point p)) (hcard : S.card = p ^ 2)
    (hplanes : ∀ (a : Geometry.Point p), a ≠ 0 → ∀ b : ZMod p,
      p ∣ (S.filter (fun x => Geometry.pairing p a x = b)).card) :
    Geometry.IsCylinder p S :=
  strongCylinderConjecture p S hcard hplanes

end Cylinder.MainTheorem
