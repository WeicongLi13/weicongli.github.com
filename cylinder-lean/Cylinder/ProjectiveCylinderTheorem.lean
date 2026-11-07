import Cylinder.ProjectiveSetChartCylinder
import Cylinder.MainTheorem

/-! The unnumbered projective form of the main theorem (Theorem 1.1*).
Its input is an arbitrary finite subset of actual PG(3,p), and its output
is the exact union of p distinct concurrent genuine projective lines with
their common point removed. -/

namespace Cylinder.ProjectiveCylinderTheorem

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveSetChart
open scoped Classical

/-- The projective strong cylinder theorem, with an arbitrary prescribed
empty plane at infinity and no prior affine-image hypothesis. -/
theorem projective_strongCylinder (p : ℕ) [Fact p.Prime]
    (H : DualPoint p) (S : Finset (PG3 p))
    (havoid : ∀ x ∈ S, ¬ Incident p x H)
    (hcard : S.card = p ^ 2)
    (hplanes : ∀ K : DualPoint p, p ∣ (S.filter (fun x => Incident p x K)).card) :
    IsProjectiveCylinder p H S := by
  obtain ⟨g, hg⟩ := exists_chart p H
  have hc : (chartSet p g S).card = p ^ 2 :=
    (chartSet_card p g H hg S havoid).trans hcard
  have hd : Geometry.PDivisible p (chartSet p g S) :=
    chartSet_pDivisible p g H hg S havoid hplanes
  exact isProjectiveCylinder_of_chart p g H hg S havoid
    (MainTheorem.strongCylinderConjecture p (chartSet p g S) hc hd)

#print axioms projective_strongCylinder

end Cylinder.ProjectiveCylinderTheorem
