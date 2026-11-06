module

public import Cylinder.ProjectiveIncidence
public import Lean.Elab.Tactic.Omega

/-!
# All actual dual projective planes are indexed by primal points

A three-dimensional subspace of the four-dimensional dual space is
the annihilator of the one-dimensional span of a nonzero primal vector.
This supplies the complete dual-plane parameterisation used by the cap bound.
-/

@[expose] public section

noncomputable section

namespace Cylinder.DualPlaneModel

open Cylinder.ProjectiveGeometry
open scoped Classical LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

def dualPlanePoints (W : Submodule (ZMod p) (Module.Dual (ZMod p) (ProjectiveGeometry.Vector p))) :
    Finset (DualPoint p) := Finset.univ.filter (fun H => H.submodule ≤ W)

theorem exists_primal_point
    (W : Submodule (ZMod p) (Module.Dual (ZMod p) (ProjectiveGeometry.Vector p)))
    (hW : Module.finrank (ZMod p) W = 3) :
    ∃ v : PG3 p, W = v.submodule.dualAnnihilator := by
  have htotal := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hdual : Module.finrank (ZMod p)
      (Module.Dual (ZMod p) (ProjectiveGeometry.Vector p)) = 4 := by
    simp [ProjectiveGeometry.Vector, Subspace.dual_finrank_eq]
  have hann : Module.finrank (ZMod p) W.dualAnnihilator = 1 := by
    rw [hW, hdual] at htotal
    omega
  have hbot : W.dualAnnihilator ≠ ⊥ := by
    intro hz
    rw [hz] at hann
    simp at hann
  obtain ⟨f, hf, hfne⟩ := (Submodule.ne_bot_iff W.dualAnnihilator).mp hbot
  let v : ProjectiveGeometry.Vector p :=
    (Module.evalEquiv (ZMod p) (ProjectiveGeometry.Vector p)).symm f
  have hv : v ≠ 0 := by
    intro hz
    apply hfne
    calc
      f = (Module.evalEquiv (ZMod p) (ProjectiveGeometry.Vector p)) v :=
        ((Module.evalEquiv (ZMod p) (ProjectiveGeometry.Vector p)).apply_symm_apply f).symm
      _ = 0 := by rw [hz, map_zero]
  let P : PG3 p := Projectivization.mk (ZMod p) v hv
  have hzero : ∀ L ∈ W, L v = 0 := by
    intro L hL
    change L ((Module.evalEquiv (ZMod p) (ProjectiveGeometry.Vector p)).symm f) = 0
    rw [Module.apply_evalEquiv_symm_apply]
    exact ((Submodule.mem_dualAnnihilator (W := W) f).mp hf) L hL
  have hle : W ≤ P.submodule.dualAnnihilator := by
    intro L hL
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    change x ∈ (Projectivization.mk (ZMod p) v hv).submodule at hx
    rw [Projectivization.submodule_mk] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [map_smul, hzero L hL]
  refine ⟨P, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  exact hW.trans (ProjectiveIncidence.finrank_point_annihilator p P).symm

theorem points_eq_incident
    (W : Submodule (ZMod p) (Module.Dual (ZMod p) (ProjectiveGeometry.Vector p)))
    (hW : Module.finrank (ZMod p) W = 3) :
    ∃ v : PG3 p, dualPlanePoints p W = Finset.univ.filter (fun H => Incident p v H) := by
  obtain ⟨v, hv⟩ := exists_primal_point p W hW
  refine ⟨v, ?_⟩
  ext H
  simp only [dualPlanePoints, Finset.mem_filter, Finset.mem_univ, true_and, hv]
  exact (ProjectiveIncidence.incident_iff_submodule_le p v H).symm

end Cylinder.DualPlaneModel

end
