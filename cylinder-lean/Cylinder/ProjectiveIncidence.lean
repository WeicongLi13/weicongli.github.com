module

public import Cylinder.ProjectiveGeometry
public import Lean.Elab.Tactic.Omega

/-!
# Point-plane incidence counts in the actual finite projective space

The planes through a point are the projectivization of its annihilator.
The planes through two distinct points are the projectivization of the
annihilator of their two-dimensional span. These are actual equivalences
of finite types, rather than assumed incidence numbers.
-/

@[expose] public section

namespace Cylinder.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Cylinder.ProjectiveGeometry

section General

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem submodule_le_iff_rep_mem (x : Projectivization K V) (W : Submodule K V) :
    x.submodule ≤ W ↔ x.rep ∈ W := by
  rw [x.submodule_eq, Submodule.span_singleton_le_iff_mem]

/-- Projectivizing a vector subspace gives exactly the ambient points in that subspace. -/
noncomputable def projectivizationSubmoduleEquiv (W : Submodule K V) :
    Projectivization K W ≃ {x : Projectivization K V // x.submodule ≤ W} :=
  Equiv.ofBijective
    (fun u => ⟨Projectivization.map W.subtype W.subtype_injective u, by
      induction u using Projectivization.ind with
      | h u hu =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact u.property⟩)
    (by
      constructor
      · intro u v huv
        exact Projectivization.map_injective W.subtype W.subtype_injective
          (congrArg Subtype.val huv)
      · intro x
        have hrep : x.val.rep ∈ W := (submodule_le_iff_rep_mem x.val W).mp x.property
        let v : W := ⟨x.val.rep, hrep⟩
        have hv : v ≠ 0 := fun h => x.val.rep_nonzero (congrArg Subtype.val h)
        refine ⟨Projectivization.mk K v hv, ?_⟩
        apply Subtype.ext
        change Projectivization.map W.subtype W.subtype_injective
          (Projectivization.mk K v hv) = x.val
        rw [Projectivization.map_mk]
        exact Projectivization.mk_rep x.val)

end General

variable (p : ℕ) [Fact p.Prime]

theorem incident_iff_submodule_le (x : PG3 p) (H : DualPoint p) :
    Incident p x H ↔ H.submodule ≤ x.submodule.dualAnnihilator := by
  rw [submodule_le_iff_rep_mem, x.submodule_eq, Submodule.mem_dualAnnihilator]
  constructor
  · intro h v hv
    change H.rep x.rep = 0 at h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [map_smul, h]
  · intro h
    exact h x.rep (Submodule.mem_span_singleton_self _)

/-- The exact finite type of planes containing a point. -/
noncomputable def planesThroughEquiv (x : PG3 p) :
    Projectivization (ZMod p) x.submodule.dualAnnihilator ≃
      {H : DualPoint p // Incident p x H} :=
  (projectivizationSubmoduleEquiv x.submodule.dualAnnihilator).trans
    (Equiv.subtypeEquivRight (fun H => (incident_iff_submodule_le p x H).symm))

theorem finrank_point_annihilator (x : PG3 p) :
    Module.finrank (ZMod p) x.submodule.dualAnnihilator = 3 := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq x.submodule
  rw [Projectivization.finrank_submodule] at h
  have hV : Module.finrank (ZMod p) (ProjectiveGeometry.Vector p) = 4 := by simp [ProjectiveGeometry.Vector]
  rw [hV] at h
  omega

theorem card_planesThrough (x : PG3 p) :
    Nat.card {H : DualPoint p // Incident p x H} = p ^ 2 + p + 1 := by
  rw [← Nat.card_congr (planesThroughEquiv p x)]
  have h := Projectivization.card_of_finrank (ZMod p) x.submodule.dualAnnihilator
    (finrank_point_annihilator p x)
  simpa [Finset.sum_range_succ, Nat.card_eq_fintype_card,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- The vector span of two homogeneous representatives. -/
noncomputable def pairSpan (x y : PG3 p) : Submodule (ZMod p) (Vector p) :=
  Submodule.span (ZMod p) (Set.range ![x.rep, y.rep])

theorem finrank_pairSpan (x y : PG3 p) (hxy : x ≠ y) :
    Module.finrank (ZMod p) (pairSpan p x y) = 2 := by
  have hlin := (Projectivization.linearIndependent_pair_iff_ne (D := x) (D' := y)).mpr hxy
  unfold pairSpan
  simpa only [Fintype.card_fin] using finrank_span_eq_card hlin

theorem incident_pair_iff_submodule_le (x y : PG3 p) (H : DualPoint p) :
    Incident p x H ∧ Incident p y H ↔
      H.submodule ≤ (pairSpan p x y).dualAnnihilator := by
  rw [submodule_le_iff_rep_mem]
  change (H.rep x.rep = 0 ∧ H.rep y.rep = 0) ↔
    H.rep ∈ (Submodule.span (ZMod p) (Set.range ![x.rep, y.rep])).dualAnnihilator
  rw [← SetLike.mem_coe, Submodule.coe_dualAnnihilator_span]
  simp [Set.insert_subset_iff, Set.singleton_subset_iff, LinearMap.mem_ker, and_comm]

/-- The exact finite type of planes containing both points. -/
noncomputable def planesThroughPairEquiv (x y : PG3 p) :
    Projectivization (ZMod p) (pairSpan p x y).dualAnnihilator ≃
      {H : DualPoint p // Incident p x H ∧ Incident p y H} :=
  (projectivizationSubmoduleEquiv (pairSpan p x y).dualAnnihilator).trans
    (Equiv.subtypeEquivRight (fun H => (incident_pair_iff_submodule_le p x y H).symm))

theorem finrank_pair_annihilator (x y : PG3 p) (hxy : x ≠ y) :
    Module.finrank (ZMod p) (pairSpan p x y).dualAnnihilator = 2 := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (pairSpan p x y)
  rw [finrank_pairSpan p x y hxy] at h
  have hV : Module.finrank (ZMod p) (ProjectiveGeometry.Vector p) = 4 := by simp [ProjectiveGeometry.Vector]
  rw [hV] at h
  omega

theorem card_planesThroughPair (x y : PG3 p) (hxy : x ≠ y) :
    Nat.card {H : DualPoint p // Incident p x H ∧ Incident p y H} = p + 1 := by
  rw [← Nat.card_congr (planesThroughPairEquiv p x y)]
  exact Projectivization.card_of_finrank_two (ZMod p) (pairSpan p x y).dualAnnihilator
    (finrank_pair_annihilator p x y hxy) |>.trans (by simp [Nat.card_eq_fintype_card])

#print axioms projectivizationSubmoduleEquiv
#print axioms card_planesThrough
#print axioms card_planesThroughPair

end Cylinder.ProjectiveIncidence
