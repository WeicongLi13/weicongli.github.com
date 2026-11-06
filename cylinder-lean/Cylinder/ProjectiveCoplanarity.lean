module

public import Cylinder.ProjectiveCover
public import Cylinder.ProjectiveCylinderChart
public import Cylinder.ProjectionPolynomial

/-!
# Coplanarity of the white configuration is exactly the cylinder property

White coplanarity means that the actual empty primal planes share a
projective point. The complement theorem makes every line through that
point which meets the set a complete affine line. Conversely, an empty
plane contains the actual direction of a complete line of a cylinder.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectiveCoplanarity

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveBalance
open Cylinder.ProjectiveCover Cylinder.ProjectiveCylinderChart
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

/-- All white dual points lie in the actual dual plane corresponding to a primal point. -/
def WhiteCoplanar (S : Finset (Geometry.Point p)) : Prop :=
  ∃ v : PG3 p, ∀ H ∈ whitePoints p S, Incident p v H

theorem incident_infinity_rep_iff (v : PG3 p) :
    Incident p v (infinity p) ↔ v.rep 0 = 0 := by
  have h := incident_mk_mk p v.rep (LinearMap.proj (0 : Fin 4)) v.rep_nonzero
    (by intro h; have := LinearMap.congr_fun h (Pi.single (0 : Fin 4) 1); simpa using this)
  simpa only [Projectivization.mk_rep, infinity, LinearMap.proj_apply] using h

theorem isCylinder_of_whiteCoplanar {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hcoplanar : WhiteCoplanar p S) :
    Geometry.IsCylinder p S := by
  obtain ⟨v, hv⟩ := hcoplanar
  have hvzero : v.rep 0 = 0 :=
    (incident_infinity_rep_iff p v).mp (hv _ (infinity_mem_whitePoints p S))
  let d : Geometry.Point p := fun i => v.rep i.succ
  have hd : d ≠ 0 := by
    intro h
    apply v.rep_nonzero
    funext i
    refine Fin.cases hvzero (fun j => ?_) i
    exact congrFun h j
  have hdir : directionVector p d = v.rep := by
    funext i
    refine Fin.cases hvzero.symm (fun _ => rfl) i
  have hpos : 0 < S.card := by
    rw [hcard]
    exact pow_pos (Fact.out : p.Prime).pos 2
  obtain ⟨base, hbase⟩ := Finset.card_pos.mp hpos
  have hbasePG : affineEmbed p base ∈ pointSet p S :=
    (affineEmbed_mem_pointSet p S base).mpr hbase
  have hline : Geometry.affineLine p base d ⊆ S := by
    intro y hy
    obtain ⟨t, rfl⟩ := (Geometry.mem_affineLine p base d y).mp hy
    apply (affineEmbed_mem_pointSet p S _).mp
    apply (mem_pointSet_iff_no_white p hcard hS _).mpr
    intro H hH hi
    have hbaseNo : ¬ Incident p (affineEmbed p base) H :=
      (mem_whitePoints_iff_no_incident p hS H).mp hH _ hbasePG
    apply hbaseNo
    rw [incident_affine_rep_iff]
    have hdirZero : H.rep (directionVector p d) = 0 := by
      rw [hdir]
      exact hv H hH
    have hEval := functional_on_line p H.rep base d t
    rw [hdirZero, mul_zero, add_zero] at hEval
    exact hEval.symm.trans ((incident_affine_rep_iff p _ H).mp hi)
  exact Geometry.isCylinder_of_inDirection p
    (ProjectionPolynomial.inDirection_of_affineLine_subset p hcard hS hd hline)

theorem whiteCoplanar_of_isCylinder {S : Finset (Geometry.Point p)}
    (hS : Geometry.PDivisible p S) (hcy : Geometry.IsCylinder p S) : WhiteCoplanar p S := by
  obtain ⟨d, hd, base, _, hUnion⟩ := hcy
  have hline : ∀ i : Fin p, Geometry.affineLine p (base i) d ⊆ S := by
    intro i x hx
    rw [hUnion]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  let i0 : Fin p := ⟨0, (Fact.out : p.Prime).pos⟩
  refine ⟨Projectivization.mk (ZMod p) (directionVector p d) (directionVector_ne_zero p hd), ?_⟩
  intro H hH
  have havoid : ∀ x ∈ S, H.rep (affineVector p x) ≠ 0 := by
    intro x hx hzero
    have hNo := (mem_whitePoints_iff_no_incident p hS H).mp hH
      (affineEmbed p x) ((affineEmbed_mem_pointSet p S x).mpr hx)
    exact hNo ((incident_affine_rep_iff p x H).mpr hzero)
  apply (incident_mk_rep_iff p _ (directionVector_ne_zero p hd) H).mpr
  exact functional_direction_zero_of_empty_plane p H.rep havoid (base i0) d (hline i0)

/-- The first coplanarity equivalence in Lemma `lem:coplanarity`. -/
theorem whiteCoplanar_iff_isCylinder {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) :
    WhiteCoplanar p S ↔ Geometry.IsCylinder p S :=
  ⟨isCylinder_of_whiteCoplanar p hcard hS, whiteCoplanar_of_isCylinder p hS⟩

#print axioms isCylinder_of_whiteCoplanar
#print axioms whiteCoplanar_of_isCylinder
#print axioms whiteCoplanar_iff_isCylinder

end Cylinder.ProjectiveCoplanarity

end
