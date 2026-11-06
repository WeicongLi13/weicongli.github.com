module

public import Cylinder.WhitePlaneHyperfocus
public import Cylinder.BMMMatchingParity
public import Cylinder.BlackProjectionRationalLines
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! An actual dual plane is put in three coordinates. Its literal white and
black slices give the arc and blocker objects used by the proved BMM geometry. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.WhitePlaneCoordinates

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.ProjectiveBlackLine Cylinder.WhitePlaneHyperfocus
open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct

variable (p : ℕ) [Fact p.Prime]

local instance : Fintype (PlanePoint (ZMod p)) := Fintype.ofFinite _

def planeEquiv (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : T ≃ₗ[ZMod p] (Fin 3 → ZMod p) := by
  let : Module.Free (ZMod p) T := Module.Free.of_divisionRing (ZMod p) T
  exact LinearEquiv.ofFinrankEq (R := ZMod p) T (Fin 3 → ZMod p) (by simpa using hT)

def planeMap (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : (Fin 3 → ZMod p) →ₗ[ZMod p] DualSpace p :=
  T.subtype.comp (planeEquiv p T hT).symm.toLinearMap

theorem planeMap_injective (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : Function.Injective (planeMap p T hT) :=
  T.subtype_injective.comp (planeEquiv p T hT).symm.injective

def planePoint (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : PlanePoint (ZMod p) → DualPoint p :=
  Projectivization.map (planeMap p T hT) (planeMap_injective p T hT)

theorem planePoint_injective (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : Function.Injective (planePoint p T hT) :=
  Projectivization.map_injective (planeMap p T hT) (planeMap_injective p T hT)

theorem planePoint_submodule (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) (P : PlanePoint (ZMod p)) :
    (planePoint p T hT P).submodule = P.submodule.map (planeMap p T hT) := by
  induction P using Projectivization.ind with
  | h v hv =>
    simp only [planePoint, Projectivization.map_mk, Projectivization.submodule_mk,
      Submodule.map_span, Set.image_singleton]

theorem planePoint_mem (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) (P : PlanePoint (ZMod p)) :
    (planePoint p T hT P).submodule ≤ T := by
  rw [planePoint_submodule]
  intro x hx
  obtain ⟨v, _, rfl⟩ := Submodule.mem_map.mp hx
  exact ((planeEquiv p T hT).symm v).property

theorem planePoint_surjective_on (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) (H : DualPoint p) (hH : H.submodule ≤ T) :
    ∃ P : PlanePoint (ZMod p), planePoint p T hT P = H := by
  let v : T := ⟨H.rep, (ProjectiveIncidence.submodule_le_iff_rep_mem H T).mp hH⟩
  have hv : v ≠ 0 := fun h => H.rep_nonzero (congrArg Subtype.val h)
  let w := planeEquiv p T hT v
  have hw : w ≠ 0 := fun h => hv ((planeEquiv p T hT).injective (by simpa only [map_zero] using h))
  refine ⟨Projectivization.mk (ZMod p) w hw, ?_⟩
  rw [planePoint, Projectivization.map_mk]
  have heq : planeMap p T hT w = H.rep := by simp [planeMap, w, v]
  simpa only [heq] using Projectivization.mk_rep H

def planeWhite (S : Finset (Geometry.Point p)) (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : Finset (PlanePoint (ZMod p)) :=
  Finset.univ.filter (fun P => planePoint p T hT P ∈ whitePoints p S)

def planeBlack (S : Finset (Geometry.Point p)) (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : Finset (PlanePoint (ZMod p)) :=
  Finset.univ.filter (fun P => planePoint p T hT P ∈ blackPoints p S)

theorem planeWhite_image (S : Finset (Geometry.Point p)) (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) :
    (planeWhite p S T hT).image (planePoint p T hT) = whiteSlice p S T := by
  ext H
  constructor
  · intro hH
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hH
    exact Finset.mem_inter.mpr ⟨(mem_linePoints p T _).mpr (planePoint_mem p T hT P),
      (Finset.mem_filter.mp hP).2⟩
  · intro hH
    obtain ⟨hHT, hHW⟩ := Finset.mem_inter.mp hH
    obtain ⟨P, rfl⟩ := planePoint_surjective_on p T hT H ((mem_linePoints p T H).mp hHT)
    exact Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHW⟩, rfl⟩

theorem planeBlack_image (S : Finset (Geometry.Point p)) (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) :
    (planeBlack p S T hT).image (planePoint p T hT) = blackSlice p S T := by
  ext H
  constructor
  · intro hH
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hH
    exact Finset.mem_inter.mpr ⟨(mem_linePoints p T _).mpr (planePoint_mem p T hT P),
      (Finset.mem_filter.mp hP).2⟩
  · intro hH
    obtain ⟨hHT, hHB⟩ := Finset.mem_inter.mp hH
    obtain ⟨P, rfl⟩ := planePoint_surjective_on p T hT H ((mem_linePoints p T H).mp hHT)
    exact Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHB⟩, rfl⟩

theorem planeWhite_card (S : Finset (Geometry.Point p)) (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : (planeWhite p S T hT).card = (whiteSlice p S T).card := by
  rw [← planeWhite_image, Finset.card_image_of_injective _ (planePoint_injective p T hT)]

theorem planeBlack_card (S : Finset (Geometry.Point p)) (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) : (planeBlack p S T hT).card = (blackSlice p S T).card := by
  rw [← planeBlack_image, Finset.card_image_of_injective _ (planePoint_injective p T hT)]

theorem planeWhite_arc {S : Finset (Geometry.Point p)} (harc : IsArc p S)
    (T : Submodule (ZMod p) (DualSpace p)) (hT : Module.finrank (ZMod p) T = 3) :
    LineCap (planeWhite p S T hT) 2 := by
  let : DecidableEq (ZMod p) := Classical.decEq _
  intro c hc
  let U := LinearMap.ker (BlackProjectionRationalLines.dotMap c)
  let L := U.map (planeMap p T hT)
  have hL : Module.finrank (ZMod p) L = 2 := by
    rw [← (Submodule.equivMapOfInjective (planeMap p T hT) (planeMap_injective p T hT) U).finrank_eq]
    exact BlackProjectionRationalLines.dotMap_kernel_finrank c hc
  have hsub : ((planeWhite p S T hT).filter (fun P => dot c P.rep = 0)).image (planePoint p T hT) ⊆
      whiteSlice p S L := by
    intro H hH
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨hPW, hPc⟩ := Finset.mem_filter.mp hP
    refine Finset.mem_inter.mpr ⟨(mem_linePoints p L _).mpr ?_, (Finset.mem_filter.mp hPW).2⟩
    rw [planePoint_submodule]
    apply Submodule.map_mono
    rw [ProjectiveIncidence.submodule_le_iff_rep_mem, LinearMap.mem_ker]
    exact hPc
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (planePoint_injective p T hT)] at hcount
  exact hcount.trans (harc L hL)

theorem plane_slices_disjoint (S : Finset (Geometry.Point p))
    (T : Submodule (ZMod p) (DualSpace p)) (hT : Module.finrank (ZMod p) T = 3) :
    Disjoint (planeWhite p S T hT) (planeBlack p S T hT) := by
  apply Finset.disjoint_left.mpr
  intro P hP hP'
  exact ProjectiveLineCap.white_ne_black p (Finset.mem_filter.mp hP).2
    (Finset.mem_filter.mp hP').2 rfl

theorem plane_blocks_secants {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (T : Submodule (ZMod p) (DualSpace p))
    (hT : Module.finrank (ZMod p) T = 3) :
    BMMArcGeometry.BlocksSecants (planeWhite p S T hT) (planeBlack p S T hT) := by
  intro P hP Q hQ hPQ
  have hPW : planePoint p T hT P ∈ whiteSlice p S T :=
    Finset.mem_inter.mpr ⟨(mem_linePoints p T _).mpr (planePoint_mem p T hT P), (Finset.mem_filter.mp hP).2⟩
  have hQW : planePoint p T hT Q ∈ whiteSlice p S T :=
    Finset.mem_inter.mpr ⟨(mem_linePoints p T _).mpr (planePoint_mem p T hT Q), (Finset.mem_filter.mp hQ).2⟩
  obtain ⟨H, hHB, hHL⟩ := secant_blocker_in_slice p hcard hS T _ _ hPW hQW
    ((planePoint_injective p T hT).ne hPQ)
  obtain ⟨R, rfl⟩ := planePoint_surjective_on p T hT H
    ((mem_linePoints p T H).mp (Finset.mem_inter.mp hHB).1)
  refine ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_inter.mp hHB).2⟩, ?_⟩
  let U := LinearMap.ker (BlackProjectionRationalLines.dotMap (cross P.rep Q.rep))
  have hPU : P.submodule ≤ U := by
    rw [ProjectiveIncidence.submodule_le_iff_rep_mem, LinearMap.mem_ker]
    exact dot_cross_left P.rep Q.rep
  have hQU : Q.submodule ≤ U := by
    rw [ProjectiveIncidence.submodule_le_iff_rep_mem, LinearMap.mem_ker]
    exact dot_cross_right P.rep Q.rep
  have hPL : (planePoint p T hT P).submodule ≤ U.map (planeMap p T hT) := by
    rw [planePoint_submodule]; exact Submodule.map_mono hPU
  have hQL : (planePoint p T hT Q).submodule ≤ U.map (planeMap p T hT) := by
    rw [planePoint_submodule]; exact Submodule.map_mono hQU
  have hRU : R.submodule ≤ U := by
    apply (Submodule.map_le_map_iff_of_injective (planeMap_injective p T hT) _ _).mp
    rw [← planePoint_submodule]
    exact le_trans hHL (pairSpan_le p _ _ _ hPL hQL)
  exact (ProjectiveIncidence.submodule_le_iff_rep_mem R U).mp hRU

theorem actual_generalized_hyperfocus {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) (harc : IsArc p S)
    (T : Submodule (ZMod p) (DualSpace p)) (hT : Module.finrank (ZMod p) T = 3)
    (hwhite : (whiteSlice p S T).Nonempty) :
    LineCap (planeWhite p S T hT) 2 ∧
    Disjoint (planeWhite p S T hT) (planeBlack p S T hT) ∧
    BMMArcGeometry.BlocksSecants (planeWhite p S T hT) (planeBlack p S T hT) ∧
    (planeBlack p S T hT).card + 1 = (planeWhite p S T hT).card := by
  refine ⟨planeWhite_arc p harc T hT, plane_slices_disjoint p S T hT,
    plane_blocks_secants p hcard hS T hT, ?_⟩
  rw [planeBlack_card, planeWhite_card]
  exact slice_card_balance p hcard hS hnon harc T hwhite

theorem actual_plane_white_even {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) (harc : IsArc p S)
    (T : Submodule (ZMod p) (DualSpace p)) (hT : Module.finrank (ZMod p) T = 3)
    (hk : 2 ≤ (whiteSlice p S T).card) : Even (whiteSlice p S T).card := by
  obtain ⟨hW, hd, hb, hc⟩ := actual_generalized_hyperfocus p hcard hS hnon harc T hT
    (Finset.card_pos.mp (by omega))
  have heven := BMMMatchingParity.white_card_even _ _ hW hd hb hc (by rwa [planeWhite_card])
  rwa [planeWhite_card] at heven

end Cylinder.WhitePlaneCoordinates

end
