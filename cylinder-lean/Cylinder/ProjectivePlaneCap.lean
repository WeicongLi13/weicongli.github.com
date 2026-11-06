module

public import Cylinder.DualLineBalance
public import Cylinder.ProjectiveCoplanarity
public import Cylinder.EmptyLineBound
public import Cylinder.AffinePlanes
public import Cylinder.DualPlaneModel

/-!
# The white-point bound in actual dual projective planes

The dual plane indexed by a primal point consists of the homogeneous
plane equations vanishing at that point. After recharting at a white
point and aligning the resulting infinity direction with the third
coordinate, its other white points come from actual empty quotient lines.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectivePlaneCap

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveBalance
open Cylinder.ProjectiveChart Cylinder.ProjectiveCylinderChart Cylinder.DualPencils
open Cylinder.CoordinateProjection
open scoped Classical BigOperators LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

def planePoints (v : PG3 p) : Finset (DualPoint p) :=
  Finset.univ.filter (fun H => Incident p v H)

def whiteOnPlane (S : Finset (Geometry.Point p)) (v : PG3 p) : Finset (DualPoint p) :=
  (whitePoints p S).filter (fun H => Incident p v H)

@[simp] theorem mem_whiteOnPlane (S : Finset (Geometry.Point p)) (v : PG3 p) (H : DualPoint p) :
    H ∈ whiteOnPlane p S v ↔ H ∈ whitePoints p S ∧ Incident p v H := by
  simp [whiteOnPlane]

theorem whiteOnPlane_eq_inter (S : Finset (Geometry.Point p)) (v : PG3 p) :
    whiteOnPlane p S v = whitePoints p S ∩ planePoints p v := by
  ext H
  simp [whiteOnPlane, planePoints]

theorem white_mapDual_iff
    (e : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)
    (S : Finset (Geometry.Point p)) (havoid : AvoidsChart p e S) (H : DualPoint p) :
    mapDual p e H ∈ whitePoints p (S.image (chartMap p e)) ↔ H ∈ whitePoints p S := by
  have hc : (intersection p (S.image (chartMap p e)) (mapDual p e H)).card =
      (intersection p S H).card := by
    rw [intersection_card, intersection_card]
    exact planeIntersection_chartImage_card p e S havoid H
  have hw (T : Finset (Geometry.Point p)) (K : DualPoint p) :
      K ∈ whitePoints p T ↔ quotient p T K = 0 := by
    unfold whitePoints WhiteBlackWeights.white
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hw, hw]
  change (intersection p (S.image (chartMap p e)) (mapDual p e H)).card / p = 0 ↔
    (intersection p S H).card / p = 0
  rw [hc]

theorem whiteOnPlane_map
    (e : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)
    (S : Finset (Geometry.Point p)) (havoid : AvoidsChart p e S) (v : PG3 p) :
    (whiteOnPlane p S v).image (mapDual p e) =
      whiteOnPlane p (S.image (chartMap p e)) (mapPoint p e v) := by
  ext H'
  constructor
  · intro hH'
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hH'
    obtain ⟨hw, hi⟩ := (mem_whiteOnPlane p S v H).mp hH
    exact (mem_whiteOnPlane p _ _ _).mpr
      ⟨(white_mapDual_iff p e S havoid H).mpr hw,
        (incident_mapPoint_mapDual p e v H).mpr hi⟩
  · intro hH'
    obtain ⟨H, rfl⟩ := mapDual_surjective p e H'
    obtain ⟨hw, hi⟩ := (mem_whiteOnPlane p _ _ _).mp hH'
    exact Finset.mem_image.mpr ⟨H, (mem_whiteOnPlane p S v H).mpr
      ⟨(white_mapDual_iff p e S havoid H).mp hw,
        (incident_mapPoint_mapDual p e v H).mp hi⟩, rfl⟩

theorem whiteOnPlane_chart_card
    (e : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)
    (S : Finset (Geometry.Point p)) (havoid : AvoidsChart p e S) (v : PG3 p) :
    (whiteOnPlane p (S.image (chartMap p e)) (mapPoint p e v)).card =
      (whiteOnPlane p S v).card := by
  rw [← whiteOnPlane_map p e S havoid v,
    Finset.card_image_of_injective _ (mapDual_injective p e)]

/-- A genuine affine linear coordinate change extended to homogeneous coordinates. -/
def homogeneous (g : Geometry.Point p ≃ₗ[ZMod p] Geometry.Point p) :
    ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p where
  toFun x := Fin.cons (x 0) (g (fun i => x i.succ))
  invFun x := Fin.cons (x 0) (g.symm (fun i => x i.succ))
  left_inv x := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    change g.symm (g (fun i => x i.succ)) j = x j.succ
    rw [g.symm_apply_apply]
  right_inv x := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    change g (g.symm (fun i => x i.succ)) j = x j.succ
    rw [g.apply_symm_apply]
  map_add' x y := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    change g ((fun i => x i.succ) + (fun i => y i.succ)) j =
      g (fun i => x i.succ) j + g (fun i => y i.succ) j
    rw [map_add]
    rfl
  map_smul' t x := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    change g (t • (fun i => x i.succ)) j = t * g (fun i => x i.succ) j
    rw [map_smul]
    rfl

theorem homogeneous_avoids (g : Geometry.Point p ≃ₗ[ZMod p] Geometry.Point p)
    (S : Finset (Geometry.Point p)) : AvoidsChart p (homogeneous p g) S := by
  intro x _hx
  change (1 : ZMod p) ≠ 0
  exact one_ne_zero

@[simp] theorem chartMap_homogeneous (g : Geometry.Point p ≃ₗ[ZMod p] Geometry.Point p)
    (x : Geometry.Point p) : chartMap p (homogeneous p g) x = g x := by
  funext i
  simp [chartMap, homogeneous, affineVector]

@[simp] theorem homogeneous_direction (g : Geometry.Point p ≃ₗ[ZMod p] Geometry.Point p)
    (d : Geometry.Point p) : homogeneous p g (directionVector p d) = directionVector p (g d) := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

def verticalPoint : PG3 p := Projectivization.mk (ZMod p)
  (directionVector p (verticalDirection p))
  (directionVector_ne_zero p (verticalDirection_ne_zero p))

@[simp] theorem affineFunctional_direction (n : Geometry.Point p) (b : ZMod p)
    (d : Geometry.Point p) :
    affinePlaneFunctional p n b (directionVector p d) = Geometry.pairing p n d := by
  simp [affinePlaneFunctional, pairingMap, ProjectiveGeometry.pairing,
    Fin.sum_univ_succ, directionVector, Geometry.pairing]

theorem incident_vertical_affinePlaneDual (n : Geometry.Point p) (hn : n ≠ 0) (b : ZMod p) :
    Incident p (verticalPoint p) (affinePlaneDual p n b hn) ↔ n 2 = 0 := by
  simp [verticalPoint, affinePlaneDual, affineFunctional_direction, Geometry.pairing,
    Fin.sum_univ_three, verticalDirection]

def lineNormal : LineFactors.Line (ZMod p) → Geometry.Point p
  | Sum.inl _ => ![0, 1, 0]
  | Sum.inr (_, β) => ![1, -β, 0]

def lineConstant : LineFactors.Line (ZMod p) → ZMod p
  | Sum.inl c => c
  | Sum.inr (α, _) => α

theorem lineNormal_ne_zero (L : LineFactors.Line (ZMod p)) : lineNormal p L ≠ 0 := by
  intro h
  rcases L with c | ⟨α, β⟩
  · have hh := congrFun h 1
    simp [lineNormal] at hh
  · have hh := congrFun h 0
    simp [lineNormal] at hh

def lineDual (L : LineFactors.Line (ZMod p)) : DualPoint p :=
  affinePlaneDual p (lineNormal p L) (lineConstant p L) (lineNormal_ne_zero p L)

theorem lineDual_incident_iff (L : LineFactors.Line (ZMod p)) (x : Geometry.Point p) :
    Incident p (affineEmbed p x) (lineDual p L) ↔ project p x ∈ LineFactors.linePoints L := by
  rw [lineDual, affineEmbed_incident_affinePlaneDual, EmptyLineBound.mem_linePoints_iff]
  rcases L with c | ⟨α, β⟩
  · simp [lineNormal, lineConstant, Geometry.pairing, Fin.sum_univ_three,
      project, LineFactors.equation, sub_eq_zero]
  · simp only [lineNormal, lineConstant, Geometry.pairing, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      one_mul, zero_mul, add_zero, LineFactors.equation,
      LineDivisibility.graphEquation, map_sub, map_add, map_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C, project, sub_eq_zero]
    rw [neg_mul, ← sub_eq_add_neg, sub_eq_iff_eq_add]

theorem affinePlaneDual_scaled {n m : Geometry.Point p} (hn : n ≠ 0) (hm : m ≠ 0)
    (b c t : ZMod p) (hnorm : n = t • m) (hconstant : b = t * c) :
    affinePlaneDual p n b hn = affinePlaneDual p m c hm := by
  have hvec : Fin.cons (-b) n = t • Fin.cons (-c) m := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hconstant, Pi.smul_apply, smul_eq_mul]
    · exact congrFun hnorm j
  have hfn : t • affinePlaneFunctional p m c = affinePlaneFunctional p n b := by
    apply LinearMap.ext
    intro x
    change t * ProjectiveGeometry.pairing p (Fin.cons (-c) m) x =
      ProjectiveGeometry.pairing p (Fin.cons (-b) n) x
    rw [hvec, ProjectiveGeometry.pairing_smul_left]
  exact (Projectivization.mk_eq_mk_iff' (ZMod p) (affinePlaneFunctional p n b)
    (affinePlaneFunctional p m c) (affinePlaneFunctional_ne_zero p hn b)
    (affinePlaneFunctional_ne_zero p hm c)).mpr ⟨t, hfn⟩

theorem lineDual_of_incident_vertical {H : DualPoint p} (hne : H ≠ infinity p)
    (hincident : Incident p (verticalPoint p) H) :
    ∃ L : LineFactors.Line (ZMod p), H = lineDual p L := by
  obtain ⟨n, b, hn, rfl⟩ := DualLineBalance.affinePlaneDual_of_ne_infinity p hne
  have h2 : n 2 = 0 := (incident_vertical_affinePlaneDual p n hn b).mp hincident
  by_cases h0 : n 0 = 0
  · have h1 : n 1 ≠ 0 := by
      intro hz
      apply hn
      funext i
      fin_cases i <;> simp_all
    let L : LineFactors.Line (ZMod p) := Sum.inl (b / n 1)
    refine ⟨L, affinePlaneDual_scaled p hn (lineNormal_ne_zero p L) b (lineConstant p L) (n 1) ?_ ?_⟩
    · funext i
      fin_cases i <;> simp [L, lineNormal, h0, h2, Pi.smul_apply, smul_eq_mul]
    · exact (AffinePlanes.scale_div_cancel p (n 1) b h1).symm
  · let L : LineFactors.Line (ZMod p) := Sum.inr (b / n 0, -n 1 / n 0)
    refine ⟨L, affinePlaneDual_scaled p hn (lineNormal_ne_zero p L) b (lineConstant p L) (n 0) ?_ ?_⟩
    · funext i
      fin_cases i
      · simp [L, lineNormal, Pi.smul_apply, smul_eq_mul]
      · simpa [L, lineNormal, Pi.smul_apply, smul_eq_mul, neg_div] using
          (AffinePlanes.scale_div_cancel p (n 0) (n 1) h0).symm
      · simp [L, lineNormal, h2, Pi.smul_apply, smul_eq_mul]
    · exact (AffinePlanes.scale_div_cancel p (n 0) b h0).symm

theorem lineDual_white_mem_emptyLines {S : Finset (Geometry.Point p)}
    (hS : Geometry.PDivisible p S) {L : LineFactors.Line (ZMod p)}
    (hwhite : lineDual p L ∈ whitePoints p S) : L ∈ EmptyLineBound.emptyLines p S := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro t
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxS, hxproj⟩ := Finset.mem_filter.mp hx
  have hpoint : project p x ∈ LineFactors.linePoints L := by
    rw [hxproj]
    exact (EmptyLineBound.mem_linePoints_iff p L _).mpr (LineFactors.equation_eval_point L t)
  have hi := (lineDual_incident_iff p L x).mpr hpoint
  exact (ProjectiveCover.mem_whitePoints_iff_no_incident p hS _).mp hwhite
    (affineEmbed p x) ((ProjectiveCover.affineEmbed_mem_pointSet p S x).mpr hxS) hi

theorem vertical_plane_white_subset {S : Finset (Geometry.Point p)} (hS : Geometry.PDivisible p S) :
    whiteOnPlane p S (verticalPoint p) ⊆
      insert (infinity p) ((EmptyLineBound.emptyLines p S).image (lineDual p)) := by
  intro H hH
  obtain ⟨hwhite, hi⟩ := (mem_whiteOnPlane p S _ H).mp hH
  by_cases hinf : H = infinity p
  · rw [hinf]
    exact Finset.mem_insert_self _ _
  · obtain ⟨L, hL⟩ := lineDual_of_incident_vertical p hinf hi
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨L,
      lineDual_white_mem_emptyLines p hS (by rw [← hL]; exact hwhite), hL.symm⟩

theorem vertical_plane_white_card_le {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S) :
    (whiteOnPlane p S (verticalPoint p)).card ≤ p - 1 := by
  have hsub := Finset.card_le_card (vertical_plane_white_subset p hS)
  have hins := Finset.card_insert_le (infinity p)
    ((EmptyLineBound.emptyLines p S).image (lineDual p))
  have himage : ((EmptyLineBound.emptyLines p S).image (lineDual p)).card ≤
      (EmptyLineBound.emptyLines p S).card := Finset.card_image_le
  have hbound := EmptyLineBound.emptyLines_card_le p hcard hS hnon
  have hp := (Fact.out : p.Prime).two_le
  omega

theorem plane_white_card_le_of_incident_infinity {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    (v : PG3 p) (hinfinity : Incident p v (infinity p)) :
    (whiteOnPlane p S v).card ≤ p - 1 := by
  have hzero := (ProjectiveCoplanarity.incident_infinity_rep_iff p v).mp hinfinity
  let d : Geometry.Point p := fun i => v.rep i.succ
  have hd : d ≠ 0 := by
    intro h
    apply v.rep_nonzero
    funext i
    refine Fin.cases hzero (fun j => congrFun h j) i
  have hrep : directionVector p d = v.rep := by
    funext i
    refine Fin.cases hzero.symm (fun _ => rfl) i
  obtain ⟨g, hgv⟩ := LinearTransport.exists_linearEquiv_to_vertical p hd
  have hvmap : mapPoint p (homogeneous p g) v = verticalPoint p := by
    rw [← Projectivization.mk_rep v, mapPoint, Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff' (ZMod p)
      (homogeneous p g v.rep) (directionVector p (verticalDirection p))
      _ (directionVector_ne_zero p (verticalDirection_ne_zero p))).mpr
    refine ⟨1, ?_⟩
    rw [← hrep, homogeneous_direction, hgv, one_smul]
  have hcount := whiteOnPlane_chart_card p (homogeneous p g) S (homogeneous_avoids p g S) v
  have hchart : chartMap p (homogeneous p g) = g := funext (chartMap_homogeneous p g)
  rw [hchart, hvmap] at hcount
  rw [← hcount]
  apply vertical_plane_white_card_le p
  · exact (LinearTransport.image_card p g S).trans hcard
  · exact LinearTransport.pDivisible_image p g hS
  · intro hcy
    exact hnon ((LinearTransport.isCylinder_image_iff p g S).mp hcy)

/-- The projective-plane assertion of Lemma `lem:planecap`. -/
theorem plane_white_card_le {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S) (v : PG3 p) :
    (whitePoints p S ∩ planePoints p v).card ≤ p - 1 := by
  rw [← whiteOnPlane_eq_inter]
  by_cases hwhite : (whiteOnPlane p S v).Nonempty
  · obtain ⟨H0, hH0⟩ := hwhite
    obtain ⟨hw, hi⟩ := (mem_whiteOnPlane p S v H0).mp hH0
    obtain ⟨e, havoid, hinf, hcard', hdiv, hcy, _hplanes⟩ :=
      EmptyPlaneChart.empty_plane_as_infinity p S H0 (DualLineBalance.empty_of_white p hS hw)
    have hi' : Incident p (mapPoint p e v) (infinity p) := by
      rw [← hinf]
      exact (incident_mapPoint_mapDual p e v H0).mpr hi
    have hcount := whiteOnPlane_chart_card p e S havoid v
    rw [← hcount]
    apply plane_white_card_le_of_incident_infinity p
      (hcard'.trans hcard) (hdiv.mpr hS) (fun h => hnon (hcy.mp h)) _ hi'
  · have hempty : whiteOnPlane p S v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hwhite
    simp [hempty]

/-- The same bound for every three-dimensional dual vector subspace. -/
theorem dual_plane_white_card_le {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    (W : Submodule (ZMod p) (Module.Dual (ZMod p) (ProjectiveGeometry.Vector p)))
    (hW : Module.finrank (ZMod p) W = 3) :
    (whitePoints p S ∩ DualPlaneModel.dualPlanePoints p W).card ≤ p - 1 := by
  obtain ⟨v, hv⟩ := DualPlaneModel.points_eq_incident p W hW
  change DualPlaneModel.dualPlanePoints p W = planePoints p v at hv
  rw [hv]
  exact plane_white_card_le p hcard hS hnon v

end Cylinder.ProjectivePlaneCap

end
