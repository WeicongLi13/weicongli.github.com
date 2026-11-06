module

public import Cylinder.DirectionCurveProposition
public import Cylinder.TwoRayMoments
public import Cylinder.ActualComponentCharacter

/-! Actual product residues yield every weighted component moment relation;
the two-point rays give the literal recurrence for their pointwise quotients. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ComponentMomentRelations
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.ExactRayMomentsTheorem Cylinder.BlackProjectionVandermonde
open Cylinder.RationalPlanePointModel Cylinder.MinimumEquationComponents
open Cylinder.DirectionCurveBounds Cylinder.EvaluationProjection

variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq (ZMod p) := Classical.decEq _

abbrev rawMoment {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (i : directionSet p S b hb) (q : ℕ) : CurveField p :=
  rayMoment (raySize p S b hb) (rayTimesOverField p hb) (rayResiduesOverField p hb c) i q

def componentIndex {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : MvPolynomial (Fin 3) (ZMod p))
    (P : exclusivePoints (directionSet p S b hb) H) : directionSet p S b hb :=
  ⟨P.val, (Finset.mem_filter.mp P.property).1⟩

def componentWeight {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : MvPolynomial (Fin 3) (ZMod p))
    (P : exclusivePoints (directionSet p S b hb) H) : CurveField p :=
  embedding p (eval P.val.rep H)

def componentMoment {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : MvPolynomial (Fin 3) (ZMod p))
    (c : DualPoint p → ZMod p) (q : ℕ)
    (P : exclusivePoints (directionSet p S b hb) H) : CurveField p :=
  componentWeight p hb H P * rawMoment p hb c (componentIndex p hb H P) (q + 1)

theorem componentWeight_ne_zero {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : MvPolynomial (Fin 3) (ZMod p)) :
    ∀ P : exclusivePoints (directionSet p S b hb) H, componentWeight p hb H P ≠ 0 := by
  intro P hz
  exact (Finset.mem_filter.mp P.property).2
    ((map_eq_zero_iff (embedding p) (embedding p).injective).mp hz)

theorem direction_representatives_eq {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) :
    directionRepresentatives p (K := CurveField p) hb = representatives (embedding p) (directionSet p S b hb) := by
  funext P j
  exact congrArg (fun f : ZMod p →+* CurveField p => f (P.val.rep j))
    (Subsingleton.elim (ProductEvaluationRelation.primeEmbedding p) (embedding p))

theorem component_moment_relation {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (hrel : EvaluationRelation (directionRepresentatives p (K := CurveField p) hb) (raySize p S b hb)
      (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2))
    (s : ℕ) (hsbound : s ≤ (p - 3) / 2)
    (F G H : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hG : Irreducible G) (hGH : F = G * H)
    (q : ℕ) (hq : q ≤ p - 3 - s + G.totalDegree) :
    PowerEvaluationRelation.Relation
      (representatives (embedding p) (exclusivePoints (directionSet p S b hb) H))
      (componentMoment p hb H c q) (p - 3 - s + G.totalDegree - q) := by
  obtain ⟨_hH0, _hGhom, hHhom, hdegree, hepos⟩ :=
    cofactor_data (directionSet p S b hb) s F hF hF0 G hG H hGH
  have hp : 3 ≤ p := by have hp2 := (Fact.out : p.Prime).two_le; omega
  have hqe : q + 1 ≤ p - 2 := by omega
  have hcutdegree : H.totalDegree ≤ p - 2 - (q + 1) := by omega
  have hmom := RayMomentRelations.relation_of_moments _ _ _ _ (p - 2) (q + 1) hqe hrel
  rw [direction_representatives_eq p hb] at hmom
  have hcut := relation_on_exclusive (embedding p) (directionSet p S b hb)
    (fun i => rawMoment p hb c i (q + 1)) (p - 2 - (q + 1)) H.totalDegree
    hcutdegree H hHhom hmom
  have hd : p - 2 - (q + 1) - H.totalDegree = p - 3 - s + G.totalDegree - q := by omega
  rw [hd] at hcut
  convert hcut using 1
  funext P
  exact mul_comm _ _

section TwoPoint
variable {K I : Type*} [Field K]

theorem rayMoment_fin_two (r : I → ℕ) (t c : ∀ i, Fin (r i) → K) (i : I) (hr : r i = 2) (q : ℕ) :
    rayMoment r t c i q = TwoRayMoments.twoMoment
      (fun ν : Fin 2 => t i ((Equiv.cast (congrArg Fin hr)).symm ν))
      (fun ν : Fin 2 => c i ((Equiv.cast (congrArg Fin hr)).symm ν)) q := by
  unfold rayMoment TwoRayMoments.twoMoment
  rw [← Fintype.sum_equiv (Equiv.cast (congrArg Fin hr))]
  intro ν
  simp only [Equiv.symm_apply_apply]

theorem two_point_ray_recurrence (r : I → ℕ) (t c : ∀ i, Fin (r i) → K)
    (i : I) (hr : r i = 2) (ht : Function.Injective (t i)) (hc : ∀ ν, c i ν ≠ 0)
    (hzero : rayMoment r t c i 0 = 0) (q : ℕ) :
    rayMoment r t c i (q + 3) / rayMoment r t c i 1 =
      (rayMoment r t c i 2 / rayMoment r t c i 1) *
        (rayMoment r t c i (q + 2) / rayMoment r t c i 1) -
      ((rayMoment r t c i 2 / rayMoment r t c i 1) ^ 2 -
        rayMoment r t c i 3 / rayMoment r t c i 1) *
        (rayMoment r t c i (q + 1) / rayMoment r t c i 1) := by
  let e := Equiv.cast (congrArg Fin hr)
  let t' := fun ν : Fin 2 => t i (e.symm ν)
  let c' := fun ν : Fin 2 => c i (e.symm ν)
  have ht' : Function.Injective t' := ht.comp e.symm.injective
  have hc' : c' 0 ≠ 0 := hc (e.symm 0)
  have hz' : TwoRayMoments.twoMoment t' c' 0 = 0 := by
    simpa only [rayMoment_fin_two r t c i hr] using hzero
  have hn1 := TwoRayMoments.normalized_one t' c' ht' hc' hz'
  have hn2 := TwoRayMoments.normalized_two t' c' ht' hc' hz'
  have hquadratic : TwoRayMoments.normalizedMoment t' c' 1 ^ 2 -
      TwoRayMoments.normalizedMoment t' c' 2 = t' 0 * t' 1 := by rw [hn1, hn2]; ring
  have hrec := TwoRayMoments.normalized_step t' c' ht' hc' hz' q
  rw [← hn1, ← hquadratic] at hrec
  simpa only [TwoRayMoments.normalizedMoment, rayMoment_fin_two r t c i hr,
    Nat.add_assoc, Nat.reduceAdd] using hrec

end TwoPoint

theorem component_two_ray_recurrence {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : MvPolynomial (Fin 3) (ZMod p))
    (c : DualPoint p → ZMod p)
    (hc : ∀ i ν, rayResiduesOverField p (K := CurveField p) hb c i ν ≠ 0)
    (hzero : ∀ i, rawMoment p hb c i 0 = 0)
    (P : exclusivePoints (directionSet p S b hb) H)
    (hr : raySize p S b hb (componentIndex p hb H P) = 2) (q : ℕ) :
    componentMoment p hb H c (q + 2) P / componentMoment p hb H c 0 P =
      (componentMoment p hb H c 1 P / componentMoment p hb H c 0 P) *
        (componentMoment p hb H c (q + 1) P / componentMoment p hb H c 0 P) -
      ((componentMoment p hb H c 1 P / componentMoment p hb H c 0 P) ^ 2 -
        componentMoment p hb H c 2 P / componentMoment p hb H c 0 P) *
        (componentMoment p hb H c q P / componentMoment p hb H c 0 P) := by
  have ha := componentWeight_ne_zero p hb H P
  have hratio (n : ℕ) : componentMoment p hb H c n P / componentMoment p hb H c 0 P =
      rawMoment p hb c (componentIndex p hb H P) (n + 1) /
        rawMoment p hb c (componentIndex p hb H P) 1 := by
    exact mul_div_mul_left _ _ ha
  simp only [hratio]
  exact two_point_ray_recurrence (raySize p S b hb) (rayTimesOverField p hb)
    (rayResiduesOverField p hb c) (componentIndex p hb H P) hr
    (rayTimesOverField_injective p hb _) (hc _) (hzero _) q

#print axioms componentWeight_ne_zero
#print axioms component_moment_relation
#print axioms two_point_ray_recurrence
#print axioms component_two_ray_recurrence

end Cylinder.ComponentMomentRelations
end
