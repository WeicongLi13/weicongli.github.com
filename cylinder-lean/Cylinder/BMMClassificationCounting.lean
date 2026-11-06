module

public import Cylinder.BMMThreeSecantAxis
public import Cylinder.ProjectiveSecantCounting

/-! The final real counting argument, conditional on two explicit local
classification and recovery statements. These statements are exposed as
inputs here; this module does not assert the full BMM theorem. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMClassificationCounting
open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMThreeSecantConfigurations Cylinder.BMMThreeSecantAxis
open Cylinder.ProjectiveSecantCounting Cylinder.BMMMatchingParity
open Cylinder.BMMFinitePlaneArcBound Cylinder.BMMNormalizedGeometry

variable {K : Type*} [Field K]

def AxisClassification (N : NormalizedSystem K) : Prop :=
  ∀ (R : N.B) (T : FourTuple (configuration N) N.E R),
    ((lineSlice N.B (firstLine N T)).card = 3 ∧ (lineSlice N.B (secondLine N T)).card = 4) ∨
      ((lineSlice N.B (firstLine N T)).card = 4 ∧ (lineSlice N.B (secondLine N T)).card = 3)

def HasAxes (N : NormalizedSystem K) {R : N.B} (T : FourTuple (configuration N) N.E R)
    (ell m : PlaneLine K) : Prop :=
  (firstLine N T = ell ∧ secondLine N T = m) ∨ (firstLine N T = m ∧ secondLine N T = ell)

def AxisRecovery (N : NormalizedSystem K) : Prop :=
  ∀ (R : N.B) (ell m : PlaneLine K),
    (lineSlice N.B ell).card = 3 → (lineSlice N.B m).card = 4 →
      ∀ (T U : FourTuple (configuration N) N.E R),
        HasAxes N T ell m → HasAxes N U ell m → fourTupleKey N R T = fourTupleKey N R U

theorem incident_mk_iff (l : Fin 3 → K) (hl : l ≠ 0) (P : PlanePoint K) :
    Incident (Projectivization.mk K l hl) P ↔ dot l P.rep = 0 := by
  let L := Projectivization.mk K l hl
  have heq : Projectivization.mk K L.rep L.rep_nonzero = Projectivization.mk K l hl :=
    Projectivization.mk_rep L
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ L.rep_nonzero hl).mp heq
  have ha0 : a ≠ 0 := by
    intro hz
    apply L.rep_nonzero
    rw [hz, zero_smul] at ha
    exact ha.symm
  change dot L.rep P.rep = 0 ↔ _
  rw [← ha, dot_smul_coefficients, mul_eq_zero]
  exact or_iff_right ha0

theorem first_axis_incident_base (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) : Incident (firstLine N T) R.val :=
  (incident_mk_iff _ (first_line_coefficients_nonzero N T) R.val).mpr (dot_cross_left _ _)

theorem second_axis_incident_base (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) : Incident (secondLine N T) R.val :=
  (incident_mk_iff _ (second_line_coefficients_nonzero N T) R.val).mpr (dot_cross_left _ _)

theorem lineSlice_card_eq_lineBlacks (N : NormalizedSystem K) (L : PlaneLine K) :
    (lineSlice N.B L).card = (lineBlacks N L.rep).card := by
  change (N.B.filter (fun P => dot L.rep P.rep = 0)).card = _
  rw [← Cylinder.BMMBlackLinePointSets.pointLineBlacks_eq_filter,
    Cylinder.BMMBlackLinePointSets.pointLineBlacks_card]

theorem exists_three_axis (N : NormalizedSystem K) (hclass : AxisClassification N) (R : N.B)
    (T : FourTuple (configuration N) N.E R) :
    ∃ ell : PlaneLine K, (lineSlice N.B ell).card = 3 ∧ Incident ell R.val ∧
      (ell = firstLine N T ∨ ell = secondLine N T) := by
  rcases hclass R T with hfirst | hsecond
  · exact ⟨firstLine N T, hfirst.1, first_axis_incident_base N T, Or.inl rfl⟩
  · exact ⟨secondLine N T, hsecond.2, second_axis_incident_base N T, Or.inr rfl⟩

theorem exists_other_four_axis (N : NormalizedSystem K) (hclass : AxisClassification N)
    (R : N.B) (T : FourTuple (configuration N) N.E R) (ell : PlaneLine K)
    (hell3 : (lineSlice N.B ell).card = 3) (hell : ell = firstLine N T ∨ ell = secondLine N T) :
    ∃ m : PlaneLine K, Incident m R.val ∧ (lineSlice N.B m).card = 4 ∧ HasAxes N T ell m := by
  rcases hell with hell | hell
  · refine ⟨secondLine N T, second_axis_incident_base N T, ?_, Or.inl ⟨hell.symm, rfl⟩⟩
    rcases hclass R T with hfirst | hsecond
    · exact hfirst.2
    · rw [hell, hsecond.1] at hell3
      omega
  · refine ⟨firstLine N T, first_axis_incident_base N T, ?_, Or.inr ⟨rfl, hell.symm⟩⟩
    rcases hclass R T with hfirst | hsecond
    · rw [hell, hfirst.2] at hell3
      omega
    · exact hsecond.1

set_option maxHeartbeats 1000000 in
theorem white_card_le_four_of_local_structure (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (N : NormalizedSystem (ZMod p)) (hclass : AxisClassification N) (hrecover : AxisRecovery N) :
    N.W.card ≤ 4 := by
  let : DecidableEq (ZMod p) := Classical.decEq _
  by_contra hlarge
  have hlarge : 4 < N.W.card := by omega
  have hp3 : 3 ≤ p := by omega
  have htwo := prime_two_nonzero p hp3
  have hnon : N.B.Nonempty := Finset.card_pos.mp (by have hc := N.card; omega)
  let R : N.B := ⟨hnon.choose, hnon.choose_spec⟩
  obtain ⟨T₀⟩ := exists_actual_nonspecial_fourtuple (configuration N) N.E N.representatives htwo hlarge R
  obtain ⟨ell, hell3, hellR, _hellaxes⟩ := exists_three_axis N hclass R T₀
  have hm : (lineBlacks N ell.rep).card = 3 := by rw [← lineSlice_card_eq_lineBlacks]; exact hell3
  have hR : R ∈ lineBlacks N ell.rep := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hellR⟩
  obtain ⟨n, _hnpos, hn⟩ := white_card_twice N.W N.B N.arc N.disjoint N.blocks N.card (by omega)
  obtain ⟨T, _hkeys, hinj, hindex, haxes⟩ :=
    exists_indexed_axis_configurations p hp3 N ell.rep ell.rep_nonzero hm R hR n hn
  have haxes' : ∀ P, ell = firstLine N (T P) ∨ ell = secondLine N (T P) := by
    intro P
    simpa only [Projectivization.mk_rep] using haxes P
  choose m hmthrough hmfour hmaxes using
    (fun P => exists_other_four_axis N hclass R (T P) ell hell3 (haxes' P))
  have hminj : Function.Injective m := by
    intro P Q heq
    apply hinj
    change fourTupleKey N R (T P) = fourTupleKey N R (T Q)
    exact hrecover R ell (m P) hell3 (hmfour P) (T P) (T Q) (hmaxes P)
      (by rw [heq]; exact hmaxes Q)
  let lines : Finset (PlaneLine (ZMod p)) := Finset.univ.image m
  have hthrough : ∀ L ∈ lines, Incident L R.val := by
    intro L hL
    obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp hL
    exact hmthrough P
  have hfour : ∀ L ∈ lines, (lineSlice N.B L).card = 4 := by
    intro L hL
    obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp hL
    exact hmfour P
  have hcount := four_secants_through_point_bound N.B R.val R.property lines hthrough hfour
  have hlines : lines.card = n := by
    change (Finset.univ.image m).card = n
    rw [Finset.card_image_of_injective _ hminj, Finset.card_univ, hindex]
  rw [hlines] at hcount
  have hc := N.card
  omega

theorem white_card_two_or_four_of_local_structure (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (N : NormalizedSystem (ZMod p)) (hclass : AxisClassification N) (hrecover : AxisRecovery N)
    (hmin : 2 ≤ N.W.card) : N.W.card = 2 ∨ N.W.card = 4 := by
  have hle := white_card_le_four_of_local_structure p hp N hclass hrecover
  obtain ⟨n, hn⟩ := white_card_even N.W N.B N.arc N.disjoint N.blocks N.card hmin
  omega

theorem configuration_card_two_or_four_of_local_structure (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (A : Cylinder.BMMActualCoefficients.Configuration (ZMod p)) (anchor : A.W)
    (hclass : AxisClassification (normalizedSystem A anchor))
    (hrecover : AxisRecovery (normalizedSystem A anchor)) (hmin : 2 ≤ A.W.card) :
    A.W.card = 2 ∨ A.W.card = 4 :=
  white_card_two_or_four_of_local_structure p hp (normalizedSystem A anchor) hclass hrecover hmin

end Cylinder.BMMClassificationCounting
end
