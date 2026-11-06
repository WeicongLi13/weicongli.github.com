module

public import Cylinder.RationalPlaneLine
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Genuine projective lines through one point have disjoint punctured
point slices. Counting these actual slices bounds a family of secants. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ProjectiveSecantCounting

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct

variable {K : Type*} [Field K]

/-- A projective coefficient vector is an actual projective line. -/
abbrev PlaneLine (K : Type*) [Field K] := Projectivization K (Fin 3 → K)

def Incident (L : PlaneLine K) (P : PlanePoint K) : Prop := dot L.rep P.rep = 0

theorem lines_eq_of_two_incident (L M : PlaneLine K) (P Q : PlanePoint K) (hPQ : P ≠ Q)
    (hLP : Incident L P) (hLQ : Incident L Q) (hMP : Incident M P) (hMQ : Incident M Q) : L = M := by
  have hc := cross_ne_zero P.rep Q.rep P.rep_nonzero (representatives_not_proportional P Q hPQ)
  obtain ⟨a, ha, hLa⟩ := annihilator_proportional L.rep P.rep Q.rep L.rep_nonzero hc hLP hLQ
  obtain ⟨b, _hb, hMb⟩ := annihilator_proportional M.rep P.rep Q.rep M.rep_nonzero hc hMP hMQ
  by_contra hLM
  apply representatives_not_proportional L M hLM (b * a⁻¹)
  calc
    M.rep = b • cross P.rep Q.rep := hMb
    _ = (b * a⁻¹) • (a • cross P.rep Q.rep) := by
      rw [smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    _ = (b * a⁻¹) • L.rep := by rw [hLa]

def lineSlice (B : Finset (PlanePoint K)) (L : PlaneLine K) : Finset (PlanePoint K) :=
  B.filter (Incident L)

def puncturedSlice (B : Finset (PlanePoint K)) (R : PlanePoint K) (L : PlaneLine K) :
    Finset (PlanePoint K) := (lineSlice B L).erase R

theorem puncturedSlice_subset (B : Finset (PlanePoint K)) (R : PlanePoint K) (L : PlaneLine K) :
    puncturedSlice B R L ⊆ B.erase R :=
  Finset.erase_subset_erase R (Finset.filter_subset (Incident L) B)

theorem puncturedSlices_disjoint (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (L M : PlaneLine K) (hLM : L ≠ M) (hLR : Incident L R) (hMR : Incident M R) :
    Disjoint (puncturedSlice B R L) (puncturedSlice B R M) := by
  apply Finset.disjoint_left.mpr
  intro P hPL hPM
  obtain ⟨hPR, hPL⟩ := Finset.mem_erase.mp hPL
  obtain ⟨_hPR, hPM⟩ := Finset.mem_erase.mp hPM
  exact hLM (lines_eq_of_two_incident L M R P hPR.symm hLR
    (Finset.mem_filter.mp hPL).2 hMR (Finset.mem_filter.mp hPM).2)

theorem puncturedSlices_pairwise_disjoint (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (lines : Finset (PlaneLine K)) (hthrough : ∀ L ∈ lines, Incident L R) :
    (lines : Set (PlaneLine K)).PairwiseDisjoint (puncturedSlice B R) := by
  intro L hL M hM hLM
  exact puncturedSlices_disjoint B R L M hLM (hthrough L hL) (hthrough M hM)

theorem sum_punctured_slice_card_le (B : Finset (PlanePoint K)) (R : PlanePoint K) (hR : R ∈ B)
    (lines : Finset (PlaneLine K)) (hthrough : ∀ L ∈ lines, Incident L R) :
    (∑ L ∈ lines, (puncturedSlice B R L).card) ≤ B.card - 1 := by
  have hsub : lines.biUnion (puncturedSlice B R) ⊆ B.erase R := by
    intro P hP
    obtain ⟨L, _hL, hPL⟩ := Finset.mem_biUnion.mp hP
    exact puncturedSlice_subset B R L hPL
  have hle := Finset.card_le_card hsub
  rwa [Finset.card_biUnion (puncturedSlices_pairwise_disjoint B R lines hthrough),
    Finset.card_erase_of_mem hR] at hle

theorem uniform_secants_through_point_bound (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (hR : R ∈ B) (lines : Finset (PlaneLine K)) (k : ℕ)
    (hthrough : ∀ L ∈ lines, Incident L R) (hsize : ∀ L ∈ lines, (lineSlice B L).card = k + 1) :
    k * lines.card ≤ B.card - 1 := by
  have hpunctured : ∀ L ∈ lines, (puncturedSlice B R L).card = k := by
    intro L hL
    have hRL : R ∈ lineSlice B L := Finset.mem_filter.mpr ⟨hR, hthrough L hL⟩
    simp only [puncturedSlice, Finset.card_erase_of_mem hRL, hsize L hL, Nat.add_sub_cancel]
  have hsum : (∑ L ∈ lines, (puncturedSlice B R L).card) = k * lines.card := by
    rw [Finset.sum_congr rfl hpunctured]
    simp [Nat.mul_comm]
  rw [← hsum]
  exact sum_punctured_slice_card_le B R hR lines hthrough

theorem four_secants_through_point_bound (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (hR : R ∈ B) (lines : Finset (PlaneLine K))
    (hthrough : ∀ L ∈ lines, Incident L R) (hsize : ∀ L ∈ lines, (lineSlice B L).card = 4) :
    3 * lines.card ≤ B.card - 1 :=
  uniform_secants_through_point_bound B R hR lines 3 hthrough hsize

end Cylinder.ProjectiveSecantCounting

end
