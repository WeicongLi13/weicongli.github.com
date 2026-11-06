module

public import Cylinder.GeneralPlanePlateau

/-!
# The saturated plane plateau theorem

This is the actual-ideal form of Lemma `lem:plateau`. Saturation, initial
degree, and both Hilbert first differences are hypotheses on genuine ring
objects. The common form is constructed from an actual finite-basis gcd.
-/

@[expose] public section
noncomputable section
namespace Cylinder.PlanePlateauTheorem
open MvPolynomial Module
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.PrimitivePlaneSystem Cylinder.GcdPlaneLine Cylinder.SaturatedPlaneLine
open Cylinder.PlaneIdealRestriction Cylinder.GeneralPlanePlateau
open Cylinder.NumericCharacterSequence
variable {K : Type*} [Field K] [Infinite K]

set_option backward.isDefEq.respectTransparency false in
/-- Equal positive consecutive Hilbert first differences yield an actual common
curve component for every lower-degree homogeneous ideal equation. -/
theorem plane_plateau (J : Ideal (PlaneRing K)) (hJ : Saturated J) (z q c : ℕ)
    (hz : Cylinder.PlanePlateau.InitialDegree J z) (hq : z - 1 ≤ q) (hc : 0 < c)
    (h0 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) q = c)
    (h1 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) (q + 1) = c) :
    ∃ G : PlaneRing K, G ≠ 0 ∧ G.IsHomogeneous c ∧ G.totalDegree = c ∧
      ∀ (d : ℕ) (P : PlaneRing K), P.IsHomogeneous d → P ∈ J → d ≤ q + 1 → G ∣ P := by
  by_cases hbase : q + 1 = z
  · obtain ⟨G, hG0, hG, hdeg, _, hlow⟩ := Cylinder.PlanePlateau.plane_plateau_initial J q c
      (by simpa only [hbase] using hz) h0 h1
    exact ⟨G, hG0, hG, hdeg, hlow⟩
  have hzq : z ≤ q := by omega
  have hqpos : 0 < q := by
    by_contra hn
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hn
    subst q
    have hU0 := piece_nonzero_of_initial_le J z 0 hz hzq
    have hpos : 0 < finrank K (Cylinder.PlanePlateau.piece J 0) := by
      by_contra h
      exact hU0 (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos h))
    have hdim := Cylinder.PlanePlateau.quotient_dimension J 0
    rw [forms_finrank_zero] at hdim
    change Cylinder.PlanePlateau.quotientHilbert J 0 = c at h0
    omega
  let degrees : Fin 2 → ℕ := ![q, q + 1]
  let indices (s : Fin 2) := Fin (finrank K (Cylinder.PlanePlateau.piece J (degrees s)))
  let : ∀ s, Fintype (indices s) := fun s => inferInstance
  let f (s : Fin 2) : indices s → PlaneRing K := basisFamily J (degrees s)
  have hdegrees (s : Fin 2) : z ≤ degrees s := by
    fin_cases s
    · exact hzq
    · change z ≤ q + 1
      omega
  have hnonzero (s : Fin 2) : ∃ i, f s i ≠ 0 :=
    basisFamily_nonzero J (degrees s) (piece_nonzero_of_initial_le J z (degrees s) hz (hdegrees s))
  obtain ⟨a, b, hregular, hpres⟩ := exists_graph_regular_preserving_gcds J hJ indices f degrees
    (fun s i => basisFamily_homogeneous J (degrees s) i) hnonzero
  have hGq0 : graphRestriction a b (familyGcd (basisFamily J q)) ≠ 0 := by
    simpa only [f, indices, degrees, Matrix.cons_val_zero] using (hpres 0).1
  have hpresq : ∀ D : BinaryRing K,
      (∀ i, D ∣ graphRestriction a b (basisFamily J q i)) ↔
        D ∣ graphRestriction a b (familyGcd (basisFamily J q)) := by
    simpa only [f, indices, degrees, Matrix.cons_val_zero] using (hpres 0).2.2
  have hU0 := restriction_nonzero_of_preserved_gcd J a b q hGq0 hpresq
  obtain ⟨B, hB0, hB, hBdeg, hfac⟩ := restricted_plateau_factor J a b q c hqpos hregular hU0 h0 h1
  let G := familyGcd (basisFamily J (q + 1))
  have hRG0 : graphRestriction a b G ≠ 0 := by
    simpa only [G, f, indices, degrees, Matrix.cons_val_one, Matrix.cons_val_zero] using (hpres 1).1
  have hRGdegree : (graphRestriction a b G).totalDegree = G.totalDegree := by
    simpa only [G, f, indices, degrees, Matrix.cons_val_one, Matrix.cons_val_zero] using (hpres 1).2.1
  have hprest : ∀ D : BinaryRing K,
      (∀ i, D ∣ graphRestriction a b (basisFamily J (q + 1) i)) ↔ D ∣ graphRestriction a b G := by
    simpa only [G, f, indices, degrees, Matrix.cons_val_one, Matrix.cons_val_zero] using (hpres 1).2.2
  have hBdiv : B ∣ graphRestriction a b G := by
    apply (hprest B).mp
    intro i
    have hm := basis_restriction_mem J a b (q + 1) i
    rw [hfac] at hm
    exact Cylinder.BinaryPlateau.dvd_of_mem_factorSpace B (q + 1 - c) hm
  have hGcommon : ∀ P ∈ restrictionSpace J a b (q + 1), graphRestriction a b G ∣ P := by
    apply (restriction_divisor_iff J a b (q + 1) _).mpr
    intro i
    exact map_dvd (graphRestriction a b).toRingHom (familyGcd_dvd (basisFamily J (q + 1)) i)
  have hGdiv : graphRestriction a b G ∣ B := by
    apply divisor_of_factorSpace B _ hB0 (q + 1 - c)
    intro P hP
    apply hGcommon P
    rw [hfac]
    exact hP
  have hGc : G.totalDegree = c := by
    have hle0 := totalDegree_le_of_dvd_of_isDomain hGdiv hB0
    have hle1 := totalDegree_le_of_dvd_of_isDomain hBdiv hRG0
    omega
  have htop : Cylinder.PlanePlateau.piece J (q + 1) ≠ ⊥ :=
    piece_nonzero_of_initial_le J z (q + 1) hz (by omega)
  have hGn0 := basisFamily_nonzero J (q + 1) htop
  have hG0 : G ≠ 0 := familyGcd_ne_zero (basisFamily J (q + 1)) hGn0
  have hGhom : G.IsHomogeneous c := by
    have hh := familyGcd_homogeneous (basisFamily J (q + 1)) (q + 1)
      (basisFamily_homogeneous J (q + 1)) hGn0
    change G.IsHomogeneous G.totalDegree at hh
    rwa [hGc] at hh
  have hGtop : ∀ P ∈ Cylinder.PlanePlateau.piece J (q + 1), G ∣ P := by
    have hle : Cylinder.PlanePlateau.piece J (q + 1) ≤ divisorSubspace G := by
      rw [← basisFamily_span]
      apply Submodule.span_le.mpr
      rintro P ⟨i, rfl⟩
      exact familyGcd_dvd (basisFamily J (q + 1)) i
    exact fun P hP => hle hP
  exact ⟨G, hG0, hGhom, hGc, fun d P hPd hPJ hd =>
    Cylinder.PlanePlateau.divisor_of_all_lower_pieces J q G hG0 hGtop P d hPd hPJ hd⟩

end Cylinder.PlanePlateauTheorem
end
