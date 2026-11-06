module

public import Cylinder.WeakDirectionDivisibility

/-! Formal moments for the larger factor in the Rédei argument. -/

@[expose] public section
noncomputable section

namespace Cylinder.Redei

open scoped Classical BigOperators
open MvPolynomial Geometry PowerEvaluationRelation WeakDirectionsGeometry

variable (p : ℕ) [Fact p.Prime]

/-- The unweighted, degree-`j` moment of a finite point set. -/
def moment (S : Finset (Point p)) (j : ℕ) : MvPolynomial (Fin 3) (ZMod p) :=
  ∑ x ∈ S, linearForm x ^ j

theorem moment_homogeneous (S : Finset (Point p)) (j : ℕ) :
    (moment p S j).IsHomogeneous j := by
  apply IsHomogeneous.sum
  intro x _
  simpa only [one_mul] using (LinearFormFactors.linearForm_homogeneous x).pow j

theorem eval_moment (S : Finset (Point p)) (j : ℕ) (u : Point p) :
    eval u (moment p S j) = ∑ x ∈ S, pairing p u x ^ j := by
  simp only [moment, map_sum, map_pow, FiniteFieldHyperplaneDivisibility.eval_linearForm,
    pairing, mul_comm]

theorem eval_moment_by_planes (S : Finset (Point p)) (j : ℕ) (u : Point p) :
    eval u (moment p S j) =
      ∑ t : ZMod p, ((S.filter fun x => pairing p u x = t).card : ZMod p) * t ^ j := by
  rw [eval_moment, ← Finset.sum_fiberwise' S (pairing p u) (fun z => z ^ j)]
  simp

/-- The plane indicator expanded in the homogeneous moments, including degree zero. -/
theorem plane_count_eq_moments (S : Finset (Point p)) (u : Point p) (t : ZMod p) :
    ((S.filter fun x => pairing p u x = t).card : ZMod p) =
      S.card - ∑ j ∈ Finset.range p,
        eval u (moment p S j) * (-t) ^ (p - 1 - j) * (Nat.choose (p-1) j : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsum :
      (∑ x ∈ S, (pairing p u x - t)^(p-1)) =
        (S.card : ZMod p) - ((S.filter fun x => pairing p u x = t).card : ZMod p) := by
    simp only [WeakDirectionMoments.indicator_identity, sub_eq_zero, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    simp
  have hbin : p - 1 + 1 = p := by omega
  simp_rw [sub_eq_add_neg, add_pow, hbin] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.sum_mul, ← eval_moment] at hsum
  rw [hsum]
  ring

/-- For a set of size `p²`, divisibility of all plane counts is equivalent to
    vanishing of the ordinary formal moments through degree `p-1`. -/
theorem pDivisible_iff_low_moments {S : Finset (Point p)} (hs : S.card = p^2) :
    PDivisible p S ↔ ∀ j < p, moment p S j = 0 := by
  constructor
  · intro h j hj
    apply FiniteGrid.eq_zero_of_degreeOf_lt_card
    · intro i
      rw [ZMod.card]
      exact (degreeOf_le_totalDegree _ _).trans_lt
        ((moment_homogeneous p S j).totalDegree_le.trans_lt hj)
    · intro u
      by_cases hu : u = 0
      · subst u
        rw [eval_moment]
        by_cases hj0 : j = 0
        · simp [hj0, hs]
        · simp [pairing, zero_pow hj0]
      · rw [eval_moment_by_planes]
        apply Finset.sum_eq_zero
        intro t _
        rw [(ZMod.natCast_eq_zero_iff _ _).mpr (h u hu t), zero_mul]
  · intro h u _ t
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [plane_count_eq_moments, hs]
    simp only [Nat.cast_pow, ZMod.natCast_self, zero_pow (by decide : 2 ≠ 0)]
    rw [zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.mem_range.mp hj), map_zero, zero_mul, zero_mul]

/-- The least nonzero moment of a nondivisible set occurs strictly between 0 and p. -/
theorem first_nonzero_moment {S : Finset (Point p)} (hs : S.card = p ^ 2)
    (hbad : ¬ PDivisible p S) :
    ∃ d, 0 < d ∧ d < p ∧ moment p S d ≠ 0 ∧ ∀ j < d, moment p S j = 0 := by
  have hex : ∃ j, j < p ∧ moment p S j ≠ 0 := by
    by_contra! hall
    exact hbad ((pDivisible_iff_low_moments p hs).mpr hall)
  let d := Nat.find hex
  have hd := Nat.find_spec hex
  have hz : moment p S 0 = 0 := by
    simp [moment, hs]
  refine ⟨d, ?_, hd.1, hd.2, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro hzero
    apply hd.2
    change moment p S d = 0
    rwa [hzero]
  · intro j hj
    by_contra hne
    exact (Nat.find_min hex hj) ⟨hj.trans hd.1, hne⟩

/-- Every missing direction divides each low positive moment polynomial as
    a linear factor. This holds independently of a tiling. -/
theorem direction_dvd_moment {S : Finset (Point p)} (hs : S.card = p ^ 2)
    {D : Direction p} (hm : ¬ Determines p S D) (j : ℕ) (hj0 : 0 < j) (hj : j < p) :
    linearForm D.rep ∣ moment p S j := by
  apply FiniteFieldHyperplaneDivisibility.zmod_linearForm_dvd_of_vanishing p _ D.rep_nonzero
  · exact (moment_homogeneous p S j).totalDegree_le.trans (by omega)
  · intro u hu
    have hperp : pairing p u D.rep = 0 := by
      simpa only [FiniteFieldHyperplaneDivisibility.eval_linearForm, pairing, mul_comm] using hu
    by_cases hz : u = 0
    · subst u
      rw [eval_moment]
      simp [pairing, zero_pow (Nat.ne_of_gt hj0)]
    · rw [eval_moment_by_planes]
      apply Finset.sum_eq_zero
      intro t _
      rw [parallel_plane_intersection_card p hs hm u hz t hperp, ZMod.natCast_self, zero_mul]

theorem missing_count_le_first_nonzero_degree {S : Finset (Point p)} (hs : S.card = p ^ 2)
    (j : ℕ) (hj0 : 0 < j) (hj : j < p) (hne : moment p S j ≠ 0) :
    (nonDeterminedDirections p S).card ≤ j := by
  refine le_trans ?_ (moment_homogeneous p S j).totalDegree_le
  · apply PrimeLinearFactorCount.prime_linear_factor_count_le_totalDegree
      (nonDeterminedDirections p S) (fun D : Direction p => linearForm D.rep) _ hne
    · intro D _
      exact LinearFormFactors.linearForm_prime _ D.rep_nonzero
    · intro D _ E _ hDE
      exact LinearFormFactors.projective_linearForms_not_associated D E hDE
    · intro D hD
      exact direction_dvd_moment p hs (Finset.mem_filter.mp hD).2 j hj0 hj
    · intro D _
      exact LinearFormFactors.linearForm_totalDegree _ D.rep_nonzero

end Cylinder.Redei
end