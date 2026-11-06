module

public import Cylinder.MinimumEquationAbsoluteFactors
public import Cylinder.GapRelations

/-! Actual exclusive point sets of the components of a minimum equation. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.MinimumEquationComponents

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.RationalMinimumEquation Cylinder.PlaneBinaryReduction
open Cylinder.EquationScalarDescent Cylinder.MinimumEquationReduced
open Cylinder.HilbertEvaluation Cylinder.ReducedGapIdeal

variable {K L : Type*} [Field K] [Field L]

def exclusivePoints (D : Finset (PlanePoint K)) (H : MvPolynomial (Fin 3) K) :
    Finset (PlanePoint K) := D.filter (fun P => eval P.rep H ≠ 0)

theorem exclusivePoints_subset (D : Finset (PlanePoint K)) (H : MvPolynomial (Fin 3) K) :
    exclusivePoints D H ⊆ D := Finset.filter_subset _ _

theorem cofactor_data (_D : Finset (PlanePoint K)) (s : ℕ)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (G : MvPolynomial (Fin 3) K) (hG : Irreducible G) (H : MvPolynomial (Fin 3) K)
    (hGH : F = G * H) :
    H ≠ 0 ∧ G.IsHomogeneous G.totalDegree ∧ H.IsHomogeneous H.totalDegree ∧
      s = G.totalDegree + H.totalDegree ∧ 0 < G.totalDegree := by
  have hH0 : H ≠ 0 := by intro hz; rw [hGH, hz, mul_zero] at hF0; exact hF0 rfl
  have hGdvd : G ∣ F := ⟨H, hGH⟩
  have hHdvd : H ∣ F := by rw [hGH]; exact dvd_mul_left H G
  refine ⟨hH0, HomogeneousFactors.homogeneous_of_dvd G F s hF hF0 hGdvd,
    HomogeneousFactors.homogeneous_of_dvd H F s hF hF0 hHdvd, ?_,
    PlaneCurveFactors.positive_degree_of_irreducible G hG⟩
  rw [← hF.totalDegree hF0, hGH, totalDegree_mul_of_isDomain hG.ne_zero hH0]

theorem factor_zero_on_exclusive (D : Finset (PlanePoint K))
    (F G H : MvPolynomial (Fin 3) K) (hGH : F = G * H)
    (hzero : ∀ P ∈ D, eval P.rep F = 0) :
    ∀ P ∈ exclusivePoints D H, eval P.rep G = 0 := by
  intro P hP
  obtain ⟨hPD, hPH⟩ := Finset.mem_filter.mp hP
  have h := hzero P hPD
  rw [hGH, map_mul] at h
  exact (mul_eq_zero.mp h).resolve_right hPH

theorem replacement_zero_on_original (D : Finset (PlanePoint K))
    (H Q : MvPolynomial (Fin 3) K)
    (hzero : ∀ P ∈ exclusivePoints D H, eval P.rep Q = 0) :
    ∀ P ∈ D, eval P.rep (Q * H) = 0 := by
  intro P hP
  rw [map_mul]
  by_cases hH : eval P.rep H = 0
  · rw [hH, mul_zero]
  · rw [hzero P (Finset.mem_filter.mpr ⟨hP, hH⟩), zero_mul]

theorem exclusive_initialDegree (D : Finset (PlanePoint K)) (s : ℕ)
    (hs : InitialDegree (baseRepresentatives D) s)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ D, eval P.rep F = 0)
    (G : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (H : MvPolynomial (Fin 3) K) (hGH : F = G * H) :
    InitialDegree (baseRepresentatives (exclusivePoints D H)) G.totalDegree := by
  obtain ⟨hH0, hGhom, hHhom, hdeg, _⟩ := cofactor_data D s F hF hF0 G hG H hGH
  refine ⟨(idealPiece_ne_bot_iff _ _).mpr ⟨G, hGhom, hG.ne_zero, ?_⟩, ?_⟩
  · intro P
    exact factor_zero_on_exclusive D F G H hGH hzero P.val P.property
  · intro d hd
    by_contra hbot
    obtain ⟨Q, hQ, hQ0, hQzero⟩ := (idealPiece_ne_bot_iff _ d).mp hbot
    have hzero' : ∀ P ∈ exclusivePoints D H, eval P.rep Q = 0 :=
      fun P hP => hQzero ⟨P, hP⟩
    have hz := equation_zero_of_degree_lt_initial (baseRepresentatives D) s hs (Q * H)
      (d + H.totalDegree) (hQ.mul hHhom) (by omega)
      (fun P => replacement_zero_on_original D H Q hzero' P.val P.property)
    exact mul_ne_zero hQ0 hH0 hz

theorem exclusive_nonempty (D : Finset (PlanePoint K)) (s : ℕ)
    (hs : InitialDegree (baseRepresentatives D) s)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (G : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (H : MvPolynomial (Fin 3) K) (hGH : F = G * H) :
    (exclusivePoints D H).Nonempty := by
  obtain ⟨hH0, _, hHhom, hdeg, hGpos⟩ := cofactor_data D s F hF hF0 G hG H hGH
  by_contra hn
  have hHzero : ∀ P : D, eval (baseRepresentatives D P) H = 0 := by
    intro P
    by_contra hP
    exact hn ⟨P.val, Finset.mem_filter.mpr ⟨P.property, hP⟩⟩
  exact hH0 (equation_zero_of_degree_lt_initial (baseRepresentatives D) s hs H
    H.totalDegree hHhom (by omega) hHzero)

theorem exclusive_initialDegree_after_embedding (f : K →+* L)
    (D : Finset (PlanePoint K)) (s : ℕ) (hs : InitialDegree (representatives f D) s)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ D, eval P.rep F = 0)
    (G : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (H : MvPolynomial (Fin 3) K) (hGH : F = G * H) :
    InitialDegree (representatives f (exclusivePoints D H)) G.totalDegree :=
  (RationalMinimumEquation.initialDegree_iff f _ _).mpr
    (exclusive_initialDegree D s ((RationalMinimumEquation.initialDegree_iff f D s).mp hs)
      F hF hF0 hzero G hG H hGH)

theorem eval_mapped_cofactor (f : K →+* L) (D : Finset (PlanePoint K))
    (H : MvPolynomial (Fin 3) K) (P : D) :
    eval (representatives f D P) (MvPolynomial.map f H) = f (eval P.val.rep H) :=
  (MvPolynomial.map_eval f P.val.rep H).symm

def outsideExclusiveEquiv (f : K →+* L) (D : Finset (PlanePoint K))
    (H : MvPolynomial (Fin 3) K) :
    Outside (representatives f D) (MvPolynomial.map f H) ≃ exclusivePoints D H where
  toFun P := ⟨P.val.val, Finset.mem_filter.mpr ⟨P.val.property, by
    intro hz
    apply P.property
    rw [eval_mapped_cofactor, hz, map_zero]⟩⟩
  invFun P := ⟨⟨P.val, (Finset.mem_filter.mp P.property).1⟩, by
    rw [eval_mapped_cofactor]
    exact fun hz => (Finset.mem_filter.mp P.property).2 ((map_eq_zero_iff f f.injective).mp hz)⟩
  left_inv P := by rfl
  right_inv P := by rfl

theorem relation_on_exclusive (f : K →+* L) (D : Finset (PlanePoint K))
    (c : D → L) (d j : ℕ) (hjd : j ≤ d) (H : MvPolynomial (Fin 3) K)
    (hH : H.IsHomogeneous j)
    (hrel : PowerEvaluationRelation.Relation (representatives f D) c d) :
    PowerEvaluationRelation.Relation (representatives f (exclusivePoints D H))
      (fun P => c ⟨P.val, (Finset.mem_filter.mp P.property).1⟩ * f (eval P.val.rep H)) (d - j) := by
  have h := GapRelations.relation_after_factor (representatives f D) c d j hjd
    (MvPolynomial.map f H) (hH.map f) hrel
  intro Q hQ
  have hsum := h Q hQ
  rw [← Fintype.sum_equiv (outsideExclusiveEquiv f D H)]
  convert hsum using 1
  intro P
  change c P.val * eval (representatives f D P.val) (MvPolynomial.map f H) *
    eval (representatives f D P.val) Q =
    c P.val * f (eval P.val.val.rep H) * eval (representatives f D P.val) Q
  rw [eval_mapped_cofactor]

theorem exclusive_coefficients_ne_zero (f : K →+* L) (D : Finset (PlanePoint K))
    (c : D → L) (hc : ∀ P, c P ≠ 0) (H : MvPolynomial (Fin 3) K) :
    ∀ P : exclusivePoints D H,
      c ⟨P.val, (Finset.mem_filter.mp P.property).1⟩ * f (eval P.val.rep H) ≠ 0 := by
  intro P
  exact mul_ne_zero (hc _) (fun hz => (Finset.mem_filter.mp P.property).2
    ((map_eq_zero_iff f f.injective).mp hz))

end Cylinder.MinimumEquationComponents

end
