module

public import Cylinder.AffineEvaluationDuality

/-! Unfiltered finite evaluation duality and the high complementary
filtration used for negative relation degrees. -/

@[expose] public section
noncomputable section

namespace Cylinder.FullEvaluationDuality

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionFiltered Cylinder.AffinePointEvaluation
open Cylinder.FiniteEvaluationDuality Cylinder.AffineFilteredAlgebra
open Cylinder.AffineResidueFunctional Cylinder.AffineFrobenius Cylinder.FrobeniusAnnihilator
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

def pointQuotientEquiv (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) f = 0) (hgv : ∀ i, eval (v i) g = 0) :
    (QuotientRing f g ⧸ pointIdeal f g v hfv hgv) ≃ₗ[K] (I → K) := by
  have iso := LinearMap.quotKerEquivOfSurjective (R := K) (evaluation f g v hfv hgv).toLinearMap
    (evaluation_surjective f g v hv hfv hgv)
  exact iso

def fullEvaluationDuality (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) f = 0) (hgv : ∀ i, eval (v i) g = 0) :
    (pointIdeal f g v hfv hgv).annihilator.restrictScalars K ≃ₗ[K] (I → K) :=
  (annihilatorEquivDualQuotient (residueFunctional f g e t he ht hf hg hfe hge hcop)
    (residuePairing_isPerfPair f g e t he ht hf hg hfe hge hcop) (pointIdeal f g v hfv hgv)).trans
      ((pointQuotientEquiv f g v hv hfv hgv).dualMap.symm.trans coefficientsEquivDual.symm)

theorem full_duality_formula (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) f = 0) (hgv : ∀ i, eval (v i) g = 0)
    (a : (pointIdeal f g v hfv hgv).annihilator.restrictScalars K) (b : QuotientRing f g) :
    residueFunctional f g e t he ht hf hg hfe hge hcop (a.val * b) =
      ∑ i, fullEvaluationDuality f g e t he ht hf hg hfe hge hcop v hv hfv hgv a i *
        evaluation f g v hfv hgv b i := by
  let c := fullEvaluationDuality f g e t he ht hf hg hfe hge hcop v hv hfv hgv a
  have hc := coefficientsEquivDual.apply_symm_apply
    ((pointQuotientEquiv f g v hv hfv hgv).dualMap.symm
      (annihilatorEquivDualQuotient (residueFunctional f g e t he ht hf hg hfe hge hcop)
        (residuePairing_isPerfPair f g e t he ht hf hg hfe hge hcop) (pointIdeal f g v hfv hgv) a))
  have hcomp := (pointQuotientEquiv f g v hv hfv hgv).dualMap.apply_symm_apply
    (annihilatorEquivDualQuotient (residueFunctional f g e t he ht hf hg hfe hge hcop)
      (residuePairing_isPerfPair f g e t he ht hf hg hfe hge hcop) (pointIdeal f g v hfv hgv) a)
  rw [← hc] at hcomp
  have hb := congrArg (fun L : Dual K (QuotientRing f g ⧸ pointIdeal f g v hfv hgv) =>
    L (Ideal.Quotient.mk (pointIdeal f g v hfv hgv) b)) hcomp
  exact hb.symm

theorem filteredPiece_eq_top (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (n : ℕ) (hn : e + t - 2 ≤ n) : filteredPiece f g n = ⊤ := by
  apply eq_top_iff.mpr
  intro a _
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, hQ, hQP⟩ := exists_low_degree_representative f g e t he ht hf hg hfe hge hcop P
  exact (mem_filteredPiece f g n _).mpr ⟨Q, hQ.trans hn, hQP⟩

def highFilteredAnnihilatorEquiv (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (v : I → Fin 2 → K)
    (hfv : ∀ i, eval (v i) f = 0) (hgv : ∀ i, eval (v i) g = 0)
    (n : ℕ) (hn : e + t - 2 ≤ n) :
    ↥((pointIdeal f g v hfv hgv).annihilator.restrictScalars K ⊓ filteredPiece f g n) ≃ₗ[K]
      (pointIdeal f g v hfv hgv).annihilator.restrictScalars K :=
  LinearEquiv.ofEq _ _ (by rw [filteredPiece_eq_top f g e t he ht hf hg hfe hge hcop n hn, inf_top_eq])

#print axioms fullEvaluationDuality
#print axioms full_duality_formula
#print axioms filteredPiece_eq_top

end Cylinder.FullEvaluationDuality

end
