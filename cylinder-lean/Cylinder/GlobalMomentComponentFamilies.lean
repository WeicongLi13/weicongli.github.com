module

public import Cylinder.GlobalMomentResidues

/-! Actual cofactor interpolation supplies forms indexed by all the real
factors. Its point identities hold on the literal exclusive components. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentComponentFamilies

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.PlaneCurveFactors Cylinder.MinimumEquationComponentSets Cylinder.MinimumEquationComponents

variable {K L : Type*} [Field K] [Field L]

def componentIndex (D : Finset (PlanePoint K)) (H : MvPolynomial (Fin 3) K)
    (P : exclusivePoints D H) : D := ⟨P.val, (Finset.mem_filter.mp P.property).1⟩

theorem assemble_component_form_families (f : K →+* L) (D : Finset (PlanePoint K))
    (F : MvPolynomial (Fin 3) K) (hF0 : F ≠ 0) (hsq : Squarefree F)
    (hzero : ∀ P ∈ D, eval P.rep F = 0) (u m₂ m₃ : D → L)
    (hforms : ∀ G ∈ factors F, ∀ H : MvPolynomial (Fin 3) K, F = G * H →
      ∃ q r : MvPolynomial (Fin 3) L, q.IsHomogeneous 1 ∧ r.IsHomogeneous 2 ∧
        (∀ P : exclusivePoints D H, m₂ (componentIndex D H P) =
          eval (representatives f (exclusivePoints D H) P) q * u (componentIndex D H P)) ∧
        ∀ P : exclusivePoints D H, m₃ (componentIndex D H P) =
          eval (representatives f (exclusivePoints D H) P) r * u (componentIndex D H P)) :
    ∃ fi gi : factors F → MvPolynomial (Fin 3) L,
      (∀ G, (fi G).IsHomogeneous 1) ∧ (∀ G, (gi G).IsHomogeneous 2) ∧
      (∀ G : factors F, ∀ P : D, P.val ∈ componentPoints D F G.val →
        m₂ P = eval (representatives f D P) (fi G) * u P) ∧
      ∀ G : factors F, ∀ P : D, P.val ∈ componentPoints D F G.val →
        m₃ P = eval (representatives f D P) (gi G) * u P := by
  have hchoice : ∀ G : factors F, ∃ q r : MvPolynomial (Fin 3) L,
      q.IsHomogeneous 1 ∧ r.IsHomogeneous 2 ∧
      (∀ P : D, P.val ∈ componentPoints D F G.val → m₂ P = eval (representatives f D P) q * u P) ∧
      ∀ P : D, P.val ∈ componentPoints D F G.val → m₃ P = eval (representatives f D P) r * u P := by
    intro G
    obtain ⟨H, hGH⟩ := factor_dvd F G.val G.property
    obtain ⟨q, r, hq, hr, hqid, hrid⟩ := hforms G.val G.property H hGH
    have hE := exclusivePoints_eq_componentPoints D F G.val H hF0 hsq G.property hGH hzero
    refine ⟨q, r, hq, hr, ?_, ?_⟩
    · intro P hP
      have hPE : P.val ∈ exclusivePoints D H := by rwa [hE]
      let P' : exclusivePoints D H := ⟨P.val, hPE⟩
      have hidx : componentIndex D H P' = P := Subtype.ext rfl
      have hreps : representatives f (exclusivePoints D H) P' = representatives f D P := rfl
      simpa only [hidx, hreps] using hqid P'
    · intro P hP
      have hPE : P.val ∈ exclusivePoints D H := by rwa [hE]
      let P' : exclusivePoints D H := ⟨P.val, hPE⟩
      have hidx : componentIndex D H P' = P := Subtype.ext rfl
      have hreps : representatives f (exclusivePoints D H) P' = representatives f D P := rfl
      simpa only [hidx, hreps] using hrid P'
  choose fi gi hfi hgi hidf hidg using hchoice
  exact ⟨fi, gi, hfi, hgi, hidf, hidg⟩

end Cylinder.GlobalMomentComponentFamilies

end
