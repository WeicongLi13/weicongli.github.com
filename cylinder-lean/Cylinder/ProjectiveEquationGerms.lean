module

public import Cylinder.ProjectiveBezoutStalks

/-! Compatibility of the actual homogeneous-fraction section on D(Z)
with the polynomial local equation in the same projective stalk. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.ProjectiveEquationGerms

open MvPolynomial AlgebraicGeometry CategoryTheory
open Cylinder.ProjectivePolynomialChart Cylinder.ProjectiveAffineOpen
open Cylinder.ProjectivePointInProj Cylinder.ProjectiveRayStalk
open Cylinder.ProjectiveBezoutStalks Cylinder.AffineAmbientStalkQuotient
open Cylinder.CurvePolarLocal Cylinder.HilbertEvaluation

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

theorem affineOpenIso_appTop :
    CommRingCat.ofHom (chartEquiv K).toRingHom ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).inv ≫
      (affineOpenIso K).hom.appTop =
      Proj.awayToSection (grading K) (X none) ≫ (standardOpen K).topIso.inv := by
  change CommRingCat.ofHom (chartEquiv K).toRingHom ≫
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).inv ≫
    (Spec.map (CommRingCat.ofHom (chartEquiv K).symm.toRingHom)).appTop ≫
    (Proj.basicOpenToSpec (grading K) (X none)).appTop = _
  have hb : (Proj.basicOpenToSpec (grading K) (X none)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing K))).hom ≫
        Proj.awayToSection (grading K) (X none) ≫ (standardOpen K).topIso.inv :=
    Proj.basicOpenToSpec_app_top (grading K) (X none)
  rw [hb]
  simp only [Scheme.ΓSpecIso_naturality_assoc]
  have hi : CommRingCat.ofHom (chartEquiv K).toRingHom ≫
      CommRingCat.ofHom (chartEquiv K).symm.toRingHom = 𝟙 (CommRingCat.of (ChartRing K)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro q
    exact (chartEquiv K).symm_apply_apply q
  simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id, hi, Category.id_comp]

theorem embedding_preimage_standardOpen :
    (affineEmbedding K) ⁻¹ᵁ standardOpen K = ⊤ := by
  simp [affineEmbedding]

theorem embedding_appLE_standardOpen :
    (affineEmbedding K).appLE (standardOpen K) ⊤
      (embedding_preimage_standardOpen K).ge =
      (standardOpen K).topIso.inv ≫ (affineOpenIso K).inv.appTop := by
  have hi : (standardOpen K).ι.appLE (standardOpen K) ⊤ (by simp) =
      (standardOpen K).topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  have he : (affineOpenIso K).inv.appLE ⊤ ⊤ (by simp) = (affineOpenIso K).inv.appTop := by
    simp [Scheme.Hom.appLE]
  calc
    _ = (standardOpen K).ι.appLE (standardOpen K) ⊤ (by simp) ≫
        (affineOpenIso K).inv.appLE ⊤ ⊤ (by simp) :=
      (Scheme.Hom.appLE_comp_appLE (affineOpenIso K).inv (standardOpen K).ι
        (standardOpen K) ⊤ ⊤ (by simp) (by simp)).symm
    _ = _ := by rw [hi, he]

theorem section_pullback :
    Proj.awayToSection (grading K) (X none) ≫
      (affineEmbedding K).appLE (standardOpen K) ⊤
        (embedding_preimage_standardOpen K).ge =
      CommRingCat.ofHom (chartEquiv K).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).inv := by
  rw [embedding_appLE_standardOpen, ← Category.assoc, ← affineOpenIso_appTop]
  rw [Category.assoc, Category.assoc, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
  simp

theorem germ_stalkMap_appLE {S T : Scheme} (f : S ⟶ T) (U : T.Opens)
    (V : S.Opens) (hV : V ≤ f ⁻¹ᵁ U) (x : S) (hx : x ∈ V) (s : Γ(T, U)) :
    f.stalkMap x (T.presheaf.germ U (f x) (hV hx) s) =
      S.presheaf.germ V x hx (f.appLE U V hV s) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact (S.presheaf.germ_res_apply (homOfLE hV) x hx (f.app U s)).symm

theorem homogeneous_section_germ (x : Fin 2 → K) (q : ChartRing K) :
    (projectivePlane K).presheaf.germ (standardOpen K) (rayPoint x)
      (rayPoint_mem_standardOpen x) (Proj.awayToSection (grading K) (X none) q) =
      polynomialGerm K x (chartEquiv K q) := by
  apply (canonicalStalkEquiv K x).injective
  rw [polynomialGerm_apply]
  let p : Spec (CommRingCat.of (MvPolynomial (Fin 2) K)) := pointPrime x
  let F := (projectivePlane K).presheaf
  let h := Inseparable.of_eq (affinePoint_eq_rayPoint K x)
  change (affineEmbedding K).stalkMap p
      ((F.stalkCongr h).inv (F.germ (standardOpen K) (rayPoint x)
        (rayPoint_mem_standardOpen x) (Proj.awayToSection (grading K) (X none) q))) = _
  have hc : (F.stalkCongr h).inv
      (F.germ (standardOpen K) (rayPoint x) (rayPoint_mem_standardOpen x)
        (Proj.awayToSection (grading K) (X none) q)) =
      F.germ (standardOpen K) (affinePoint K p)
        ((embedding_preimage_standardOpen K).ge (show p ∈ (⊤ : (Spec
          (CommRingCat.of (MvPolynomial (Fin 2) K))).Opens) from trivial))
        (Proj.awayToSection (grading K) (X none) q) := by
    change F.stalkSpecializes h.le _ = _
    exact congrArg (fun u => u (Proj.awayToSection (grading K) (X none) q))
      (F.germ_stalkSpecializes (rayPoint_mem_standardOpen x) h.le)
  rw [hc]
  change (affineEmbedding K).stalkMap p
    ((projectivePlane K).presheaf.germ (standardOpen K) ((affineEmbedding K) p)
      ((embedding_preimage_standardOpen K).ge trivial)
      (Proj.awayToSection (grading K) (X none) q)) = _
  rw [germ_stalkMap_appLE (affineEmbedding K) (standardOpen K) ⊤
    (embedding_preimage_standardOpen K).ge p trivial]
  have hs := congrArg (fun u => u q) (section_pullback K)
  change (affineEmbedding K).appLE (standardOpen K) ⊤
    (embedding_preimage_standardOpen K).ge
      (Proj.awayToSection (grading K) (X none) q) =
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).inv (chartEquiv K q) at hs
  change (Spec (CommRingCat.of (MvPolynomial (Fin 2) K))).presheaf.germ ⊤ (pointPrime x)
    (show pointPrime x ∈ (⊤ : (Spec (CommRingCat.of (MvPolynomial (Fin 2) K))).Opens) from trivial)
    ((affineEmbedding K).appLE (standardOpen K) ⊤ (embedding_preimage_standardOpen K).ge
      (Proj.awayToSection (grading K) (X none) q)) = _
  rw [hs]
  rfl

theorem homogeneous_fraction_germ (x : Fin 2 → K) (n : ℕ)
    (H : HomogeneousPlanePolynomial (K := K)) (hH : H ∈ grading K (n • (1 : ℕ))) :
    (projectivePlane K).presheaf.germ (standardOpen K) (rayPoint x)
      (rayPoint_mem_standardOpen x)
      (Proj.awayToSection (grading K) (X none)
        (HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n H hH)) =
      equationGerm K x H := by
  rw [homogeneous_section_germ, chartEquiv_mk]
  rfl

theorem homogeneous_equations_germ_ideal (x : Fin 2 → K) (n m : ℕ)
    (H J : HomogeneousPlanePolynomial (K := K))
    (hH : H ∈ grading K (n • (1 : ℕ))) (hJ : J ∈ grading K (m • (1 : ℕ))) :
    germIdeal K (dehomogenize H) (dehomogenize J) x =
      Ideal.span ({
        (projectivePlane K).presheaf.germ (standardOpen K) (rayPoint x)
          (rayPoint_mem_standardOpen x)
          (Proj.awayToSection (grading K) (X none)
            (HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n H hH)),
        (projectivePlane K).presheaf.germ (standardOpen K) (rayPoint x)
          (rayPoint_mem_standardOpen x)
          (Proj.awayToSection (grading K) (X none)
            (HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) m J hJ))} :
        Set (ProjectiveStalk K x)) := by
  rw [homogeneous_fraction_germ, homogeneous_fraction_germ]
  rfl

end Cylinder.ProjectiveEquationGerms
end
