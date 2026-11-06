module

public import Cylinder.PrincipalCechOneFractionField
public import Cylinder.SheafCechOneDescent
public import Mathlib.AlgebraicGeometry.StructureSheaf

/-! Actual principal-cover Čech exactness for the structure sheaf of Spec R.
The section/localization isomorphisms are constructed by the real
`IsLocalization.Away` instances for basic opens; they are not hypotheses. -/

@[expose] public section
noncomputable section

universe u

namespace Cylinder.ActualAffineCechOne

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.PrincipalCechOneFractionField Cylinder.SheafCechOneDescent

variable {R K : Type u} [CommRing R] [Field K]

abbrev basicSections (R : Type u) [CommRing R] (f : R) :=
  (Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f))

def basicSectionEquiv (f : R) : Localization.Away f ≃ₐ[R] basicSections R f :=
  IsLocalization.algEquiv (.powers f) _ _

def sectionRestriction {U V : Opens (PrimeSpectrum.Top R)} (h : V ≤ U) :
    (Spec.structureSheaf R).obj.obj (op U) →+* (Spec.structureSheaf R).obj.obj (op V) :=
  ((Spec.structureSheaf R).obj.map (homOfLE h).op).hom

@[simp] theorem sectionRestriction_algebraMap {U V : Opens (PrimeSpectrum.Top R)}
    (h : V ≤ U) (a : R) :
    sectionRestriction h (algebraMap R ((Spec.structureSheaf R).obj.obj (op U)) a) =
      algebraMap R ((Spec.structureSheaf R).obj.obj (op V)) a := rfl

@[simp] theorem sectionRestriction_comp {U V W : Opens (PrimeSpectrum.Top R)}
    (hUV : V ≤ U) (hVW : W ≤ V) (x : (Spec.structureSheaf R).obj.obj (op U)) :
    sectionRestriction hVW (sectionRestriction hUV x) = sectionRestriction (hVW.trans hUV) x := by
  change (Spec.structureSheaf R).obj.map (homOfLE hVW).op
    ((Spec.structureSheaf R).obj.map (homOfLE hUV).op x) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

@[simp] theorem sectionRestriction_self {U : Opens (PrimeSpectrum.Top R)}
    (x : (Spec.structureSheaf R).obj.obj (op U)) : sectionRestriction le_rfl x = x := by
  change (Spec.structureSheaf R).obj.map (𝟙 (op U)) x = x
  exact congrArg (fun f : (Spec.structureSheaf R).obj.obj (op U) ⟶
    (Spec.structureSheaf R).obj.obj (op U) => f x) ((Spec.structureSheaf R).obj.map_id (op U))

theorem basicOpen_le_of_dvd {f g : R} (h : f ∣ g) :
    PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f := by
  intro P hPg hPf
  obtain ⟨a, ha⟩ := h
  apply hPg
  rw [ha]
  exact P.asIdeal.mul_mem_right a hPf

theorem localizedSection_restriction (f g : R) (h : f ∣ g) (x : basicSections R f) :
    (basicSectionEquiv g).symm (sectionRestriction (basicOpen_le_of_dvd h) x) =
      restriction f g h ((basicSectionEquiv f).symm x) := by
  have he : (basicSectionEquiv g).symm.toRingHom.comp
        (sectionRestriction (basicOpen_le_of_dvd h)) =
      (restriction f g h).comp (basicSectionEquiv f).symm.toRingHom := by
    apply IsLocalization.ringHom_ext (.powers f)
    ext a
    simp
  exact RingHom.congr_fun he x

def structureAb (R : Type u) [CommRing R] :
    CategoryTheory.Sheaf (Opens.grothendieckTopology (PrimeSpectrum.Top R)) AddCommGrpCat.{u} :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj (Spec.structureSheaf R)

theorem basic_sections_cech_one_exact {I : Type u} [Fintype I]
    (ι : R →+* K) (hι : Function.Injective ι) (f : I → R)
    (hf : ∀ i, ι (f i) ≠ 0) (hspan : Ideal.span (Set.range f) = ⊤)
    (z : ∀ i j, basicSections R (f i * f j))
    (hcocycle : ∀ i j k,
      sectionRestriction (basicOpen_le_of_dvd (show f i * f k ∣ f i * f j * f k from
          ⟨f j, by ring⟩)) (z i k) -
        sectionRestriction (basicOpen_le_of_dvd (show f j * f k ∣ f i * f j * f k from
          ⟨f i, by ring⟩)) (z j k) =
      sectionRestriction (basicOpen_le_of_dvd (dvd_mul_right (f i * f j) (f k))) (z i j)) :
    ∃ b : ∀ i, basicSections R (f i), ∀ i j,
      sectionRestriction (basicOpen_le_of_dvd (dvd_mul_right (f i) (f j))) (b i) -
        sectionRestriction (basicOpen_le_of_dvd (dvd_mul_left (f j) (f i))) (b j) = z i j := by
  let zz (i j : I) := (basicSectionEquiv (f i * f j)).symm (z i j)
  have hc (i j k : I) :
      restriction (f i * f k) (f i * f j * f k) (⟨f j, by ring⟩) (zz i k) -
        restriction (f j * f k) (f i * f j * f k) (⟨f i, by ring⟩) (zz j k) =
      tripleRestriction f i j k (zz i j) := by
    have h := congrArg (basicSectionEquiv (f i * f j * f k)).symm (hcocycle i j k)
    simpa only [map_sub,
      localizedSection_restriction (f i * f k) (f i * f j * f k) (⟨f j, by ring⟩),
      localizedSection_restriction (f j * f k) (f i * f j * f k) (⟨f i, by ring⟩),
      localizedSection_restriction (f i * f j) (f i * f j * f k) (dvd_mul_right _ _),
      zz, tripleRestriction] using h
  obtain ⟨bb, hb⟩ := finite_principal_cech_one_exact ι hι f hf hspan zz hc
  refine ⟨fun i => basicSectionEquiv (f i) (bb i), fun i j => ?_⟩
  apply (basicSectionEquiv (f i * f j)).symm.injective
  simpa only [map_sub,
    localizedSection_restriction (f i) (f i * f j) (dvd_mul_right _ _),
    localizedSection_restriction (f j) (f i * f j) (dvd_mul_left _ _),
    AlgEquiv.symm_apply_apply, zz] using hb i j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem structureAb_cech_one_exact {I : Type u} [Fintype I]
    (ι : R →+* K) (hι : Function.Injective ι) (f : I → R)
    (hf : ∀ i, ι (f i) ≠ 0) (hspan : Ideal.span (Set.range f) = ⊤) :
    CechOneExact (structureAb R) (fun i => PrimeSpectrum.basicOpen (f i)) := by
  change ∀ z : ∀ i j, (Spec.structureSheaf R).obj.obj
      (op (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j))),
    (∀ i j k,
      sectionRestriction (inf_le_inf inf_le_left le_rfl) (z i k) -
        sectionRestriction (inf_le_inf inf_le_right le_rfl) (z j k) =
      sectionRestriction inf_le_left (z i j)) →
    ∃ b : ∀ i, basicSections R (f i), ∀ i j,
      sectionRestriction inf_le_left (b i) - sectionRestriction inf_le_right (b j) = z i j
  intro z hz
  let zz (i j : I) : basicSections R (f i * f j) :=
    sectionRestriction (PrimeSpectrum.basicOpen_mul (f i) (f j)).le (z i j)
  have hc (i j k : I) :
      sectionRestriction (basicOpen_le_of_dvd (show f i * f k ∣ f i * f j * f k from
          ⟨f j, by ring⟩)) (zz i k) -
        sectionRestriction (basicOpen_le_of_dvd (show f j * f k ∣ f i * f j * f k from
          ⟨f i, by ring⟩)) (zz j k) =
      sectionRestriction (basicOpen_le_of_dvd (dvd_mul_right (f i * f j) (f k))) (zz i j) := by
    have ht : PrimeSpectrum.basicOpen (f i * f j * f k) ≤
        (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) ⊓
          PrimeSpectrum.basicOpen (f k) :=
      (PrimeSpectrum.basicOpen_mul _ _).le.trans
        (inf_le_inf (PrimeSpectrum.basicOpen_mul _ _).le le_rfl)
    have h := congrArg (sectionRestriction ht) (hz i j k)
    simpa only [map_sub, zz, sectionRestriction_comp] using h
  obtain ⟨b, hb⟩ := basic_sections_cech_one_exact ι hι f hf hspan zz hc
  refine ⟨b, fun i j => ?_⟩
  have h := congrArg (sectionRestriction (PrimeSpectrum.basicOpen_mul (f i) (f j)).ge) (hb i j)
  simpa only [map_sub, zz, sectionRestriction_comp, sectionRestriction_self] using h

end Cylinder.ActualAffineCechOne

end
