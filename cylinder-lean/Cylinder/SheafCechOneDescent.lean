module

public import Cylinder.SheafInjectiveCokernel
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective

/-! Descent of actual local lifts using degree-one Čech exactness.
The differences of local lifts are lifted through the actual kernel sheaf.
Their cocycle identity follows from the monomorphism, and the corrected local
lifts are glued by the sheaf axiom.  This is the comparison step; its Čech
exactness input must still be supplied for the actual sheaf and cover. -/

@[expose] public section
noncomputable section

universe u

namespace Cylinder.SheafCechOneDescent

open TopCat TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

variable {X : TopCat.{u}}

abbrev sectionsRestrict (F : TopCat.Sheaf AddCommGrpCat.{u} X) {U V : Opens X}
    (h : V ≤ U) : F.obj.obj (op U) →+ F.obj.obj (op V) :=
  (F.obj.map (homOfLE h).op).hom

@[simp] theorem sectionsRestrict_comp (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {U V W : Opens X} (hUV : V ≤ U) (hVW : W ≤ V) (x : F.obj.obj (op U)) :
    sectionsRestrict F hVW (sectionsRestrict F hUV x) =
      sectionsRestrict F (hVW.trans hUV) x := by
  change F.obj.map (homOfLE hVW).op (F.obj.map (homOfLE hUV).op x) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

@[simp] theorem map_sectionsRestrict {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) {U V : Opens X} (h : V ≤ U) (x : F.obj.obj (op U)) :
    f.hom.app (op V) (sectionsRestrict F h x) =
      sectionsRestrict G h (f.hom.app (op U) x) :=
  TopCat.Presheaf.map_restrict f.hom h x

def CechOneExact {I : Type*} (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : I → Opens X) : Prop :=
  ∀ z : ∀ i j, F.obj.obj (op (U i ⊓ U j)),
    (∀ i j k,
      sectionsRestrict F (inf_le_inf inf_le_left le_rfl) (z i k) -
        sectionsRestrict F (inf_le_inf inf_le_right le_rfl) (z j k) =
      sectionsRestrict F inf_le_left (z i j)) →
    ∃ b : ∀ i, F.obj.obj (op (U i)), ∀ i j,
      sectionsRestrict F inf_le_left (b i) - sectionsRestrict F inf_le_right (b j) = z i j

theorem shortComplex_comp_app_zero
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (U : Opens X)
    (x : S.X₁.obj.obj (op U)) : S.g.hom.app (op U) (S.f.hom.app (op U) x) = 0 := by
  have h := congrArg (fun f : S.X₁ ⟶ S.X₃ => f.hom.app (op U) x) S.zero
  exact h

/-- A genuine local lifting and Čech correction argument for a short exact sequence. -/
theorem lift_section_on_open_of_cech_one_exact {I : Type*}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (V : Opens X) (U : I → Opens X) (hUV : ∀ i, U i ≤ V) (hcover : V ≤ iSup U)
    (hcech : CechOneExact S.X₁ U) (t : S.X₃.obj.obj (op V))
    (s : ∀ i, S.X₂.obj.obj (op (U i)))
    (hs : ∀ i, S.g.hom.app (op (U i)) (s i) = sectionsRestrict S.X₃ (hUV i) t) :
    ∃ a : S.X₂.obj.obj (op V), S.g.hom.app (op V) a = t := by
  classical
  let : Mono S.f := hS.mono_f
  let : Mono S.f.hom := Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{u} X) S.f
  have hinj (V : Opens X) : Function.Injective (S.f.hom.app (op V)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  let d (i j : I) : S.X₂.obj.obj (op (U i ⊓ U j)) :=
    sectionsRestrict S.X₂ inf_le_left (s i) - sectionsRestrict S.X₂ inf_le_right (s j)
  have hd (i j : I) : S.g.hom.app (op (U i ⊓ U j)) (d i j) = 0 := by
    simp only [d, map_sub, map_sectionsRestrict, hs, sectionsRestrict_comp, sub_self]
  choose z hz using fun i j =>
    TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f (d i j) (hd i j)
  have hzc (i j k : I) :
      sectionsRestrict S.X₁ (inf_le_inf inf_le_left le_rfl) (z i k) -
        sectionsRestrict S.X₁ (inf_le_inf inf_le_right le_rfl) (z j k) =
      sectionsRestrict S.X₁ inf_le_left (z i j) := by
    apply hinj (U i ⊓ U j ⊓ U k)
    simp only [map_sub, map_sectionsRestrict, hz, d, map_sub, sectionsRestrict_comp]
    abel
  obtain ⟨b, hb⟩ := hcech z hzc
  let sf (i : I) : S.X₂.obj.obj (op (U i)) := s i - S.f.hom.app (op (U i)) (b i)
  have hcompat : TopCat.Presheaf.IsCompatible S.X₂.obj U sf := by
    intro i j
    have h := congrArg (fun x => S.f.hom.app (op (U i ⊓ U j)) x) (hb i j)
    simp only [map_sub, map_sectionsRestrict, hz, d] at h
    change sectionsRestrict S.X₂ inf_le_left (sf i) =
      sectionsRestrict S.X₂ inf_le_right (sf j)
    simp only [sf, map_sub]
    calc
      sectionsRestrict S.X₂ inf_le_left (s i) -
          sectionsRestrict S.X₂ inf_le_left (S.f.hom.app (op (U i)) (b i)) =
        (d i j - (sectionsRestrict S.X₂ inf_le_left (S.f.hom.app (op (U i)) (b i)) -
          sectionsRestrict S.X₂ inf_le_right (S.f.hom.app (op (U j)) (b j)))) +
          (sectionsRestrict S.X₂ inf_le_right (s j) -
            sectionsRestrict S.X₂ inf_le_right (S.f.hom.app (op (U j)) (b j))) := by
              dsimp [d]
              abel
      _ = _ := by rw [h]; simp [d]
  obtain ⟨a, ha, _⟩ := S.X₂.existsUnique_gluing' U V (fun i => homOfLE (hUV i))
    hcover sf hcompat
  refine ⟨a, ?_⟩
  apply S.X₃.eq_of_locally_eq' U V (fun i => homOfLE (hUV i)) hcover
  intro i
  change sectionsRestrict S.X₃ (hUV i) (S.g.hom.app (op V) a) =
    sectionsRestrict S.X₃ (hUV i) t
  rw [← map_sectionsRestrict]
  have hai : sectionsRestrict S.X₂ (hUV i) a = sf i := ha i
  rw [hai]
  simp only [sf, map_sub, hs, shortComplex_comp_app_zero, sub_zero]

theorem lift_section_of_cech_one_exact {I : Type*}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (U : I → Opens X) (hcover : (⊤ : Opens X) ≤ iSup U)
    (hcech : CechOneExact S.X₁ U) (t : S.X₃.obj.obj (op (⊤ : Opens X)))
    (s : ∀ i, S.X₂.obj.obj (op (U i)))
    (hs : ∀ i, S.g.hom.app (op (U i)) (s i) = sectionsRestrict S.X₃ le_top t) :
    ∃ a : S.X₂.obj.obj (op (⊤ : Opens X)), S.g.hom.app (op ⊤) a = t :=
  lift_section_on_open_of_cech_one_exact hS ⊤ U (fun _ => le_top) hcover hcech t s hs

theorem sections_surjective_of_cech_one_exact {I : Type*}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (U : I → Opens X) (hcover : (⊤ : Opens X) ≤ iSup U)
    (hcech : CechOneExact S.X₁ U)
    (hlift : ∀ t : S.X₃.obj.obj (op (⊤ : Opens X)), ∀ i,
      ∃ s : S.X₂.obj.obj (op (U i)),
        S.g.hom.app (op (U i)) s = sectionsRestrict S.X₃ le_top t) :
    Function.Surjective (S.g.hom.app (op (⊤ : Opens X))) := by
  intro t
  choose s hs using hlift t
  exact lift_section_of_cech_one_exact hS U hcover hcech t s hs

/-- Local lifts and their covering opens are obtained from the actual sheaf epimorphism. -/
theorem exists_local_lifting_cover {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) [Epi f] (t : G.obj.obj (op (⊤ : Opens X))) :
    ∃ U : X → Opens X, (⊤ : Opens X) ≤ iSup U ∧
      ∃ s : ∀ x, F.obj.obj (op (U x)), ∀ x,
        f.hom.app (op (U x)) (s x) = sectionsRestrict G le_top t := by
  classical
  have hlocal := (TopCat.Presheaf.isLocallySurjective_iff f.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr inferInstance)
  have hl (x : X) : ∃ V : Opens X, ∃ s : F.obj.obj (op V),
      f.hom.app (op V) s = sectionsRestrict G le_top t ∧ x ∈ V := by
    obtain ⟨V, _, ⟨s, hs⟩, hx⟩ := hlocal ⊤ t x (by trivial)
    exact ⟨V, s, hs, hx⟩
  choose U s hs hx using hl
  refine ⟨U, ?_, s, hs⟩
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hx x⟩

theorem sections_surjective_of_all_cech_one_exact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (hcech : ∀ U : X → Opens X, (⊤ : Opens X) ≤ iSup U → CechOneExact S.X₁ U) :
    Function.Surjective (S.g.hom.app (op (⊤ : Opens X))) := by
  let : Epi S.g := hS.epi_g
  intro t
  obtain ⟨U, hcover, s, hs⟩ := exists_local_lifting_cover S.g t
  exact lift_section_of_cech_one_exact hS U hcover (hcech U hcover) t s hs

end Cylinder.SheafCechOneDescent

end
