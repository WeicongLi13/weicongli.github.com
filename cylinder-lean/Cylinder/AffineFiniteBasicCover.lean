module

public import Cylinder.SheafCechOneDescent
public import Mathlib.AlgebraicGeometry.StructureSheaf

/-! Actual finite principal refinements of open covers of Spec R.
The finite set, refining indices and nonzero defining elements are all
constructed from the basic-open basis and compactness of the spectrum. -/

@[expose] public section
noncomputable section

universe u v

namespace Cylinder.AffineFiniteBasicCover

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.SheafCechOneDescent

variable {R : Type u} [CommRing R]

theorem exists_finite_basic_refinement {I : Type v}
    (U : I → Opens (PrimeSpectrum.Top R))
    (hcover : (⊤ : Opens (PrimeSpectrum.Top R)) ≤ iSup U) :
    ∃ (J : Type u) (_ : Fintype J) (f : J → R) (ref : J → I),
      (∀ j, f j ≠ 0) ∧ (∀ j, PrimeSpectrum.basicOpen (f j) ≤ U (ref j)) ∧
        Ideal.span (Set.range f) = ⊤ := by
  classical
  have hlocal (P : PrimeSpectrum.Top R) : ∃ (i : I) (f : R),
      P ∈ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ U i := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover (by trivial : P ∈ (⊤ : Opens _)))
    obtain ⟨_, ⟨f, rfl⟩, hPf, hfU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp (U i).isOpen P hi
    exact ⟨i, f, hPf, hfU⟩
  choose r f hPf hfU using hlocal
  obtain ⟨t, ht⟩ :=
    (show IsCompact (Set.univ : Set (PrimeSpectrum R)) from isCompact_univ).elim_finite_subcover
    (fun P => (PrimeSpectrum.basicOpen (f P) : Set (PrimeSpectrum R)))
    (fun _ => (PrimeSpectrum.basicOpen _).isOpen)
    (fun P _ => Set.mem_iUnion_of_mem P (hPf P))
  refine ⟨t, inferInstance, fun j => f j.val, fun j => r j.val, ?_, ?_, ?_⟩
  · intro j hj
    simpa [hj] using hPf j.val
  · intro j
    exact hfU j.val
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_unique
    intro P hP
    simpa using ht hP

/-- An actual sheaf epimorphism admits local lifts on a finite principal cover.
Neither a chosen covering nor local section-surjectivity is a hypothesis. -/
theorem exists_finite_basic_lifting_cover
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (PrimeSpectrum.Top R)}
    (q : F ⟶ G) [Epi q] (t : G.obj.obj (op (⊤ : Opens (PrimeSpectrum.Top R)))) :
    ∃ (J : Type u) (_ : Fintype J) (f : J → R),
      (∀ j, f j ≠ 0) ∧ Ideal.span (Set.range f) = ⊤ ∧
      ∃ s : ∀ j, F.obj.obj (op (PrimeSpectrum.basicOpen (f j))), ∀ j,
        q.hom.app (op (PrimeSpectrum.basicOpen (f j))) (s j) = sectionsRestrict G le_top t := by
  obtain ⟨U, hU, s, hs⟩ := exists_local_lifting_cover q t
  obtain ⟨J, hJ, f, ref, hf0, hfU, hspan⟩ := exists_finite_basic_refinement U hU
  let := hJ
  refine ⟨J, hJ, f, hf0, hspan, fun j => sectionsRestrict F (hfU j) (s (ref j)), ?_⟩
  intro j
  rw [map_sectionsRestrict, hs, sectionsRestrict_comp]

end Cylinder.AffineFiniteBasicCover

end
