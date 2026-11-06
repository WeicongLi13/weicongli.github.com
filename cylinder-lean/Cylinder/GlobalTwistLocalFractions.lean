module

public import Cylinder.CoordinateTwistChartModule
public import Cylinder.ProjectiveCompleteIntersectionCover
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.LocalPredicate

/-! Degree-v local homogeneous fractions at every actual point of Proj.
The coefficient action is the original multiplication in polynomial
localizations. No cohomology or global-section identification is assumed. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistLocalFractions

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

abbrev plane : Scheme := Proj (grading K)
abbrev FullLocal (q : plane K) := Localization.AtPrime q.asHomogeneousIdeal.toIdeal

def IsFraction (v : ℤ) {U : (plane K).Opens} (f : ∀ q : U, FullLocal K q.val) : Prop :=
  ∃ (m n : ℕ) (H B : PlaneRing K), (m : ℤ) - n = v ∧ H.IsHomogeneous m ∧ B.IsHomogeneous n ∧
    ∃ hB : ∀ q : U, B ∉ q.val.asHomogeneousIdeal,
      ∀ q : U, f q = Localization.mk H ⟨B, hB q⟩

def isFractionPrelocal (v : ℤ) : PrelocalPredicate (fun q : plane K => FullLocal K q) where
  pred f := IsFraction K v f
  res := by
    rintro V U i f ⟨m, n, H, B, hd, hH, hB, hb, he⟩
    exact ⟨m, n, H, B, hd, hH, hB, fun q => hb (i q), fun q => he (i q)⟩

def isLocallyFraction (v : ℤ) : LocalPredicate (fun q : plane K => FullLocal K q) :=
  (isFractionPrelocal K v).sheafify

theorem zero_mem (v : ℤ) (U : (plane K).Opens) :
    (isLocallyFraction K v).pred (0 : ∀ q : U, FullLocal K q.val) := by
  intro x
  obtain ⟨i, hi⟩ := not_forall.mp
    (Cylinder.ProjectiveCompleteIntersectionCover.not_all_variables_mem x.val)
  let V := U ⊓ Proj.basicOpen (grading K) (X i)
  let m := v.toNat
  let n := (-v).toNat
  refine ⟨V, ⟨x.property, hi⟩, Opens.infLELeft _ _, m, n, 0, X i ^ n, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [m, n]
    omega
  · exact isHomogeneous_zero (Option (Fin 2)) K m
  · exact isHomogeneous_X_pow i n
  · intro q hq
    exact q.property.2 (q.val.isPrime.mem_of_pow_mem n hq)
  · intro q
    simp only [Pi.zero_apply, Localization.mk_zero]

theorem add_mem (v : ℤ) (U : (plane K).Opens) (f g : ∀ q : U, FullLocal K q.val)
    (hf : (isLocallyFraction K v).pred f) (hg : (isLocallyFraction K v).pred g) :
    (isLocallyFraction K v).pred (f + g) := by
  intro x
  rcases hf x with ⟨Vf, hxf, ifu, mf, nf, Hf, Bf, hdf, hHf, hBf, hbf, hef⟩
  rcases hg x with ⟨Vg, hxg, igu, mg, ng, Hg, Bg, hdg, hHg, hBg, hbg, heg⟩
  have heq : ng + mf = nf + mg := by omega
  refine ⟨Vf ⊓ Vg, ⟨hxf, hxg⟩, Opens.infLELeft _ _ ≫ ifu,
    nf + mg, nf + ng, Bf * Hg + Bg * Hf, Bf * Bg, ?_, ?_, hBf.mul hBg, ?_, ?_⟩
  · omega
  · exact (hBf.mul hHg).add (heq ▸ hBg.mul hHf)
  · intro q
    exact q.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hbf ⟨q.val, q.property.1⟩) (hbg ⟨q.val, q.property.2⟩)
  · rintro ⟨q, hq⟩
    simp only [Subtype.forall, Opens.apply_mk] at hef heg
    change f ⟨q, _⟩ + g ⟨q, _⟩ = _
    calc
      _ = Localization.mk Hf ⟨Bf, hbf ⟨q, hq.1⟩⟩ +
          Localization.mk Hg ⟨Bg, hbg ⟨q, hq.2⟩⟩ :=
        congrArg₂ (fun a b : FullLocal K q => a + b) (hef q hq.1) (heg q hq.2)
      _ = Localization.mk (Bf * Hg + Bg * Hf)
          (⟨Bf, hbf ⟨q, hq.1⟩⟩ * ⟨Bg, hbg ⟨q, hq.2⟩⟩) := Localization.add_mk _ _ _ _
      _ = _ := congrArg (Localization.mk (Bf * Hg + Bg * Hf)) (Subtype.ext rfl)

theorem regular_smul_mem (v : ℤ) (U : (plane K).Opens)
    (s : Γ(plane K, U)) (f : ∀ q : U, FullLocal K q.val)
    (hf : (isLocallyFraction K v).pred f) :
    (isLocallyFraction K v).pred (fun q => (s.val q).val * f q) := by
  have hs : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction (grading K)).pred s.val := s.property
  intro x
  rcases hs x with ⟨Vs, hxs, isu, k, ⟨Hs, hHs⟩, ⟨Bs, hBs⟩, hbs, hes⟩
  rcases hf x with ⟨Vf, hxf, ifu, m, n, Hf, Bf, hd, hHf, hBf, hbf, hef⟩
  refine ⟨Vs ⊓ Vf, ⟨hxs, hxf⟩, Opens.infLELeft _ _ ≫ isu,
    k + m, k + n, Hs * Hf, Bs * Bf, ?_, hHs.mul hHf, hBs.mul hBf, ?_, ?_⟩
  · omega
  · intro q
    exact q.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hbs ⟨q.val, q.property.1⟩) (hbf ⟨q.val, q.property.2⟩)
  · rintro ⟨q, hq⟩
    simp only [Subtype.forall, Opens.apply_mk] at hes hef
    simp only [Opens.apply_mk, hes q hq.1, hef q hq.2,
      HomogeneousLocalization.val_mk, Localization.mk_mul, Submonoid.mk_mul_mk]

def scalarMap (U : (plane K).Opens) :
    Γ(plane K, U) →+* (∀ q : U, FullLocal K q.val) where
  toFun s q := (s.val q).val
  map_one' := by funext q; exact HomogeneousLocalization.val_one
  map_mul' s t := by funext q; exact HomogeneousLocalization.val_mul _ _
  map_zero' := by funext q; exact HomogeneousLocalization.val_zero
  map_add' s t := by funext q; exact HomogeneousLocalization.val_add _ _

instance sectionFunctionAlgebra (U : (plane K).Opens) :
    Algebra Γ(plane K, U) (∀ q : U, FullLocal K q.val) :=
  (scalarMap K U).toAlgebra

def sectionsSubmodule (v : ℤ) (U : (plane K).Opens) :
    Submodule Γ(plane K, U) (∀ q : U, FullLocal K q.val) where
  carrier := (isLocallyFraction K v).pred
  zero_mem' := zero_mem K v U
  add_mem' := add_mem K v U _ _
  smul_mem' s f hf := regular_smul_mem K v U s f hf

theorem sections_smul_coe (v : ℤ) (U : (plane K).Opens)
    (s : Γ(plane K, U)) (f : sectionsSubmodule K v U) (q : U) :
    ((s • f : sectionsSubmodule K v U) : ∀ q : U, FullLocal K q.val) q =
      (s.val q).val * f.val q := rfl

end Cylinder.GlobalTwistLocalFractions
end
