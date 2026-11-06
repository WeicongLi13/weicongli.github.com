module

public import Cylinder.GlobalProjectiveTwist

/-! Multiplication of actual local homogeneous fractions adds degrees.
In particular an actual global section gives a morphism of the global
module sheaves; neither global-section formulas nor vanishing are assumed. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistMultiplication

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem mul_mem (v w : ℤ) (U : (plane K).Opens)
    (f g : ∀ q : U, FullLocal K q.val)
    (hf : (isLocallyFraction K v).pred f) (hg : (isLocallyFraction K w).pred g) :
    (isLocallyFraction K (v + w)).pred (f * g) := by
  intro x
  rcases hf x with ⟨Vf, hxf, ifu, mf, nf, Hf, Bf, hdf, hHf, hBf, hbf, hef⟩
  rcases hg x with ⟨Vg, hxg, igu, mg, ng, Hg, Bg, hdg, hHg, hBg, hbg, heg⟩
  refine ⟨Vf ⊓ Vg, ⟨hxf, hxg⟩, Opens.infLELeft _ _ ≫ ifu,
    mf + mg, nf + ng, Hf * Hg, Bf * Bg, ?_, hHf.mul hHg, hBf.mul hBg, ?_, ?_⟩
  · omega
  · intro q
    exact q.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hbf ⟨q.val, q.property.1⟩) (hbg ⟨q.val, q.property.2⟩)
  · rintro ⟨q, hq⟩
    simp only [Subtype.forall, Opens.apply_mk] at hef heg
    simp only [Pi.mul_apply, Opens.apply_mk, hef q hq.1, heg q hq.2,
      Localization.mk_mul]
    exact congrArg (Localization.mk (Hf * Hg)) (Subtype.ext rfl)

def sectionMultiply (v w : ℤ) (U : (plane K).Opens)
    (f : sectionsSubmodule K v U) :
    sectionsSubmodule K w U →ₗ[Γ(plane K, U)] sectionsSubmodule K (v + w) U where
  toFun g := ⟨f.val * g.val, mul_mem K v w U f.val g.val f.property g.property⟩
  map_add' g h := by
    apply Subtype.ext
    funext q
    exact mul_add _ _ _
  map_smul' s g := by
    apply Subtype.ext
    funext q
    change f.val q * ((s.val q).val * g.val q) = (s.val q).val * (f.val q * g.val q)
    exact mul_left_comm _ _ _

theorem sectionMultiply_apply (v w : ℤ) (U : (plane K).Opens)
    (f : sectionsSubmodule K v U) (g : sectionsSubmodule K w U) (q : U) :
    (sectionMultiply K v w U f g).val q = f.val q * g.val q := rfl

def multiplyByGlobalSection (d v : ℤ) (f : Γ(twist K d, ⊤)) :
    twist K v ⟶ twist K (d + v) where
  val :=
    { app := fun U => ModuleCat.ofHom
        (sectionMultiply K d v U.unop
          ((twist K d).presheaf.map (homOfLE le_top).op f))
      naturality := by intro U V i; rfl }

theorem multiplyByGlobalSection_apply (d v : ℤ) (f : Γ(twist K d, ⊤))
    (U : (plane K).Opens) (g : Γ(twist K v, U)) (q : U) :
    (((multiplyByGlobalSection K d v f).app U) g).val q =
      f.val ⟨q.val, trivial⟩ * g.val q := rfl

end Cylinder.GlobalTwistMultiplication
end
