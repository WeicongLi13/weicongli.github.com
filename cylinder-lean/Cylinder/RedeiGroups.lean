import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Complement
import Mathlib.LinearAlgebra.Dimension.Free
import Cylinder.Geometry

/-! Transfer the rank-three coordinate statement to the elementary abelian
group formulation. The hypothesis on the exponent is intrinsic to G. -/
namespace Cylinder.Redei
open Geometry

variable {p : ℕ} [Fact p.Prime]

private theorem complement_map_equiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (A B : Finset G) (h : AddSubgroup.IsComplement (A : Set G) B) :
    AddSubgroup.IsComplement
      ((A.map e.toEquiv.toEmbedding : Finset H) : Set H)
      (B.map e.toEquiv.toEmbedding : Finset H) := by
  let u := (Finset.equivMap e.toEquiv.toEmbedding A).prodCongr
    (Finset.equivMap e.toEquiv.toEmbedding B)
  change Function.Bijective (fun x : A.map e.toEquiv.toEmbedding × B.map e.toEquiv.toEmbedding =>
    (x.1 : H) + x.2)
  apply (u.bijective_comp _).mp
  have he : (fun x : A.map e.toEquiv.toEmbedding × B.map e.toEquiv.toEmbedding =>
      (x.1 : H) + x.2) ∘ u = e ∘ (fun x : A × B => (x.1 : G) + x.2) := by
    funext x
    exact (e.map_add _ _).symm
  rw [he]
  exact e.bijective.comp h

/-- A proof in coordinates gives exactly the proper-subgroup conclusion for any
finite abelian group of order p³ killed by p. -/
private theorem group_factorization_with_module
    (hcoord : ∀ (A B : Finset (Point p)), 0 ∈ A → 0 ∈ B →
      AddSubgroup.IsComplement (A : Set (Point p)) B →
      Submodule.span (ZMod p) (A : Set (Point p)) ≠ ⊤ ∨
      Submodule.span (ZMod p) (B : Set (Point p)) ≠ ⊤)
    {G : Type*} [AddCommGroup G] [Module (ZMod p) G] [Finite G]
    (horder : Nat.card G = p ^ 3)
    (A B : Finset G) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (htile : AddSubgroup.IsComplement (A : Set G) B) :
    AddSubgroup.closure (A : Set G) ≠ ⊤ ∨ AddSubgroup.closure (B : Set G) ≠ ⊤ := by
  classical
  have hdim : Module.finrank (ZMod p) G = 3 := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := G)
    rw [Nat.card_zmod] at hc
    exact hc.symm.trans horder
  let e : G ≃ₗ[ZMod p] Point p := LinearEquiv.ofFinrankEq (R := ZMod p) G (Point p) (by simpa [Point] using hdim)
  let f := e.toEquiv.toEmbedding
  have hn (S : Finset G) (hs : 0 ∈ S) : 0 ∈ S.map f :=
    Finset.mem_map.mpr ⟨0, hs, e.map_zero⟩
  have pull (S : Finset G)
      (h : Submodule.span (ZMod p) (↑(S.map f) : Set (Point p)) ≠ ⊤) :
      AddSubgroup.closure (S : Set G) ≠ ⊤ := by
    let U := Submodule.span (ZMod p) (↑(S.map f) : Set (Point p))
    have hs : AddSubgroup.closure (S : Set G) ≤ (U.comap e.toLinearMap).toAddSubgroup :=
      (AddSubgroup.closure_le _).2 (fun x hx => Submodule.subset_span (Finset.mem_map.mpr ⟨x, hx, rfl⟩))
    intro htop
    apply h
    apply top_unique
    intro y _
    obtain ⟨x,rfl⟩ := e.surjective y
    exact hs (htop.symm ▸ (show x ∈ (⊤ : AddSubgroup G) from trivial))
  exact (hcoord (A.map f) (B.map f) (hn A hA) (hn B hB)
    (complement_map_equiv e.toAddEquiv A B htile)).imp (pull A) (pull B)
/-- A proof in coordinates gives exactly the proper-subgroup conclusion for any
finite abelian group of order p³ killed by p. -/
theorem group_factorization_of_coordinates
    (hcoord : ∀ (A B : Finset (Point p)), 0 ∈ A → 0 ∈ B →
      AddSubgroup.IsComplement (A : Set (Point p)) B →
      Submodule.span (ZMod p) (A : Set (Point p)) ≠ ⊤ ∨
      Submodule.span (ZMod p) (B : Set (Point p)) ≠ ⊤)
    {G : Type*} [AddCommGroup G] [Finite G]
    (horder : Nat.card G = p ^ 3) (hexp : ∀ x : G, p • x = 0)
    (A B : Finset G) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (htile : AddSubgroup.IsComplement (A : Set G) B) :
    AddSubgroup.closure (A : Set G) ≠ ⊤ ∨ AddSubgroup.closure (B : Set G) ≠ ⊤ := by
  let _ : Module (ZMod p) G := AddCommGroup.zmodModule hexp
  exact group_factorization_with_module (p := p) hcoord horder A B hA hB htile

end Cylinder.Redei
