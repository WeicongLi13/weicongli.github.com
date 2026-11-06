module

public import Cylinder.ProjectiveIncidence
public import Mathlib.Data.Fintype.Option

/-!
# The dual line of a parallel affine plane pencil

The line is the projectivization of the actual vector span of the infinity
functional and one homogenized affine plane functional. Its points are
exactly infinity and the parallel affine planes with the same nonzero normal.
-/

@[expose] public section

noncomputable section

namespace Cylinder.DualPencils

open Cylinder.ProjectiveGeometry
open scoped LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

abbrev infinityFunctional : Module.Dual (ZMod p) (Vector p) :=
  LinearMap.proj (0 : Fin 4)

theorem infinityFunctional_ne_zero : infinityFunctional p ≠ 0 := by
  intro h
  have hh := LinearMap.congr_fun h (Pi.single (0 : Fin 4) 1)
  simp at hh

@[simp] theorem affineFunctional_single_zero (n : Geometry.Point p) (b : ZMod p) :
    affinePlaneFunctional p n b (Pi.single (0 : Fin 4) 1) = -b := by
  simp [affinePlaneFunctional, pairingMap, pairing, Pi.single_apply]

@[simp] theorem affineFunctional_single_succ (n : Geometry.Point p) (b : ZMod p)
    (i : Fin 3) : affinePlaneFunctional p n b (Pi.single i.succ 1) = n i := by
  simp [affinePlaneFunctional, pairingMap, pairing, Pi.single_apply]

theorem affineFunctional_shift (n : Geometry.Point p) (b c : ZMod p) :
    affinePlaneFunctional p n c =
      (b - c) • infinityFunctional p + affinePlaneFunctional p n b := by
  apply LinearMap.ext
  intro x
  simp [affinePlaneFunctional, pairingMap, pairing, Fin.sum_univ_succ,
    infinityFunctional, smul_eq_mul]
  ring

theorem scalar_affine_ne_infinity {n : Geometry.Point p} (hn : n ≠ 0)
    (b t : ZMod p) : t • affinePlaneFunctional p n b ≠ infinityFunctional p := by
  intro h
  obtain ⟨i, hi⟩ := Geometry.nonzero_coordinate p hn
  have hs := LinearMap.congr_fun h (Pi.single i.succ 1)
  have hmul : t * n i = 0 := by simpa [infinityFunctional, smul_eq_mul] using hs
  have ht : t = 0 := (mul_eq_zero.mp hmul).resolve_right hi
  rw [ht, zero_smul] at h
  exact infinityFunctional_ne_zero p h.symm

theorem infinity_ne_affinePlaneDual {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p) :
    infinity p ≠ affinePlaneDual p n b hn := by
  intro h
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' (ZMod p)
    (infinityFunctional p) (affinePlaneFunctional p n b)
    (infinityFunctional_ne_zero p) (affinePlaneFunctional_ne_zero p hn b)).mp h
  exact scalar_affine_ne_infinity p hn b t ht

theorem affinePlaneDual_injective {n : Geometry.Point p} (hn : n ≠ 0) :
    Function.Injective (fun b : ZMod p => affinePlaneDual p n b hn) := by
  intro b c h
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' (ZMod p)
    (affinePlaneFunctional p n b) (affinePlaneFunctional p n c)
    (affinePlaneFunctional_ne_zero p hn b) (affinePlaneFunctional_ne_zero p hn c)).mp h
  obtain ⟨i, hi⟩ := Geometry.nonzero_coordinate p hn
  have hs := LinearMap.congr_fun ht (Pi.single i.succ 1)
  have hmul : t * n i = n i := by simpa [smul_eq_mul] using hs
  have htone : t = 1 := mul_right_cancel₀ hi (hmul.trans (one_mul _).symm)
  have hc := LinearMap.congr_fun ht (Pi.single (0 : Fin 4) 1)
  simpa [htone, smul_eq_mul] using hc.symm

def pencilSubspace (n : Geometry.Point p) (b : ZMod p) :
    Submodule (ZMod p) (Module.Dual (ZMod p) (Vector p)) :=
  Submodule.span (ZMod p) ({infinityFunctional p, affinePlaneFunctional p n b} : Set _)

abbrev PencilPoint (n : Geometry.Point p) (b : ZMod p) :=
  {H : DualPoint p // H.submodule ≤ pencilSubspace p n b}

instance (n : Geometry.Point p) (b : ZMod p) : Fintype (PencilPoint p n b) :=
  Fintype.ofFinite _

theorem finrank_pencilSubspace {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p) :
    Module.finrank (ZMod p) (pencilSubspace p n b) = 2 := by
  have hli : LinearIndependent (ZMod p)
      ![infinityFunctional p, affinePlaneFunctional p n b] := by
    rw [linearIndependent_fin2]
    constructor
    · exact affinePlaneFunctional_ne_zero p hn b
    · intro t
      exact scalar_affine_ne_infinity p hn b t
  have hrange : Set.range ![infinityFunctional p, affinePlaneFunctional p n b] =
      ({infinityFunctional p, affinePlaneFunctional p n b} : Set _) := by
    ext f
    simp [or_comm]
  change Module.finrank (ZMod p)
    (Submodule.span (ZMod p) ({infinityFunctional p, affinePlaneFunctional p n b} : Set _)) = 2
  rw [← hrange]
  simpa using finrank_span_eq_card hli

theorem infinity_on_pencil (n : Geometry.Point p) (b : ZMod p) :
    (infinity p).submodule ≤ pencilSubspace p n b := by
  rw [infinity, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
  apply Submodule.subset_span
  simp

theorem affinePlaneDual_on_pencil {n : Geometry.Point p} (hn : n ≠ 0)
    (b c : ZMod p) : (affinePlaneDual p n c hn).submodule ≤ pencilSubspace p n b := by
  rw [affinePlaneDual, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
  apply (Submodule.mem_span_pair).mpr
  refine ⟨b - c, 1, ?_⟩
  simpa only [one_smul] using (affineFunctional_shift p n b c).symm

theorem pencilSubspace_le {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p)
    (W : Submodule (ZMod p) (Module.Dual (ZMod p) (Vector p)))
    (hinfinity : (infinity p).submodule ≤ W)
    (hplane : (affinePlaneDual p n b hn).submodule ≤ W) :
    pencilSubspace p n b ≤ W := by
  rw [infinity, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem] at hinfinity
  rw [affinePlaneDual, Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem] at hplane
  apply Submodule.span_le.mpr
  intro f hf
  change f ∈ W
  rcases Set.mem_insert_iff.mp hf with hf | hf
  · rw [hf]
    exact hinfinity
  · rw [Set.mem_singleton_iff.mp hf]
    exact hplane

/-- A projective line through infinity and the given plane is exactly this pencil. -/
theorem pencilSubspace_eq_of_finrank_two {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p)
    (W : Submodule (ZMod p) (Module.Dual (ZMod p) (Vector p)))
    (hW : Module.finrank (ZMod p) W = 2)
    (hinfinity : (infinity p).submodule ≤ W)
    (hplane : (affinePlaneDual p n b hn).submodule ≤ W) :
    pencilSubspace p n b = W :=
  Submodule.eq_of_le_of_finrank_eq (pencilSubspace_le p hn b W hinfinity hplane)
    ((finrank_pencilSubspace p hn b).trans hW.symm)

def parameterDual (n : Geometry.Point p) (hn : n ≠ 0) : Option (ZMod p) → DualPoint p
  | none => infinity p
  | some c => affinePlaneDual p n c hn

theorem parameterDual_injective {n : Geometry.Point p} (hn : n ≠ 0) :
    Function.Injective (parameterDual p n hn) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some c => exact False.elim (infinity_ne_affinePlaneDual p hn c h)
  | some b =>
    cases y with
    | none => exact False.elim (infinity_ne_affinePlaneDual p hn b h.symm)
    | some c => exact congrArg some (affinePlaneDual_injective p hn h)

theorem parameterDual_on_pencil {n : Geometry.Point p} (hn : n ≠ 0)
    (b : ZMod p) (c : Option (ZMod p)) :
    (parameterDual p n hn c).submodule ≤ pencilSubspace p n b := by
  cases c with
  | none => exact infinity_on_pencil p n b
  | some c => exact affinePlaneDual_on_pencil p hn b c

theorem pencil_classification {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p)
    (H : DualPoint p) (hH : H.submodule ≤ pencilSubspace p n b) :
    ∃ c : Option (ZMod p), parameterDual p n hn c = H := by
  induction H using Projectivization.ind with
  | h f hf =>
    rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem] at hH
    obtain ⟨α, β, hform⟩ := (Submodule.mem_span_pair).mp hH
    by_cases hβ : β = 0
    · refine ⟨none, ?_⟩
      change infinity p = Projectivization.mk (ZMod p) f hf
      apply Eq.symm
      apply (Projectivization.mk_eq_mk_iff' (ZMod p) f (infinityFunctional p)
        hf (infinityFunctional_ne_zero p)).mpr
      refine ⟨α, ?_⟩
      simpa [hβ] using hform
    · let c : ZMod p := b - α / β
      have hscalar : β * (b - c) = α := by
        change β * (b - (b - α / β)) = α
        rw [show b - (b - α / β) = α / β by ring, mul_comm, div_mul_cancel₀ _ hβ]
      have heq : β • affinePlaneFunctional p n c = f := by
        rw [affineFunctional_shift p n b c, smul_add, smul_smul, hscalar]
        exact hform
      refine ⟨some c, ?_⟩
      change affinePlaneDual p n c hn = Projectivization.mk (ZMod p) f hf
      apply Eq.symm
      exact (Projectivization.mk_eq_mk_iff' (ZMod p) f (affinePlaneFunctional p n c)
        hf (affinePlaneFunctional_ne_zero p hn c)).mpr ⟨β, heq⟩

def parameterPencil {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p)
    (c : Option (ZMod p)) : PencilPoint p n b :=
  ⟨parameterDual p n hn c, parameterDual_on_pencil p hn b c⟩

def pencilEquiv {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p) :
    Option (ZMod p) ≃ PencilPoint p n b :=
  Equiv.ofBijective (parameterPencil p hn b) (by
    constructor
    · intro x y h
      exact parameterDual_injective p hn (congrArg Subtype.val h)
    · intro H
      obtain ⟨c, hc⟩ := pencil_classification p hn b H.val H.property
      exact ⟨c, Subtype.ext hc⟩)

theorem card_pencil {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p) :
    Fintype.card (PencilPoint p n b) = p + 1 := by
  rw [← Fintype.card_congr (pencilEquiv p hn b)]
  simp

end Cylinder.DualPencils

end
