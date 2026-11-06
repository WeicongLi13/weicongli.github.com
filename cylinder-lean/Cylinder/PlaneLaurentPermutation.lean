module

public import Cylinder.PlaneLaurentPieces
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Coordinate permutations act on the literal exponent vectors of
the homogeneous Laurent pieces. Their action commutes with every
inclusion of coordinate intersections. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.PlaneLaurentPermutation

open Cylinder.PlaneLaurentPieces

set_option autoImplicit false

def exponentEquiv (e : Fin 3 ≃ Fin 3) : Exponent ≃ Exponent where
  toFun a := fun i => a (e.symm i)
  invFun a := fun i => a (e i)
  left_inv a := by funext i; exact congrArg a (e.symm_apply_apply i)
  right_inv a := by funext i; exact congrArg a (e.apply_symm_apply i)

theorem totalDegree_permute (e : Fin 3 ≃ Fin 3) (a : Exponent) :
    totalDegree (exponentEquiv e a) = totalDegree a := by
  simpa only [totalDegree, exponentEquiv, Equiv.coe_fn_mk, Fin.sum_univ_three]
    using e.symm.sum_comp a

theorem allowed_permute (e : Fin 3 ≃ Fin 3) (v : ℤ) (I : Finset (Fin 3)) (a : Exponent) :
    Allowed v (I.map e.toEmbedding) (exponentEquiv e a) ↔ Allowed v I a := by
  constructor
  · rintro ⟨hd, hn⟩
    refine ⟨(totalDegree_permute e a).symm.trans hd, ?_⟩
    intro i hi
    have hni : e i ∉ I.map e.toEmbedding := by simpa using hi
    simpa [exponentEquiv] using hn (e i) hni
  · rintro ⟨hd, hn⟩
    refine ⟨(totalDegree_permute e a).trans hd, ?_⟩
    intro i hi
    apply hn (e.symm i)
    intro hmem
    apply hi
    exact Finset.mem_map.mpr ⟨e.symm i, hmem, e.apply_symm_apply i⟩

variable {K : Type*} [CommRing K]

def laurentEquiv (e : Fin 3 ≃ Fin 3) : Laurent K ≃ₗ[K] Laurent K :=
  Finsupp.domLCongr (exponentEquiv e)

theorem laurentEquiv_coeff (e : Fin 3 ≃ Fin 3) (f : Laurent K) (a : Exponent) :
    laurentEquiv e f a = f ((exponentEquiv e).symm a) := by
  rfl

theorem laurentEquiv_mem (e : Fin 3 ≃ Fin 3) (v : ℤ) (I : Finset (Fin 3)) (f : Laurent K) :
    laurentEquiv e f ∈ piece v (I.map e.toEmbedding) ↔ f ∈ piece v I := by
  simp only [mem_piece_iff]
  constructor
  · intro hf a ha
    have h := hf (exponentEquiv e a) (by simpa [laurentEquiv_coeff] using ha)
    exact (allowed_permute e v I a).mp h
  · intro hf a ha
    have h := hf ((exponentEquiv e).symm a) (by simpa [laurentEquiv_coeff] using ha)
    simpa only [Equiv.apply_symm_apply] using
      (allowed_permute e v I ((exponentEquiv e).symm a)).mpr h

def pieceEquiv (e : Fin 3 ≃ Fin 3) (v : ℤ) (I : Finset (Fin 3)) :
    piece (K := K) v I ≃ₗ[K] piece (K := K) v (I.map e.toEmbedding) where
  toFun f := ⟨laurentEquiv (K := K) e f.val, (laurentEquiv_mem e v I f.val).mpr f.property⟩
  invFun f := ⟨(laurentEquiv (K := K) e).symm f.val,
    (laurentEquiv_mem e v I ((laurentEquiv (K := K) e).symm f.val)).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using f.property)⟩
  left_inv f := Subtype.ext ((laurentEquiv e).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((laurentEquiv e).apply_symm_apply f.val)
  map_add' f g := Subtype.ext ((laurentEquiv e).map_add f.val g.val)
  map_smul' a f := Subtype.ext ((laurentEquiv e).map_smul a f.val)

def inclusion (v : ℤ) {I J : Finset (Fin 3)} (hIJ : I ⊆ J) :
    piece (K := K) v I →ₗ[K] piece (K := K) v J :=
  Submodule.inclusion (p := piece (K := K) v I) (p' := piece (K := K) v J)
    (piece_mono (K := K) v hIJ)

theorem inclusion_natural (e : Fin 3 ≃ Fin 3) (v : ℤ)
    {I J : Finset (Fin 3)} (hIJ : I ⊆ J) (f : piece (K := K) v I) :
    pieceEquiv e v J (inclusion v hIJ f) =
      inclusion v (Finset.map_subset_map.mpr hIJ) (pieceEquiv e v I f) := rfl

end Cylinder.PlaneLaurentPermutation

end
