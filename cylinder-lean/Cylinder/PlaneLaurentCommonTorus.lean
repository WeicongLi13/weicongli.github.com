module

public import Cylinder.CommonTorusFractions

/-! Every actual homogeneous coefficient piece embeds into the same
two-coordinate torus. Equality there is literal equality of the original
homogeneous Laurent coefficient functions, including across different pieces. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentCommonTorus

open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentTripleBasis
open Cylinder.CommonTorusFractions Cylinder.TripleCoordinateLocalization

variable (K : Type*) [Field K]

def fullInclusion (v : ℤ) (I : Finset (Fin 3)) :
    piece (K := K) v I →ₗ[K] piece (K := K) v {0, 1, 2} :=
  Submodule.inclusion (piece_mono v (by
    intro i _
    fin_cases i <;> simp))

def commonPieceMap (v : ℤ) (I : Finset (Fin 3)) :
    piece (K := K) v I →ₗ[K] TorusRing K :=
  (productLaurentEquiv K).symm.toLinearEquiv.toLinearMap.comp
    ((tripleLaurentEquiv v).toLinearMap.comp (fullInclusion K v I))

theorem commonPieceMap_eq_iff (v : ℤ) {I J : Finset (Fin 3)}
    (f : piece (K := K) v I) (g : piece (K := K) v J) :
    commonPieceMap K v I f = commonPieceMap K v J g ↔ f.val = g.val := by
  constructor
  · intro h
    have h' := (productLaurentEquiv K).symm.injective h
    have h'' := (tripleLaurentEquiv v).injective h'
    exact congrArg Subtype.val h''
  · intro h
    have h' : fullInclusion K v I f = fullInclusion K v J g := Subtype.ext h
    exact congrArg (fun z => (productLaurentEquiv K).symm (tripleLaurentEquiv v z)) h'

theorem commonPieceMap_injective (v : ℤ) (I : Finset (Fin 3)) :
    Function.Injective (commonPieceMap K v I) := by
  intro f g h
  exact Subtype.ext ((commonPieceMap_eq_iff K v f g).mp h)

theorem commonPieceMap_inclusion (v : ℤ) {I J : Finset (Fin 3)}
    (hIJ : I ⊆ J) (f : piece (K := K) v I) :
    commonPieceMap K v J (Submodule.inclusion (piece_mono v hIJ) f) =
      commonPieceMap K v I f := rfl

end Cylinder.PlaneLaurentCommonTorus

end
