module

public import Cylinder.RationalPlaneLine
public import Cylinder.FrobeniusPolar
public import Cylinder.PlanePointModel

/-! Actual base-field projective points, with representatives fixed by Frobenius. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.RationalPlanePointModel

open Cylinder.RationalPlaneLine Cylinder.ProjectiveFieldEmbedding

variable {K L : Type*} [Field K] [Field L]

def representatives (f : K →+* L) (D : Finset (PlanePoint K)) : D → Fin 3 → L :=
  fun P j => f (P.val.rep j)

theorem representatives_nonzero (f : K →+* L) (D : Finset (PlanePoint K)) :
    ∀ P : D, representatives f D P ≠ 0 := by
  intro P hz
  apply P.val.rep_nonzero
  funext j
  have h : f (P.val.rep j) = 0 := congrFun hz j
  apply f.injective
  change f (P.val.rep j) = f (0 : K)
  rw [map_zero]
  exact h

theorem representatives_distinct (f : K →+* L) (D : Finset (PlanePoint K)) :
    Cylinder.HilbertEvaluation.ProjectivelyDistinct (representatives f D) := by
  intro P Q hPQ a ha
  have hproj := (Projectivization.mk_eq_mk_iff' L (representatives f D Q)
    (representatives f D P) (representatives_nonzero f D Q)
    (representatives_nonzero f D P)).mpr ⟨a, ha.symm⟩
  have hQ : pointMap f Q.val = Projectivization.mk L (representatives f D Q)
      (representatives_nonzero f D Q) := by
    calc
      _ = pointMap f (Projectivization.mk K Q.val.rep Q.val.rep_nonzero) :=
        (congrArg (pointMap f) (Projectivization.mk_rep Q.val)).symm
      _ = _ := pointMap_mk f Q.val.rep Q.val.rep_nonzero
  have hP : pointMap f P.val = Projectivization.mk L (representatives f D P)
      (representatives_nonzero f D P) := by
    calc
      _ = pointMap f (Projectivization.mk K P.val.rep P.val.rep_nonzero) :=
        (congrArg (pointMap f) (Projectivization.mk_rep P.val)).symm
      _ = _ := pointMap_mk f P.val.rep P.val.rep_nonzero
  have hmap : pointMap f Q.val = pointMap f P.val := hQ.trans (hproj.trans hP.symm)
  exact hPQ (Subtype.ext (pointMap_injective f hmap).symm)

theorem representatives_frobeniusFixed (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* L) (D : Finset (PlanePoint (ZMod p))) :
    ∀ P : D, Cylinder.FrobeniusPolar.FrobeniusFixed p (representatives f D P) :=
  fun P => Cylinder.FrobeniusPolar.frobeniusFixed_primeField_image p f P.val.rep

end Cylinder.RationalPlanePointModel

end
