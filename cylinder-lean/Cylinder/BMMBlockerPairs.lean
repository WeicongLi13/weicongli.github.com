module

public import Cylinder.BMMArcGeometry

/-! The actual black point on a white secant is unique and symmetric in
its endpoints. Different secants through one white point have different
black points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMBlockerPairs

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry

variable {K : Type*} [Field K]

set_option maxHeartbeats 1000000

def secantBlocker (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P Q : W) (hPQ : P ≠ Q) : B :=
  blockerMap W B hblock P.val P.property
    ⟨Q.val, Finset.mem_erase.mpr ⟨fun h => hPQ (Subtype.ext h.symm), Q.property⟩⟩

theorem secantBlocker_collinear (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P Q : W) (hPQ : P ≠ Q) :
    Collinear P.val Q.val (secantBlocker W B hW hdisj hblock hcard P Q hPQ).val := by
  let Q' : W.erase P.val :=
    ⟨Q.val, Finset.mem_erase.mpr ⟨fun h => hPQ (Subtype.ext h.symm), Q.property⟩⟩
  change Collinear P.val Q.val (blockerMap W B hblock P.val P.property Q').val
  exact blockerMap_collinear W B hblock P.val P.property Q'

theorem secantBlocker_unique (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P Q : W) (hPQ : P ≠ Q) (R : B) (hR : Collinear P.val Q.val R.val) :
    secantBlocker W B hW hdisj hblock hcard P Q hPQ = R := by
  obtain ⟨Q', hQR⟩ := (blockerMap_bijective W B hW hdisj hblock hcard P.val P.property).2 R
  have hPR : P.val ≠ R.val := by
    intro h
    exact Finset.disjoint_left.mp hdisj P.property (h ▸ R.property)
  have hQeq : Q.val = Q'.val := arc_unique_other W hW P.val Q.val Q'.val R.val
    P.property Q.property (Finset.mem_erase.mp Q'.property).2
    (fun h => hPQ (Subtype.ext h)) (Finset.mem_erase.mp Q'.property).1.symm hPR hR
    (by simpa only [hQR] using blockerMap_collinear W B hblock P.val P.property Q')
  change blockerMap W B hblock P.val P.property _ = R
  rw [← hQR]
  apply congrArg (blockerMap W B hblock P.val P.property)
  exact Subtype.ext hQeq

theorem secantBlocker_symm (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P Q : W) (hPQ : P ≠ Q) :
    secantBlocker W B hW hdisj hblock hcard P Q hPQ =
      secantBlocker W B hW hdisj hblock hcard Q P hPQ.symm :=
  secantBlocker_unique W B hW hdisj hblock hcard P Q hPQ _
    (collinear_swap _ _ _ (secantBlocker_collinear W B hW hdisj hblock hcard Q P hPQ.symm))

theorem secantBlocker_injective_at (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P Q R : W) (hPQ : P ≠ Q) (hPR : P ≠ R)
    (h : secantBlocker W B hW hdisj hblock hcard P Q hPQ =
      secantBlocker W B hW hdisj hblock hcard P R hPR) : Q = R := by
  have hQR := blockerMap_injective W B hW hdisj hblock P.val P.property h
  exact Subtype.ext (congrArg (fun X : W.erase P.val => X.val) hQR)

theorem secantBlocker_ne_at (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P Q R : W) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    secantBlocker W B hW hdisj hblock hcard P Q hPQ ≠
      secantBlocker W B hW hdisj hblock hcard P R hPR := by
  intro h
  exact hQR (secantBlocker_injective_at W B hW hdisj hblock hcard P Q R hPQ hPR h)

end Cylinder.BMMBlockerPairs

end
