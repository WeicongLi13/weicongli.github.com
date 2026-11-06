module

public import Cylinder.ProjectiveSecantCounting

/-! A genuine secant of a projective arc recovers its entire unordered
white pair. This is actual line incidence and the arc bound. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ArcSecantRecovery

open Cylinder.RationalPlaneLine Cylinder.ProjectiveSecantCounting

variable {K : Type*} [Field K]

theorem arc_line_slice_eq_pair (W : Finset (PlanePoint K)) (hW : LineCap W 2)
    (L : PlaneLine K) (P Q : PlanePoint K) (hP : P ∈ W) (hQ : Q ∈ W) (hPQ : P ≠ Q)
    (hLP : Incident L P) (hLQ : Incident L Q) : lineSlice W L = {P, Q} := by
  have hsub : ({P, Q} : Finset (PlanePoint K)) ⊆ lineSlice W L := by
    intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact Finset.mem_filter.mpr ⟨hP, hLP⟩
    have hRQ := Finset.mem_singleton.mp hR
    subst R
    exact Finset.mem_filter.mpr ⟨hQ, hLQ⟩
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  have heq : lineSlice W L = W.filter (fun P => Cylinder.PlaneCrossProduct.dot L.rep P.rep = 0) := by
    ext P
    simp only [lineSlice, Finset.mem_filter]
    rfl
  rw [heq, Finset.card_pair hPQ]
  exact hW L.rep L.rep_nonzero

theorem arc_pairs_on_line_equal (W : Finset (PlanePoint K)) (hW : LineCap W 2)
    (L : PlaneLine K) (P Q U V : PlanePoint K)
    (hP : P ∈ W) (hQ : Q ∈ W) (hU : U ∈ W) (hV : V ∈ W)
    (hPQ : P ≠ Q) (hUV : U ≠ V)
    (hLP : Incident L P) (hLQ : Incident L Q) (hLU : Incident L U) (hLV : Incident L V) :
    ({P, Q} : Finset (PlanePoint K)) = {U, V} :=
  (arc_line_slice_eq_pair W hW L P Q hP hQ hPQ hLP hLQ).symm.trans
    (arc_line_slice_eq_pair W hW L U V hU hV hUV hLU hLV)

end Cylinder.ArcSecantRecovery

end
