module

public import Cylinder.PairLaurentTorusModel
public import Cylinder.GlobalTwistChartTorusModel
public import Cylinder.PlaneLaurentTorusCocycles
public import Cylinder.GlobalTwistPairInfSections
public import Cylinder.PairTorusAdditiveCompatibility
public import Cylinder.SheafCechOneDescent
public import Cylinder.SheafCohomologyScalarAction

/-! Every actual one-cocycle of the global twisting sheaf on the
three standard coordinate charts is an actual coboundary. The proof
preserves literal fraction values and uses the homogeneous Laurent
coefficient primitive only after mapping the actual restrictions. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Cylinder.GlobalTwistCoordinateCech

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Cylinder.CoordinateChartPermutation Cylinder.CoordinateChartLaurent
open Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistPairSections Cylinder.GlobalTwistPairInfSections
open Cylinder.GlobalTwistChartLaurent Cylinder.GlobalTwistChartTorusModel
open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentCommonTorus
open Cylinder.SheafCohomologyScalarAction Cylinder.GlobalTwistKSheaf
open Cylinder.SheafCechOneDescent Cylinder.GlobalTwistTorusCompatibility

variable (K : Type*) [Field K] [Infinite K]

theorem coordinate_cech_one_exact (v : ℤ) :
    CechOneExact (X := (GlobalTwistLocalFractions.plane K).toTopCat)
      ((forgetModules (J := _root_.Opens.grothendieckTopology
        (GlobalTwistLocalFractions.plane K).toTopCat) (K := K)).obj (twistK K v))
      (coordinateOpen K) := by
  intro z hz
  let zp (i j : Index) : Γ(twist K v, pairOpen K i j) := infToPair K v i j (z i j)
  let t (i j : Index) := PairTorusEvaluation.torusValue K i j v (zp i j)
  have hcycle (i j k : Index) : t i k - t j k = t i j := by
    let U := coordinateOpen K i ⊓ coordinateOpen K j ⊓ coordinateOpen K k
    have hU : ActualTorusGenericPoint.genericPoint K ∈ U :=
      ⟨⟨ActualTorusGenericPoint.genericPoint_mem_coordinateOpen K i,
        ActualTorusGenericPoint.genericPoint_mem_coordinateOpen K j⟩,
        ActualTorusGenericPoint.genericPoint_mem_coordinateOpen K k⟩
    have h₁ : U ≤ pairOpen K i k := by
      rw [pairOpen_eq]
      exact inf_le_inf inf_le_left le_rfl
    have h₂ : U ≤ pairOpen K j k := by
      rw [pairOpen_eq]
      exact inf_le_inf inf_le_right le_rfl
    have h₃ : U ≤ pairOpen K i j := by
      rw [pairOpen_eq]
      exact inf_le_left
    apply PairTorusAdditiveCompatibility.restriction_sub_eq K i k j k i j v U hU h₁ h₂ h₃
      (zp i k) (zp j k) (zp i j)
    apply Subtype.ext
    funext q
    exact congrArg (fun x : Γ(twist K v, U) => x.val q) (hz i j k)
  have n₀ : coordinateNumber none = 0 := by simp [coordinateNumber]
  have n₁ : coordinateNumber (some 0) = 1 := by simp [coordinateNumber]
  have n₂ : coordinateNumber (some 1) = 2 := by simp [coordinateNumber]
  obtain ⟨r₀₁, hr₀₁⟩ := PairLaurentTorusModel.exists_piece_of_section K v none (some 0) (zp none (some 0))
  obtain ⟨r₀₂, hr₀₂⟩ := PairLaurentTorusModel.exists_piece_of_section K v none (some 1) (zp none (some 1))
  obtain ⟨r₁₂, hr₁₂⟩ := PairLaurentTorusModel.exists_piece_of_section K v (some 0) (some 1) (zp (some 0) (some 1))
  let f₀₁ : piece (K := K) v {0, 1} := ⟨r₀₁.val, by simpa only [n₀, n₁] using r₀₁.property⟩
  let f₀₂ : piece (K := K) v {0, 2} := ⟨r₀₂.val, by simpa only [n₀, n₂] using r₀₂.property⟩
  let f₁₂ : piece (K := K) v {1, 2} := ⟨r₁₂.val, by simpa only [n₁, n₂] using r₁₂.property⟩
  have hf₀₁ : commonPieceMap K v {0, 1} f₀₁ = t none (some 0) :=
    ((commonPieceMap_eq_iff K v f₀₁ r₀₁).mpr rfl).trans hr₀₁
  have hf₀₂ : commonPieceMap K v {0, 2} f₀₂ = t none (some 1) :=
    ((commonPieceMap_eq_iff K v f₀₂ r₀₂).mpr rfl).trans hr₀₂
  have hf₁₂ : commonPieceMap K v {1, 2} f₁₂ = t (some 0) (some 1) :=
    ((commonPieceMap_eq_iff K v f₁₂ r₁₂).mpr rfl).trans hr₁₂
  have hc : commonPieceMap K v {0, 2} f₀₂ - commonPieceMap K v {1, 2} f₁₂ =
      commonPieceMap K v {0, 1} f₀₁ := by
    rw [hf₀₂, hf₁₂, hf₀₁]
    exact hcycle none (some 0) (some 1)
  obtain ⟨s₀, s₁, s₂, hs₀₁, hs₀₂, hs₁₂⟩ :=
    PlaneLaurentTorusCocycles.exists_torus_primitive K v f₀₁ f₀₂ f₁₂ hc
  let c₀ : piece (K := K) v {coordinateNumber none} :=
    ⟨s₀.val, by simpa only [n₀] using s₀.property⟩
  let c₁ : piece (K := K) v {coordinateNumber (some 0)} :=
    ⟨s₁.val, by simpa only [n₁] using s₁.property⟩
  let c₂ : piece (K := K) v {coordinateNumber (some 1)} :=
    ⟨s₂.val, by simpa only [n₂] using s₂.property⟩
  let b : ∀ i : Index, Γ(twist K v, coordinateOpen K i) := fun i =>
    Option.rec (motive := fun i => Γ(twist K v, coordinateOpen K i))
      ((chartSectionsEquiv K v none).symm c₀)
      (fun j => Fin.cases (motive := fun j : Fin 2 => Γ(twist K v, coordinateOpen K (some j)))
        ((chartSectionsEquiv K v (some 0)).symm c₁)
        (fun k => Fin.cases
          (motive := fun k : Fin 1 => Γ(twist K v, coordinateOpen K (some k.succ)))
          ((chartSectionsEquiv K v (some 1)).symm c₂) (fun k => Fin.elim0 k) k) j) i
  have bv₀ : torusValue K none v (b none) = commonPieceMap K v {0} s₀ :=
    (chartSectionsEquiv_symm_torusValue K v none c₀).trans
      ((commonPieceMap_eq_iff K v c₀ s₀).mpr rfl)
  have bv₁ : torusValue K (some 0) v (b (some 0)) = commonPieceMap K v {1} s₁ :=
    (chartSectionsEquiv_symm_torusValue K v (some 0) c₁).trans
      ((commonPieceMap_eq_iff K v c₁ s₁).mpr rfl)
  have bv₂ : torusValue K (some 1) v (b (some 1)) = commonPieceMap K v {2} s₂ :=
    (chartSectionsEquiv_symm_torusValue K v (some 1) c₂).trans
      ((commonPieceMap_eq_iff K v c₂ s₂).mpr rfl)
  have hd (i : Index) : t i i = 0 := by
    have h := hcycle i i i
    simpa only [sub_self] using h.symm
  have hr (i j : Index) : t j i = -t i j := by
    have h := hcycle i j i
    rw [hd, zero_sub] at h
    exact (neg_neg (t j i)).symm.trans (congrArg Neg.neg h)
  have hb (i j : Index) : torusValue K i v (b i) - torusValue K j v (b j) = t i j := by
    cases i with
    | none =>
      cases j with
      | none => simp only [sub_self, hd]
      | some j =>
        fin_cases j
        · change torusValue K none v (b none) - torusValue K (some 0) v (b (some 0)) =
            t none (some 0)
          rw [bv₀, bv₁]
          exact hs₀₁.trans hf₀₁
        · change torusValue K none v (b none) - torusValue K (some 1) v (b (some 1)) =
            t none (some 1)
          rw [bv₀, bv₂]
          exact hs₀₂.trans hf₀₂
    | some i =>
      fin_cases i
      · cases j with
        | none =>
          change torusValue K (some 0) v (b (some 0)) - torusValue K none v (b none) =
            t (some 0) none
          rw [bv₁, bv₀, hr none (some 0), ← hf₀₁, ← hs₀₁]
          abel
        | some j =>
          fin_cases j
          · change torusValue K (some 0) v (b (some 0)) - torusValue K (some 0) v (b (some 0)) =
              t (some 0) (some 0)
            simp only [sub_self, hd]
          · change torusValue K (some 0) v (b (some 0)) - torusValue K (some 1) v (b (some 1)) =
              t (some 0) (some 1)
            rw [bv₁, bv₂]
            exact hs₁₂.trans hf₁₂
      · cases j with
        | none =>
          change torusValue K (some 1) v (b (some 1)) - torusValue K none v (b none) =
            t (some 1) none
          rw [bv₂, bv₀, hr none (some 1), ← hf₀₂, ← hs₀₂]
          abel
        | some j =>
          fin_cases j
          · change torusValue K (some 1) v (b (some 1)) - torusValue K (some 0) v (b (some 0)) =
              t (some 1) (some 0)
            rw [bv₂, bv₁, hr (some 0) (some 1), ← hf₁₂, ← hs₁₂]
            abel
          · change torusValue K (some 1) v (b (some 1)) - torusValue K (some 1) v (b (some 1)) =
              t (some 1) (some 1)
            simp only [sub_self, hd]
  refine ⟨b, fun i j => ?_⟩
  have hsub (s t : Γ(twist K v, pairOpen K i j)) :
      PairTorusEvaluation.torusValue K i j v (s - t) =
        PairTorusEvaluation.torusValue K i j v s - PairTorusEvaluation.torusValue K i j v t := by
    apply (eq_sub_iff_add_eq).mpr
    calc
      _ = PairTorusEvaluation.torusValue K i j v ((s - t) + t) :=
        ((PairTorusEvaluation.torusValue K i j v).map_add _ _).symm
      _ = _ := congrArg (PairTorusEvaluation.torusValue K i j v) (sub_add_cancel s t)
  have hp : (twist K v).presheaf.map (homOfLE (pairOpen_le_first K i j)).op (b i) -
      (twist K v).presheaf.map
        (homOfLE ((le_of_eq (pairOpen_eq K i j)).trans inf_le_right)).op (b j) = zp i j := by
    apply PairTorusCompatibility.torusValue_injective K i j v
    rw [hsub, PairTorusCompatibility.chart_restriction_value,
      PairTorusCompatibility.second_chart_restriction_value]
    exact hb i j
  apply Subtype.ext
  funext q
  let q' : pairOpen K i j := ⟨q.val, by rw [pairOpen_eq]; exact q.property⟩
  exact congrArg (fun s : Γ(twist K v, pairOpen K i j) => s.val q') hp

end Cylinder.GlobalTwistCoordinateCech

end
