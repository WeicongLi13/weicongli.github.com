module

public import Cylinder.ArcCoordinateRecovery

/-! A true linear change preserving the distinguished black point and
the two unordered axial black pairs preserves or exchanges the two white
diagonal lines. The white pair family is independent of this frame choice. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.FiveBlackFrameRecovery

open Cylinder.RationalPlaneLine Cylinder.BMMLinearCoordinates

variable {K : Type*} [Field K]

def vertex : Fin 3 → K := ![0, 0, 1]

def axisVector (i : Fin 2) : Fin 3 → K := if i = 0 then ![1, 0, 0] else ![0, 1, 0]

theorem axisVector_nonzero (i : Fin 2) : axisVector (K := K) i ≠ 0 := by
  intro hz
  have hh := congrFun hz i.castSucc
  fin_cases i <;> simp [axisVector] at hh

theorem axisShift_nonzero (i : Fin 2) : axisVector (K := K) i + vertex ≠ 0 := by
  intro hz
  have hh := congrFun hz i.castSucc
  fin_cases i <;> simp [axisVector, vertex, Pi.add_apply] at hh

def axisPoint (i : Fin 2) : PlanePoint K :=
  Projectivization.mk K (axisVector i) (axisVector_nonzero i)

def axisShiftPoint (i : Fin 2) : PlanePoint K :=
  Projectivization.mk K (axisVector i + vertex) (axisShift_nonzero i)

theorem axis_points_distinct (i : Fin 2) : axisPoint (K := K) i ≠ axisShiftPoint i := by
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ (axisVector_nonzero i) (axisShift_nonzero i)).mp h
  have hlast : a = 0 := by
    have hh := congrFun ha (2 : Fin 3)
    fin_cases i <;> simpa [axisVector, vertex, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  rw [hlast, zero_smul] at ha
  exact axisVector_nonzero i ha.symm

theorem pair_image_permutation {I : Type*} (f : I → I) (hf : Function.Injective f)
    (a b : I) (hab : a ≠ b) (himage : ({a, b} : Finset I).image f = {a, b}) :
    (f a = a ∧ f b = b) ∨ (f a = b ∧ f b = a) := by
  have hfa : f a = a ∨ f a = b := by
    have hmem : f a ∈ ({a, b} : Finset I).image f := Finset.mem_image.mpr ⟨a, by simp, rfl⟩
    rw [himage] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hfb : f b = a ∨ f b = b := by
    have hmem : f b ∈ ({a, b} : Finset I).image f := Finset.mem_image.mpr ⟨b, by simp, rfl⟩
    rw [himage] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hfa with hfa | hfa
  · rcases hfb with hfb | hfb
    · exact False.elim (hab (hf (hfa.trans hfb.symm)))
    · exact Or.inl ⟨hfa, hfb⟩
  · rcases hfb with hfb | hfb
    · exact Or.inr ⟨hfa, hfb⟩
    · exact False.elim (hab (hf (hfa.trans hfb.symm)))

theorem point_image_scalar (q : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (v w : Fin 3 → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : linearPointMap q (Projectivization.mk K v hv) = Projectivization.mk K w hw) :
    ∃ a : K, q v = a • w := by
  rw [linearPointMap_mk] at heq
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp heq
  exact ⟨a, ha.symm⟩

theorem axis_image_eq_or (q : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (hq : q vertex = vertex)
    (i : Fin 2)
    (himage : ({axisPoint i, axisShiftPoint i} : Finset (PlanePoint K)).image (linearPointMap q) =
      {axisPoint i, axisShiftPoint i}) :
    q (axisVector i) = axisVector i ∨ q (axisVector i) = -(axisVector i + vertex) := by
  rcases pair_image_permutation (linearPointMap q) (linearPointMap_injective q)
      (axisPoint i) (axisShiftPoint i) (axis_points_distinct (K := K) i) himage with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · obtain ⟨a, ha⟩ := point_image_scalar q _ _ (axisVector_nonzero (K := K) i) (axisVector_nonzero (K := K) i) h0
    obtain ⟨b, hb⟩ := point_image_scalar q _ _ (axisShift_nonzero (K := K) i) (axisShift_nonzero (K := K) i) h1
    have heq : (a • axisVector i + vertex : Fin 3 → K) = b • (axisVector i + vertex) := by
      calc
        a • axisVector i + vertex = q (axisVector i) + q vertex := by rw [ha, hq]
        _ = q (axisVector i + vertex) := (map_add q _ _).symm
        _ = _ := hb
    have hb1 : b = 1 := by
      have hh := (congrFun heq (2 : Fin 3)).symm
      fin_cases i <;> simpa [axisVector, vertex, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
    have hab : a = b := by
      have hh := congrFun heq i.castSucc
      fin_cases i <;> simpa [axisVector, vertex, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
    exact Or.inl (by rw [ha, hab, hb1, one_smul])
  · obtain ⟨a, ha⟩ := point_image_scalar q _ _ (axisVector_nonzero (K := K) i) (axisShift_nonzero (K := K) i) h0
    obtain ⟨b, hb⟩ := point_image_scalar q _ _ (axisShift_nonzero (K := K) i) (axisVector_nonzero (K := K) i) h1
    have heq : (a • (axisVector i + vertex) + vertex : Fin 3 → K) = b • axisVector i := by
      calc
        a • (axisVector i + vertex) + vertex = q (axisVector i) + q vertex := by rw [ha, hq]
        _ = q (axisVector i + vertex) := (map_add q _ _).symm
        _ = _ := hb
    have ha1 : a = -1 := by
      have hh : a + 1 = 0 := by
        have hh := congrFun heq (2 : Fin 3)
        fin_cases i <;> simpa [axisVector, vertex, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
      exact eq_neg_of_add_eq_zero_left hh
    exact Or.inr (by rw [ha, ha1, neg_one_smul])

theorem vector_expansion (x : Fin 3 → K) :
    x = x 0 • axisVector 0 + x 1 • axisVector 1 + x 2 • vertex := by
  ext i
  fin_cases i <;> simp [axisVector, vertex]

theorem diagonal_equations_preserved_or_swapped (q : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (hq : q vertex = vertex)
    (haxis : ∀ i : Fin 2,
      ({axisPoint i, axisShiftPoint i} : Finset (PlanePoint K)).image (linearPointMap q) =
        {axisPoint i, axisShiftPoint i}) :
    ((∀ x, q x 0 = q x 1 ↔ x 0 = x 1) ∧ (∀ x, q x 0 = -(q x 1) ↔ x 0 = -(x 1))) ∨
      ((∀ x, q x 0 = q x 1 ↔ x 0 = -(x 1)) ∧ (∀ x, q x 0 = -(q x 1) ↔ x 0 = x 1)) := by
  have h0 := axis_image_eq_or q hq 0 (haxis 0)
  have h1 := axis_image_eq_or q hq 1 (haxis 1)
  let a := q (axisVector 0) 0
  let b := q (axisVector 1) 1
  have ha : a = 1 ∨ a = -1 := by
    rcases h0 with h0 | h0
    · exact Or.inl (by change q (axisVector 0) 0 = 1; rw [h0]; rfl)
    · exact Or.inr (by change q (axisVector 0) 0 = -1; rw [h0]; simp [axisVector, vertex])
  have hb : b = 1 ∨ b = -1 := by
    rcases h1 with h1 | h1
    · exact Or.inl (by change q (axisVector 1) 1 = 1; rw [h1]; rfl)
    · exact Or.inr (by change q (axisVector 1) 1 = -1; rw [h1]; simp [axisVector, vertex])
  have h01 : q (axisVector 0) 1 = 0 := by
    rcases h0 with h0 | h0
    · rw [h0]; rfl
    · rw [h0]; simp [axisVector, vertex]
  have h10 : q (axisVector 1) 0 = 0 := by
    rcases h1 with h1 | h1
    · rw [h1]; rfl
    · rw [h1]; simp [axisVector, vertex]
  have hexp (x : Fin 3 → K) : q x = x 0 • q (axisVector 0) + x 1 • q (axisVector 1) + x 2 • vertex := by
    simpa only [map_add, map_smul, hq] using congrArg q (vector_expansion x)
  have hfirst (x : Fin 3 → K) : q x 0 = a * x 0 := by
    have hh := congrFun (hexp x) (0 : Fin 3)
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h10, vertex, mul_comm] using hh
  have hsecond (x : Fin 3 → K) : q x 1 = b * x 1 := by
    have hh := congrFun (hexp x) (1 : Fin 3)
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h01, vertex, mul_comm] using hh
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · left
    constructor <;> intro x <;> simp [hfirst, hsecond, ha, hb]
  · right
    constructor <;> intro x <;> simp [hfirst, hsecond, ha, hb]
  · right
    constructor <;> intro x <;> simp [hfirst, hsecond, ha, hb, neg_eq_iff_eq_neg]
  · left
    constructor <;> intro x <;> simp [hfirst, hsecond, ha, hb, neg_eq_iff_eq_neg]

def positiveSlice (W : Finset (PlanePoint K)) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :
    Finset (PlanePoint K) := W.filter (fun P => g P.rep 0 = g P.rep 1)

def negativeSlice (W : Finset (PlanePoint K)) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :
    Finset (PlanePoint K) := W.filter (fun P => g P.rep 0 = -(g P.rep 1))

theorem diagonal_slice_family_eq (W : Finset (PlanePoint K))
    (g g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (hq : (g.symm.trans g') vertex = vertex)
    (haxis : ∀ i : Fin 2,
      ({axisPoint i, axisShiftPoint i} : Finset (PlanePoint K)).image
        (linearPointMap (g.symm.trans g')) = {axisPoint i, axisShiftPoint i}) :
    ({positiveSlice W g', negativeSlice W g'} : Finset (Finset (PlanePoint K))) =
      {positiveSlice W g, negativeSlice W g} := by
  rcases diagonal_equations_preserved_or_swapped (g.symm.trans g') hq haxis with ⟨hp, hn⟩ | ⟨hp, hn⟩
  · have hpos : positiveSlice W g' = positiveSlice W g := by
      ext P
      have hh := hp (g P.rep)
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hh
      simp only [positiveSlice, Finset.mem_filter, hh]
    have hneg : negativeSlice W g' = negativeSlice W g := by
      ext P
      have hh := hn (g P.rep)
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hh
      simp only [negativeSlice, Finset.mem_filter, hh]
    rw [hpos, hneg]
  · have hpos : positiveSlice W g' = negativeSlice W g := by
      ext P
      have hh := hp (g P.rep)
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hh
      simp only [positiveSlice, negativeSlice, Finset.mem_filter, hh]
    have hneg : negativeSlice W g' = positiveSlice W g := by
      ext P
      have hh := hn (g P.rep)
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hh
      simp only [positiveSlice, negativeSlice, Finset.mem_filter, hh]
    rw [hpos, hneg, Finset.pair_comm]

end Cylinder.FiveBlackFrameRecovery

end
