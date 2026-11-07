module
public import Cylinder.ProjectiveProjectionFibres
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace Cylinder.ProjectionChart
open ProjectiveProjection EvaluationProjection
variable {K σ : Type*} [Field K]

/-- An arbitrary coordinate system centred at the given projective point.
The representative of the centre may have any nonzero last coordinate. -/
structure Chart (centre : Point K σ) where
  g : Space K σ ≃ₗ[K] Space K σ
  c : Kˣ
  map_centre : g centre.rep = (c : K) • centreAxis K σ

def lift : (σ → K) →ₗ[K] Space K σ where
  toFun a := rayPoint a 0
  map_add' _ _ := by ext o; cases o <;> simp [rayPoint]
  map_smul' _ _ := by ext o; cases o <;> simp [rayPoint]

def tail : Space K σ →ₗ[K] (σ → K) where
  toFun x s := x (some s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem tail_lift (a : σ → K) : tail (lift a) = a := rfl
@[simp] theorem tail_axis : tail (centreAxis K σ) = 0 := by ext s; simp [tail, centreAxis]
theorem decompose (x : Space K σ) : x = lift (tail x) + x none • centreAxis K σ := by
  ext o; cases o <;> simp [lift, tail, rayPoint, centreAxis]

def Chart.transition {centre : Point K σ} (C : Chart centre) :=
  (coordinateChange K σ centre).symm.trans C.g

@[simp] theorem Chart.transition_axis {centre : Point K σ} (C : Chart centre) :
    C.transition (centreAxis K σ) = (C.c : K) • centreAxis K σ := by
  change C.g ((coordinateChange K σ centre).symm (centreAxis K σ)) = _
  rw [← coordinateChange_centre K σ centre, LinearEquiv.symm_apply_apply]
  simpa only [coordinateChange_centre] using C.map_centre

def Chart.directionMap {centre : Point K σ} (C : Chart centre) : (σ → K) →ₗ[K] (σ → K) :=
  tail.comp (C.transition.toLinearMap.comp lift)

theorem Chart.tail_transition {centre : Point K σ} (C : Chart centre) (x : Space K σ) :
    tail (C.transition x) = C.directionMap (tail x) := by
  conv_lhs => rw [decompose x]
  simp [Chart.directionMap, map_add, map_smul]

theorem Chart.directionMap_injective {centre : Point K σ} (C : Chart centre) :
    Function.Injective C.directionMap := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hx : C.transition (lift a) =
      (C.transition (lift a) none / (C.c : K)) • C.transition (centreAxis K σ) := by
    rw [C.transition_axis, smul_smul, div_mul_cancel₀ _ C.c.ne_zero]
    have htail : tail (C.transition (lift a)) = 0 := ha
    simpa [htail] using decompose (C.transition (lift a))
  have hy : lift a = (C.transition (lift a) none / (C.c : K)) • centreAxis K σ :=
    C.transition.injective (by simpa only [map_smul] using hx)
  have hz := congrArg tail hy
  simpa using hz

def Chart.directionEquiv [Finite σ] {centre : Point K σ} (C : Chart centre) :
    (σ → K) ≃ₗ[K] (σ → K) :=
  LinearEquiv.ofBijective C.directionMap
    ⟨C.directionMap_injective,
      (LinearMap.injective_iff_surjective).mp C.directionMap_injective⟩

def Chart.timeShift {centre : Point K σ} (C : Chart centre) : (σ → K) →ₗ[K] K :=
  (LinearMap.proj none).comp (C.transition.toLinearMap.comp lift)

theorem Chart.transition_rayPoint [Finite σ] {centre : Point K σ} (C : Chart centre)
    (a : σ → K) (t : K) :
    C.transition (rayPoint a t) =
      rayPoint (C.directionEquiv a) (C.timeShift a + (C.c : K) * t) := by
  have h : rayPoint a t = lift a + t • centreAxis K σ := by
    ext o; cases o <;> simp [lift, rayPoint, centreAxis]
  rw [h, map_add, map_smul, C.transition_axis]
  ext o
  cases o with
  | none => simp [rayPoint, centreAxis, Chart.timeShift, mul_comm]
  | some s => simp [rayPoint, centreAxis, Chart.directionEquiv, Chart.directionMap, tail]

/-- The direction in arbitrary coordinates is the constructed linear image
of the canonical direction. -/
theorem Chart.directionVector_eq [Finite σ] {centre : Point K σ} (C : Chart centre)
    (P : Point K σ) :
    tail (C.g P.rep) = C.directionEquiv (directionVector K σ centre P) := by
  change tail (C.g P.rep) = C.directionMap (tail (coordinateChange K σ centre P.rep))
  have h := C.tail_transition (coordinateChange K σ centre P.rep)
  simpa only [Chart.transition, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h

end Cylinder.ProjectionChart
end



