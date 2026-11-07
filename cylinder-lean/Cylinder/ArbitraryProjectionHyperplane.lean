module
public import Cylinder.ProjectionChart
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace Cylinder.ArbitraryProjectionHyperplane
open ProjectiveProjection ProjectionChart ProjectiveIncidence
variable {K σ : Type*} [Field K]

/-- Vector projection onto the given hyperplane, from the given centre. -/
def retract (centre : Point K σ) (ell : Module.Dual K (Space K σ)) :
    Space K σ →ₗ[K] Space K σ where
  toFun x := x - (ell x / ell centre.rep) • centre.rep
  map_add' x y := by simp [map_add, add_div, add_smul]; abel
  map_smul' a x := by simp [map_smul, smul_sub, smul_smul, mul_div_assoc]

@[simp] theorem retract_centre (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) : retract centre ell centre.rep = 0 := by
  simp [retract, hb]

theorem retract_mem (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) (x : Space K σ) : retract centre ell x ∈ LinearMap.ker ell := by
  change ell (x - (ell x / ell centre.rep) • centre.rep) = 0
  simp [map_sub, map_smul, div_mul_cancel₀ _ hb]

theorem retract_of_mem (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (x : Space K σ) (hx : x ∈ LinearMap.ker ell) : retract centre ell x = x := by
  change ell x = 0 at hx
  simp [retract, hx]

theorem retract_ne_zero (centre P : Point K σ) (ell : Module.Dual K (Space K σ))
    (hP : P ≠ centre) : retract centre ell P.rep ≠ 0 := by
  intro hz
  have he : (ell P.rep / ell centre.rep) • centre.rep = P.rep :=
    (sub_eq_zero.mp hz).symm
  apply hP
  calc
    P = Projectivization.mk K P.rep P.rep_nonzero := (Projectivization.mk_rep P).symm
    _ = Projectivization.mk K centre.rep centre.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨_, he⟩
    _ = centre := Projectivization.mk_rep centre

def projectPoint (centre P : Point K σ) (ell : Module.Dual K (Space K σ))
    (hP : P ≠ centre) : Point K σ :=
  Projectivization.mk K (retract centre ell P.rep) (retract_ne_zero centre P ell hP)

/-- The geometric projective line through the original two points. -/
def joiningLine (centre P : Point K σ) : Submodule K (Space K σ) :=
  Submodule.span K {centre.rep, P.rep}

theorem joiningLine_finrank (centre P : Point K σ) (hP : P ≠ centre) :
    Module.finrank K (joiningLine centre P) = 2 := by
  let f : Fin 2 → Space K σ := ![centre.rep, P.rep]
  have hf : LinearIndependent K f :=
    Projectivization.linearIndependent_pair_iff_ne.mpr (Ne.symm hP)
  have hr : Set.range f = {centre.rep, P.rep} := by
    ext w
    simp [f, or_comm]
  have he : Submodule.span K (Set.range f) = joiningLine centre P := by
    rw [hr]
    rfl
  calc
    Module.finrank K (joiningLine centre P) =
        Module.finrank K (Submodule.span K (Set.range f)) :=
      (LinearEquiv.ofEq _ _ he).finrank_eq.symm
    _ = 2 := by simpa using finrank_span_eq_card hf

theorem projected_mem_line (centre P : Point K σ) (ell : Module.Dual K (Space K σ))
    (hP : P ≠ centre) : (projectPoint centre P ell hP).submodule ≤ joiningLine centre P := by
  rw [projectPoint, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
  apply Submodule.sub_mem
  · exact Submodule.subset_span (by simp)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem projected_mem_hyperplane (centre P : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) (hP : P ≠ centre) :
    (projectPoint centre P ell hP).submodule ≤ LinearMap.ker ell := by
  rw [projectPoint, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
  exact retract_mem centre ell hb P.rep

/-- The constructed projection is exactly the unique intersection of the
original projective line with the prescribed hyperplane. -/
theorem intersection_unique (centre P : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) (hP : P ≠ centre) (Q : Point K σ) :
    Q.submodule ≤ joiningLine centre P ∧ Q.submodule ≤ LinearMap.ker ell ↔
      Q = projectPoint centre P ell hP := by
  constructor
  · rintro ⟨hl, hH⟩
    have hq := (submodule_le_iff_rep_mem Q _).mp hl
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hq
    have hr := congrArg (retract centre ell) hab
    rw [map_add, map_smul, map_smul, retract_centre centre ell hb, smul_zero, zero_add,
      retract_of_mem centre ell Q.rep ((submodule_le_iff_rep_mem Q _).mp hH)] at hr
    calc
      Q = Projectivization.mk K Q.rep Q.rep_nonzero := (Projectivization.mk_rep Q).symm
      _ = projectPoint centre P ell hP :=
        (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, hr⟩
  · rintro rfl
    exact ⟨projected_mem_line centre P ell hP, projected_mem_hyperplane centre P ell hb hP⟩

variable [Finite σ]

/-- Coordinates adapted simultaneously to any given centre and hyperplane. -/
def coordinateMap (centre : Point K σ) (ell : Module.Dual K (Space K σ)) :
    Space K σ →ₗ[K] Space K σ where
  toFun x := EvaluationProjection.rayPoint
    (tail (coordinateChange K σ centre x)) (ell x / ell centre.rep)
  map_add' x y := by ext o; cases o <;> simp [EvaluationProjection.rayPoint, map_add, add_div, tail]
  map_smul' a x := by ext o; cases o <;> simp [EvaluationProjection.rayPoint, map_smul, mul_div_assoc, tail]

theorem coordinateMap_injective (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) : Function.Injective (coordinateMap centre ell) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have ht : tail (coordinateChange K σ centre x) = 0 := by
    funext s
    exact congrFun hx (some s)
  have hn : ell x = 0 := by
    have h := congrFun hx none
    change ell x / ell centre.rep = 0 at h
    exact (div_eq_zero_iff).mp h |>.resolve_right hb
  have hd : coordinateChange K σ centre x =
      (coordinateChange K σ centre x none) • centreAxis K σ := by
    simpa [ht] using decompose (coordinateChange K σ centre x)
  have he : x = (coordinateChange K σ centre x none) • centre.rep := by
    apply (coordinateChange K σ centre).injective
    simpa [map_smul, coordinateChange_centre] using hd
  have hz : coordinateChange K σ centre x none = 0 := by
    have h := congrArg ell he
    rw [hn, map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hb
  simpa [hz] using he

def coordinates (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) : Space K σ ≃ₗ[K] Space K σ :=
  LinearEquiv.ofBijective (coordinateMap centre ell)
    ⟨coordinateMap_injective centre ell hb,
      LinearMap.injective_iff_surjective.mp (coordinateMap_injective centre ell hb)⟩

def chart (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) : Chart centre where
  g := coordinates centre ell hb
  c := 1
  map_centre := by
    ext o
    cases o <;> simp [coordinates, coordinateMap, EvaluationProjection.rayPoint,
      coordinateChange_centre, tail, centreAxis, hb]

@[simp] theorem coordinates_none (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) (x : Space K σ) :
    coordinates centre ell hb x none = ell x / ell centre.rep := rfl

theorem coordinates_hyperplane (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) (x : Space K σ) :
    x ∈ LinearMap.ker ell ↔ coordinates centre ell hb x none = 0 := by
  simp [coordinates_none, LinearMap.mem_ker, hb]

def hyperplaneEquiv (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) : LinearMap.ker ell ≃ₗ[K] (σ → K) where
  toFun x := tail (coordinates centre ell hb x.val)
  invFun a := ⟨(coordinates centre ell hb).symm (lift a), by
    rw [coordinates_hyperplane centre ell hb, LinearEquiv.apply_symm_apply]
    rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply (coordinates centre ell hb).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := decompose (coordinates centre ell hb x.val)
    have hz := (coordinates_hyperplane centre ell hb x.val).mp x.property
    simpa [hz] using h.symm
  right_inv a := by simp
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem hyperplaneEquiv_projection (centre : Point K σ) (ell : Module.Dual K (Space K σ))
    (hb : ell centre.rep ≠ 0) (x : Space K σ) :
    hyperplaneEquiv centre ell hb ⟨retract centre ell x, retract_mem centre ell hb x⟩ =
      tail ((chart centre ell hb).g x) := by
  change tail (coordinates centre ell hb (x - (ell x / ell centre.rep) • centre.rep)) = _
  rw [map_sub, map_smul]
  have hc := (chart centre ell hb).map_centre
  change coordinates centre ell hb centre.rep = (1 : Kˣ) • centreAxis K σ at hc
  simp [hc, chart]

/-- Every hyperplane missing the centre has a defining nonzero linear
functional; no equation or coordinate choice is required as extra input. -/
theorem exists_equation [Fintype σ] (centre : Point K σ)
    (H : Submodule K (Space K σ))
    (hH : Module.finrank K H + 1 = Fintype.card (Option σ))
    (hb : centre.rep ∉ H) :
    ∃ ell : Module.Dual K (Space K σ), ell centre.rep ≠ 0 ∧ LinearMap.ker ell = H := by
  obtain ⟨ell, hellb, hmap⟩ := H.exists_dual_map_eq_bot_of_notMem hb inferInstance
  refine ⟨ell, hellb, ?_⟩
  have hell : ell ≠ 0 := fun hz => hellb (by rw [hz]; rfl)
  have hle : H ≤ LinearMap.ker ell := by
    intro x hx
    have hm : ell x ∈ H.map ell := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap, Submodule.mem_bot] at hm
    exact hm
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hell
  have hn : Module.finrank K (Space K σ) = Fintype.card (Option σ) := by simp [Space]
  omega


/-- Adapted coordinates exist for every given hyperplane missing the centre. -/
theorem exists_hyperplane_chart [Fintype σ] (centre : Point K σ)
    (H : Submodule K (Space K σ))
    (hH : Module.finrank K H + 1 = Fintype.card (Option σ))
    (hb : centre.rep ∉ H) :
    ∃ C : Chart centre, ∀ x, x ∈ H ↔ C.g x none = 0 := by
  obtain ⟨ell, hell, heq⟩ := exists_equation centre H hH hb
  refine ⟨chart centre ell hell, ?_⟩
  intro x
  rw [← heq]
  exact coordinates_hyperplane centre ell hell x

#print axioms joiningLine_finrank
#print axioms intersection_unique
#print axioms hyperplaneEquiv_projection
#print axioms exists_equation
#print axioms exists_hyperplane_chart

end Cylinder.ArbitraryProjectionHyperplane
end

