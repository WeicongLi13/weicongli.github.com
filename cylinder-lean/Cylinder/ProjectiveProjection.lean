module

public import Cylinder.LinearEvaluationTransport
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators

/-!
# Actual projective projection and normalized ray coordinates

The centre is sent to the last coordinate axis by a constructed linear
equivalence. Directions form the finite image in the projectivization
of the remaining coordinates. Each ray is a genuine fibre of this map.
Nonzero units normalize its point representatives to one fixed direction
representative, and their last coordinates are distinct.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectiveProjection

open scoped Classical BigOperators LinearAlgebra.Projectivization

variable (K σ : Type*) [Field K]

abbrev Space := Option σ → K
abbrev Point := Projectivization K (Space K σ)
abbrev Direction := Projectivization K (σ → K)

def centreAxis : Space K σ := Pi.single none 1

theorem centreAxis_ne_zero : centreAxis K σ ≠ 0 := by
  intro h
  have hh := congrFun h none
  simp [centreAxis] at hh

theorem exists_centre_coordinates (centre : Point K σ) :
    ∃ g : Space K σ ≃ₗ[K] Space K σ, g centre.rep = centreAxis K σ := by
  let u : Fin 1 → Space K σ := fun _ => centre.rep
  let w : Fin 1 → Space K σ := fun _ => centreAxis K σ
  have hu : LinearIndependent K u := linearIndependent_unique_iff.mpr centre.rep_nonzero
  have hw : LinearIndependent K w := linearIndependent_unique_iff.mpr (centreAxis_ne_zero K σ)
  let f : Submodule.span K (Set.range u) ≃ₗ[K] Submodule.span K (Set.range w) :=
    hu.linearCombinationEquiv.symm.trans hw.linearCombinationEquiv
  let : FiniteDimensional K (Submodule.span K (Set.range u)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range u)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  simpa [f, u, w] using (hg (hu.linearCombinationEquiv (Finsupp.single (0 : Fin 1) 1))).symm

def coordinateChange (centre : Point K σ) : Space K σ ≃ₗ[K] Space K σ :=
  Classical.choose (exists_centre_coordinates K σ centre)

theorem coordinateChange_centre (centre : Point K σ) :
    coordinateChange K σ centre centre.rep = centreAxis K σ :=
  Classical.choose_spec (exists_centre_coordinates K σ centre)

def directionVector (centre P : Point K σ) : σ → K :=
  fun s => coordinateChange K σ centre P.rep (some s)

theorem directionVector_ne_zero (centre P : Point K σ) (hPC : P ≠ centre) :
    directionVector K σ centre P ≠ 0 := by
  intro hzero
  let g := coordinateChange K σ centre
  let t : K := g P.rep none
  have hscale : t • centre.rep = P.rep := by
    apply g.injective
    rw [map_smul, coordinateChange_centre]
    funext o
    cases o with
    | none => simp [centreAxis, t]
    | some s =>
      have hs := congrFun hzero s
      simpa [directionVector, centreAxis, g] using hs.symm
  apply hPC
  calc
    P = Projectivization.mk K P.rep P.rep_nonzero := (Projectivization.mk_rep P).symm
    _ = Projectivization.mk K centre.rep centre.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' K P.rep centre.rep P.rep_nonzero centre.rep_nonzero).mpr ⟨t, hscale⟩
    _ = centre := Projectivization.mk_rep centre

def projectPoint (centre P : Point K σ) (hPC : P ≠ centre) : Direction K σ :=
  Projectivization.mk K (directionVector K σ centre P) (directionVector_ne_zero K σ centre P hPC)

variable (E : Finset (Point K σ)) (centre : Point K σ) (houtside : centre ∉ E)

def projection (x : E) : Direction K σ :=
  projectPoint K σ centre x.val (fun h => houtside (h ▸ x.property))

def directionSet : Finset (Direction K σ) :=
  Finset.univ.image (projection K σ E centre houtside)

def projectionIndex (x : E) : directionSet K σ E centre houtside :=
  ⟨projection K σ E centre houtside x,
    Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

abbrev RayIndex (i : directionSet K σ E centre houtside) :=
  {x : E // projectionIndex K σ E centre houtside x = i}

def raySize (i : directionSet K σ E centre houtside) : ℕ :=
  Fintype.card (RayIndex K σ E centre houtside i)

def rayEnumeration (i : directionSet K σ E centre houtside) :
    Fin (raySize K σ E centre houtside i) ≃ RayIndex K σ E centre houtside i :=
  (Fintype.equivFin (RayIndex K σ E centre houtside i)).symm

theorem raySize_pos (i : directionSet K σ E centre houtside) :
    0 < raySize K σ E centre houtside i := by
  obtain ⟨x, _hx, hxi⟩ := Finset.mem_image.mp i.property
  have hy : RayIndex K σ E centre houtside i := ⟨x, Subtype.ext hxi⟩
  exact Fintype.card_pos_iff.mpr ⟨hy⟩

theorem normalisingUnit_exists (i : directionSet K σ E centre houtside)
    (x : RayIndex K σ E centre houtside i) :
    ∃ u : Kˣ, u • directionVector K σ centre x.val.val = i.val.rep := by
  have hproj : projection K σ E centre houtside x.val = i.val :=
    congrArg Subtype.val x.property
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K
    (directionVector K σ centre x.val.val)
    (directionVector_ne_zero K σ centre x.val.val
      (fun h => houtside (h ▸ x.val.property)))
  refine ⟨u, ?_⟩
  change u • directionVector K σ centre x.val.val =
    (projection K σ E centre houtside x.val).rep at hu
  rw [hproj] at hu
  exact hu

def normalisingUnit (i : directionSet K σ E centre houtside)
    (x : RayIndex K σ E centre houtside i) : Kˣ :=
  Classical.choose (normalisingUnit_exists K σ E centre houtside i x)

theorem normalisingUnit_spec (i : directionSet K σ E centre houtside)
    (x : RayIndex K σ E centre houtside i) :
    normalisingUnit K σ E centre houtside i x • directionVector K σ centre x.val.val = i.val.rep :=
  Classical.choose_spec (normalisingUnit_exists K σ E centre houtside i x)

def normalizedVector (i : directionSet K σ E centre houtside)
    (x : RayIndex K σ E centre houtside i) : Space K σ :=
  (normalisingUnit K σ E centre houtside i x : K) • coordinateChange K σ centre x.val.val.rep

def rayParameter (i : directionSet K σ E centre houtside)
    (x : RayIndex K σ E centre houtside i) : K := normalizedVector K σ E centre houtside i x none

theorem normalizedVector_eq_rayPoint (i : directionSet K σ E centre houtside)
    (x : RayIndex K σ E centre houtside i) :
    normalizedVector K σ E centre houtside i x =
      EvaluationProjection.rayPoint i.val.rep (rayParameter K σ E centre houtside i x) := by
  funext o
  cases o with
  | none => rfl
  | some s =>
    have hs := congrFun (normalisingUnit_spec K σ E centre houtside i x) s
    simpa only [normalizedVector, Units.smul_def, Pi.smul_apply, directionVector,
      EvaluationProjection.rayPoint] using hs

theorem map_rep (g : Space K σ ≃ₗ[K] Space K σ) (P : Point K σ) :
    Projectivization.map g.toLinearMap g.injective P =
      Projectivization.mk K (g P.rep)
        (by intro h; exact P.rep_nonzero (g.injective (by simpa using h))) := by
  simpa only [Projectivization.mk_rep, LinearEquiv.coe_coe] using
    Projectivization.map_mk g.toLinearMap g.injective P.rep P.rep_nonzero

theorem rayParameter_injective (i : directionSet K σ E centre houtside) :
    Function.Injective (rayParameter K σ E centre houtside i) := by
  intro x y hxy
  let g := coordinateChange K σ centre
  let u := normalisingUnit K σ E centre houtside i x
  let v := normalisingUnit K σ E centre houtside i y
  have hvector : u • g x.val.val.rep = v • g y.val.val.rep := by
    have hnorm : normalizedVector K σ E centre houtside i x =
        normalizedVector K σ E centre houtside i y := by
      rw [normalizedVector_eq_rayPoint, normalizedVector_eq_rayPoint, hxy]
    simpa only [normalizedVector, Units.smul_def] using hnorm
  have hscale : (u⁻¹ * v) • g y.val.val.rep = g x.val.val.rep := by
    rw [mul_smul, ← hvector, inv_smul_smul]
  apply Subtype.ext
  apply Subtype.ext
  apply Projectivization.map_injective g.toLinearMap g.injective
  rw [map_rep K σ g x.val.val, map_rep K σ g y.val.val]
  exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr ⟨u⁻¹ * v, hscale⟩

def rayTimes (i : directionSet K σ E centre houtside) : Fin (raySize K σ E centre houtside i) → K :=
  fun ν => rayParameter K σ E centre houtside i (rayEnumeration K σ E centre houtside i ν)

theorem rayTimes_injective (i : directionSet K σ E centre houtside) :
    Function.Injective (rayTimes K σ E centre houtside i) :=
  (rayParameter_injective K σ E centre houtside i).comp (rayEnumeration K σ E centre houtside i).injective

theorem sum_over_rays (f : E → K) :
    (∑ i : directionSet K σ E centre houtside,
      ∑ ν : Fin (raySize K σ E centre houtside i), f (rayEnumeration K σ E centre houtside i ν).val) =
      ∑ x : E, f x := by
  calc
    (∑ i : directionSet K σ E centre houtside,
      ∑ ν : Fin (raySize K σ E centre houtside i), f (rayEnumeration K σ E centre houtside i ν).val) =
        ∑ i : directionSet K σ E centre houtside, ∑ x : RayIndex K σ E centre houtside i, f x.val := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (rayEnumeration K σ E centre houtside i).sum_comp (fun x => f x.val)
    _ = ∑ x : (Σ i : directionSet K σ E centre houtside, RayIndex K σ E centre houtside i), f x.2.val :=
      (Fintype.sum_sigma
        (fun x : (Σ i : directionSet K σ E centre houtside, RayIndex K σ E centre houtside i) =>
          f x.2.val)).symm
    _ = ∑ x : E, f x := (Equiv.sigmaFiberEquiv (projectionIndex K σ E centre houtside)).sum_comp f

end Cylinder.ProjectiveProjection

end
