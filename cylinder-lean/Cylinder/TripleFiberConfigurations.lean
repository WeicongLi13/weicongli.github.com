module

public import Cylinder.InvolutionPairRepresentatives

/-! Every three-element fibre gives three different unordered pairs:
one is obtained by deleting each of its elements. This is an actual
finite construction, indexed by the original elements. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.TripleFiberConfigurations

variable {I J V : Type*} [Fintype I]

def fiber (k : I → J) (x : I) : Finset I := Finset.univ.filter (fun y => k y = k x)

def configuration (k : I → J) (x : I) : Finset I := (fiber k x).erase x

theorem mem_fiber (k : I → J) (x y : I) : y ∈ fiber k x ↔ k y = k x := by
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]

theorem self_mem_fiber (k : I → J) (x : I) : x ∈ fiber k x := (mem_fiber k x x).mpr rfl

theorem fiber_eq (k : I → J) (x y : I) (h : k x = k y) : fiber k x = fiber k y := by
  ext z
  rw [mem_fiber, mem_fiber, h]

theorem configuration_card (k : I → J) (hthree : ∀ x, (fiber k x).card = 3) (x : I) :
    (configuration k x).card = 2 := by
  rw [configuration, Finset.card_erase_of_mem (self_mem_fiber k x), hthree]

theorem configuration_injective (k : I → J) (hthree : ∀ x, (fiber k x).card = 3) :
    Function.Injective (configuration k) := by
  intro x y hxy
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (configuration k x).card by rw [configuration_card k hthree]; decide)
  have hzx := (mem_fiber k x z).mp (Finset.mem_erase.mp hz).2
  have hzy := (mem_fiber k y z).mp (Finset.mem_erase.mp (hxy ▸ hz)).2
  have hF := fiber_eq k x y (hzx.symm.trans hzy)
  change (fiber k x).erase x = (fiber k y).erase y at hxy
  rw [← hF] at hxy
  exact (Finset.erase_inj _ (self_mem_fiber k x)).mp hxy

theorem configurations_card (k : I → J) (hthree : ∀ x, (fiber k x).card = 3) :
    (Finset.univ.image (configuration k)).card = Fintype.card I := by
  rw [Finset.card_image_of_injective _ (configuration_injective k hthree), Finset.card_univ]

theorem configuration_sum_ne_zero [AddCommMonoid V] (k : I → J) (v : I → V)
    (hn : ∀ x, v x ≠ 0) (hzero : ∀ x, (∑ y ∈ fiber k x, v y) = 0) (x : I) :
    (∑ y ∈ configuration k x, v y) ≠ 0 := by
  intro hz
  have hs := Finset.sum_erase_add (fiber k x) v (self_mem_fiber k x)
  change (∑ y ∈ configuration k x, v y) + v x = ∑ y ∈ fiber k x, v y at hs
  rw [hz, zero_add, hzero] at hs
  exact hn x hs

end Cylinder.TripleFiberConfigurations
end
