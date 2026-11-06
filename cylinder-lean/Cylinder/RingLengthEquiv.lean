module

public import Mathlib.RingTheory.Length

/-! Ring isomorphisms preserve the length of the ring as a module over itself. -/

@[expose] public section
noncomputable section

namespace Cylinder.RingLengthEquiv

set_option autoImplicit false

theorem self_length_eq {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : R →ₛₗ[e.toRingHom] S :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := e.map_mul }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

end Cylinder.RingLengthEquiv

end
