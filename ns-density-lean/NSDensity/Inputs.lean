import NSDensity.Arithmetic
import NSDensity.Sieve

/-!
Explicit interface for the one external analytic-number-theory theorem.
This is a proposition supplied as a theorem parameter, not an axiom declaration.
Only reciprocal divergence is needed; neither a density formula nor an error term
is assumed. The classification interface is defined with the initial families.
-/

namespace NSDensity

def OrderPrimes (b h : ℕ) : Set ℕ :=
  {r | r.Prime ∧ Nat.Coprime b r ∧ h ∣ orderOf (b : ZMod r)}

/-- The precise consequence of Wiertelak--Moree used in this project. -/
def WiertelakMoreeInput : Prop :=
  ∀ b h : ℕ, 1 < b → 1 < h → ReciprocalDiverges (OrderPrimes b h)

theorem orderPrimes_prime {b h r : ℕ} (hr : r ∈ OrderPrimes b h) : r.Prime := hr.1

theorem densityZero_avoids_orderPrimes (hWM : WiertelakMoreeInput)
    {b h : ℕ} (hb : 1 < b) (hh : 1 < h) :
    DensityZero (avoids (OrderPrimes b h)) :=
  densityZero_avoids (fun _ hr => hr.1) (hWM b h hb hh)

theorem densityZero_atMostOne_orderPrimes (hWM : WiertelakMoreeInput)
    {b h : ℕ} (hb : 1 < b) (hh : 1 < h) :
    DensityZero (atMostOne (OrderPrimes b h)) :=
  densityZero_atMostOne (fun _ hr => hr.1) (hWM b h hb hh)

end NSDensity
