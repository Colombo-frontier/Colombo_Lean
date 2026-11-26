import SampleReuse.DisclosureEntropy
import SecondOrder.ScaledFirstOrderFrontier

/-!
The conservative scalar loss supplies a complete value/gradient/Hessian jet.
Once all later gates vanish, that jet is a deterministic function of the
known hidden prefix, the saved coefficient prefix, and one next-block array.
This file replaces the predecessor's fresh past-array law by fixed arrays
already in the transcript, and permits the next array itself to be cached.
-/

open MeasureTheory InformationTheory SecondOrder
open scoped ENNReal Classical

namespace SampleReuse
noncomputable section
variable {d T k : ℕ}

/-- A frontier simulator with a fixed coefficient prefix. It has no next
hidden-vector input. All three returned entries are derivatives of one scalar loss. -/
def persistentFrontierReply (θ₀ : Fin d → Bool) (pastΘ : Fin k → Fin d → Bool)
    (A β : ℝ) {R : ℝ} (x : Point (FirstOrderDimension d T))
    (pastZ : FirstOrderPastCoefficients d k R) (z : Fin d → SignedCoefficient R) :
    RichReply (FirstOrderDimension d T) :=
  scaledFirstOrderFrontierReply θ₀ pastΘ A β x (pastZ, z)

/-- Actual derivative-oracle equality, not equality of an auxiliary response
statistic. The next hidden sign block is absent from the simulator. -/
theorem scalar_jet_persistent_frontier
    (Θ : Fin (T + 1) → Fin d → Bool) (θ₀ : Fin d → Bool)
    (A β : ℝ) {R : ℝ} (z : FirstOrderCoefficients d T R) (hk : k ≤ T)
    (x : Point (FirstOrderDimension d T))
    (hfuture : ∀ i, k ≤ i.val →
      firstOrderBlockCompletion (Θ i) ((firstOrderDilation d T β x) i) = 0) :
    richReply (scaledFirstOrderSample Θ A β) z x =
      persistentFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val, by omega⟩) A β x
        (fun i : Fin k => z ⟨i.val, by omega⟩) (z ⟨k, by omega⟩) := by
  rw [scaledFirstOrderReply_truncate Θ A β z k x hfuture]
  exact scaledFirstOrderTruncatedReply_frontier_map Θ θ₀ A β z hk x

theorem persistentFrontierReply_base_independent
    (θ₀ θ₁ : Fin d → Bool) (pastΘ : Fin k → Fin d → Bool)
    (A β : ℝ) {R : ℝ} (hk : k ≤ T) (x : Point (FirstOrderDimension d T))
    (pastZ : FirstOrderPastCoefficients d k R) (z : Fin d → SignedCoefficient R) :
    persistentFrontierReply θ₀ pastΘ A β x pastZ z =
      persistentFrontierReply θ₁ pastΘ A β x pastZ z :=
  scaledFirstOrderFrontierReply_base_independent θ₀ θ₁ pastΘ A β hk x (pastZ, z)

/-- Concrete one-step information bound with persistent past arrays and a
possibly already-disclosed frontier array. New arrays cost D/R²; reuse costs zero. -/
theorem persistentFrontierReply_kl
    (θ₀ : Fin d → Bool) (pastΘ : Fin k → Fin d → Bool)
    (freshθ : Fin d → Bool) (A β R : ℝ) (hR : 2 ≤ R)
    (x : Point (FirstOrderDimension d T)) (pastZ : FirstOrderPastCoefficients d k R)
    (saved : Option (Fin d → SignedCoefficient R)) :
    klDiv
      ((disclosurePMF saved (firstOrderCoefficientLaw freshθ R hR)).toMeasure.map
        (persistentFrontierReply θ₀ pastΘ A β x pastZ))
      ((disclosurePMF saved
        (finitePiPMF (fun _ : Fin d => fairCoefficientPMF R hR))).toMeasure.map
        (persistentFrontierReply θ₀ pastΘ A β x pastZ)) ≤
      ENNReal.ofReal (if saved = none then (d : ℝ) / R ^ 2 else 0) := by
  cases saved with
  | none =>
    simpa only [disclosurePMF, firstOrderCoefficientLaw, if_true, Fintype.card_fin] using
      coefficientResponse_kl R (fun i => signValue (freshθ i)) hR
        (fun i => signValue_sq (freshθ i))
        (persistentFrontierReply θ₀ pastΘ A β x pastZ)
  | some a => simp [disclosurePMF, klDiv_self]

end
end SampleReuse
