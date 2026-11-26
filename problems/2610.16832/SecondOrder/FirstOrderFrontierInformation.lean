import SecondOrder.FirstOrderFrontierDependence
import SecondOrder.FinitePrefixLaw

open MeasureTheory InformationTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T k : ℕ}

def firstOrderPastCoefficientLaw (pastΘ : Fin k → (Fin d → Bool)) (R : ℝ) (hR : 2≤R) :
    PMF (FirstOrderPastCoefficients d k R) :=
  finitePiPMF (fun i => firstOrderCoefficientLaw (pastΘ i) R hR)

def firstOrderFrontierTrueLaw (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (freshθ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R) (x : FirstOrderSpace d T) :
    Measure (FirstOrderRichResponse d T) :=
  ((firstOrderPastCoefficientLaw pastΘ R hR).toMeasure.prod
    (firstOrderCoefficientLaw freshθ R hR).toMeasure).map (firstOrderFrontierReply θ₀ pastΘ x)

/-- The reference law preserves the entire past law and uses fair coefficients
only for the fresh array. It has no fresh hidden-vector argument. -/
def firstOrderFrontierReferenceLaw (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (x : FirstOrderSpace d T) : Measure (FirstOrderRichResponse d T) :=
  ((firstOrderPastCoefficientLaw pastΘ R hR).toMeasure.prod
    (finitePiPMF (fun _ : Fin d => fairCoefficientPMF R hR)).toMeasure).map
      (firstOrderFrontierReply θ₀ pastΘ x)

theorem firstOrderFrontierReferenceLaw_base_independent (θ₀ θ₁ : (Fin d → Bool))
    (pastΘ : Fin k → (Fin d → Bool)) (hk : k≤T) (R : ℝ) (hR : 2≤R) (x : FirstOrderSpace d T) :
    firstOrderFrontierReferenceLaw θ₀ pastΘ R hR x =
      firstOrderFrontierReferenceLaw θ₁ pastΘ R hR x := by
  have he : firstOrderFrontierReply θ₀ pastΘ (R := R) x = firstOrderFrontierReply θ₁ pastΘ x :=
    funext (firstOrderFrontierReply_base_independent θ₀ θ₁ pastΘ hk x)
  unfold firstOrderFrontierReferenceLaw
  rw [he]

theorem firstOrderFrontier_kl (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (freshθ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R) (x : FirstOrderSpace d T) :
    klDiv (firstOrderFrontierTrueLaw θ₀ pastΘ freshθ R hR x)
      (firstOrderFrontierReferenceLaw θ₀ pastΘ R hR x) ≤
      ENNReal.ofReal ((d:ℝ)/R^2) := by
  have hp : ∀ a, firstOrderPastCoefficientLaw pastΘ R hR a ≠ 0 := by
    apply finitePiPMF_ne_zero
    intro i
    apply finitePiPMF_ne_zero
    intro e
    exact coefficientPMF_ne_zero R _ hR _
  have hh := coefficientResponse_with_past_kl (firstOrderPastCoefficientLaw pastΘ R hR) hp
    R (fun i => signValue (freshθ i)) hR (fun i => signValue_sq (freshθ i)) (firstOrderFrontierReply θ₀ pastΘ x)
  simpa only [Fintype.card_fin] using hh

/-- The actual full-array sampling experiment has exactly the same response
law as the past-and-fresh experiment; unused arrays are marginalized out. -/
theorem firstOrderTruncatedReply_law_frontier (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : FirstOrderSpace d T) :
    (firstOrderChainCoefficientLaw Θ R hR).toMeasure.map (fun z => firstOrderTruncatedReply Θ z k x) =
      firstOrderFrontierTrueLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩)
        (Θ ⟨k,by omega⟩) R hR x := by
  let π : FirstOrderCoefficients d T R →
      FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R) :=
    fun z => ((fun i : Fin k => z ⟨i.val,by omega⟩),z ⟨k,by omega⟩)
  let pastΘ : Fin k → (Fin d → Bool) := fun i => Θ ⟨i.val,by omega⟩
  have he : (fun z : FirstOrderCoefficients d T R => firstOrderTruncatedReply Θ z k x) =
      firstOrderFrontierReply θ₀ pastΘ x ∘ π :=
    funext (fun z => firstOrderTruncatedReply_frontier_map Θ θ₀ z hk x)
  rw [he, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hmarg := finitePiPMF_prefix_next (fun i : Fin (T+1) => firstOrderCoefficientLaw (Θ i) R hR)
    (show k<T+1 by omega)
  change (firstOrderChainCoefficientLaw Θ R hR).toMeasure.map π =
    (firstOrderPastCoefficientLaw pastΘ R hR).toMeasure.prod
      (firstOrderCoefficientLaw (Θ ⟨k,by omega⟩) R hR).toMeasure at hmarg
  rw [hmarg]
  rfl

theorem firstOrderTruncatedReply_frontier_kl (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : FirstOrderSpace d T) :
    klDiv ((firstOrderChainCoefficientLaw Θ R hR).toMeasure.map (fun z => firstOrderTruncatedReply Θ z k x))
      (firstOrderFrontierReferenceLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) R hR x) ≤
      ENNReal.ofReal ((d:ℝ)/R^2) := by
  rw [firstOrderTruncatedReply_law_frontier Θ θ₀ R hR hk x]
  exact firstOrderFrontier_kl θ₀ _ _ R hR x

/-- The actual full-array sampling experiment has exactly the same response
law as the past-and-fresh experiment; unused arrays are marginalized out. -/
theorem firstOrderRichReply_law_frontier (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : FirstOrderSpace d T)
    (hfuture : ∀ i, k ≤ i.val → firstOrderBlockCompletion (Θ i) (x i)=0) :
    (firstOrderChainCoefficientLaw Θ R hR).toMeasure.map (fun z => firstOrderRichReply Θ z x) =
      firstOrderFrontierTrueLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩)
        (Θ ⟨k,by omega⟩) R hR x := by
  have he : (fun z : FirstOrderCoefficients d T R => firstOrderRichReply Θ z x) =
      (fun z => firstOrderTruncatedReply Θ z k x) :=
    funext (fun z => firstOrderRichReply_truncate Θ z k x hfuture)
  rw [he]
  exact firstOrderTruncatedReply_law_frontier Θ θ₀ R hR hk x

/-- The manuscript's one-call frontier information bound, for the actual
joint value/gradient/Hessian response of the conservative chain loss. -/
theorem firstOrderRichReply_frontier_kl (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : FirstOrderSpace d T)
    (hfuture : ∀ i, k ≤ i.val → firstOrderBlockCompletion (Θ i) (x i)=0) :
    klDiv ((firstOrderChainCoefficientLaw Θ R hR).toMeasure.map (fun z => firstOrderRichReply Θ z x))
      (firstOrderFrontierReferenceLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) R hR x) ≤
      ENNReal.ofReal ((d:ℝ)/R^2) := by
  rw [firstOrderRichReply_law_frontier Θ θ₀ R hR hk x hfuture]
  exact firstOrderFrontier_kl θ₀ _ _ R hR x

end
end SecondOrder

