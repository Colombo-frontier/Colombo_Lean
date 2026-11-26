import SecondOrder.ScaledFirstOrderFrontier

open MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T k : ℕ}

def scaledFirstOrderFrontierTrueLaw (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (freshθ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (x : Point (FirstOrderDimension d T)) :
    Measure (RichReply (FirstOrderDimension d T)) :=
  ((firstOrderPastCoefficientLaw pastΘ R hR).toMeasure.prod
    (firstOrderCoefficientLaw freshθ R hR).toMeasure).map (scaledFirstOrderFrontierReply θ₀ pastΘ A β x)

def scaledFirstOrderReferenceKernel (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (A β R : ℝ) (hR : 2≤R) : Kernel (Point (FirstOrderDimension d T)) (RichReply (FirstOrderDimension d T)) :=
  sampledResponseKernel ((firstOrderPastCoefficientLaw pastΘ R hR).toMeasure.prod
    (finitePiPMF (fun _ : Fin d => fairCoefficientPMF R hR)).toMeasure)
      (scaledFirstOrderFrontierReply θ₀ pastΘ A β) (scaledFirstOrderFrontierReply_measurable θ₀ pastΘ A β R)

def scaledFirstOrderExtendedKernel (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ)
    (hR : 2≤R) (k : ℕ) : Kernel (Point (FirstOrderDimension d T)) (RichReply (FirstOrderDimension d T)) :=
  sampledResponseKernel (firstOrderChainCoefficientLaw Θ R hR).toMeasure
    (fun x z => scaledFirstOrderTruncatedReply Θ A β z k x) (scaledFirstOrderTruncatedReply_measurable Θ A β R k)

instance scaledFirstOrderReferenceKernel_markov (θ₀ : (Fin d → Bool))
    (pastΘ : Fin k → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) :
    IsMarkovKernel (scaledFirstOrderReferenceKernel (T := T) θ₀ pastΘ A β R hR) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

instance scaledFirstOrderExtendedKernel_markov (Θ : Fin (T+1) → (Fin d → Bool))
    (A β R : ℝ) (hR : 2≤R) (k : ℕ) : IsMarkovKernel (scaledFirstOrderExtendedKernel Θ A β R hR k) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

theorem scaledFirstOrderReferenceKernel_base_independent (θ₀ θ₁ : (Fin d → Bool))
    (pastΘ : Fin k → (Fin d → Bool)) (hk : k≤T) (A β R : ℝ) (hR : 2≤R)
    (x : Point (FirstOrderDimension d T)) :
    scaledFirstOrderReferenceKernel θ₀ pastΘ A β R hR x =
      scaledFirstOrderReferenceKernel θ₁ pastΘ A β R hR x := by
  have he : scaledFirstOrderFrontierReply θ₀ pastΘ A β (R := R) x =
      scaledFirstOrderFrontierReply θ₁ pastΘ A β x :=
    funext (scaledFirstOrderFrontierReply_base_independent θ₀ θ₁ pastΘ A β hk x)
  change Measure.map _ _ = Measure.map _ _
  rw [he]

theorem scaledFirstOrderFrontier_kl (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (freshθ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (x : Point (FirstOrderDimension d T)) :
    klDiv (scaledFirstOrderFrontierTrueLaw θ₀ pastΘ freshθ A β R hR x)
      (scaledFirstOrderReferenceKernel θ₀ pastΘ A β R hR x) ≤
      ENNReal.ofReal ((d:ℝ)/R^2) := by
  have hp : ∀ a, firstOrderPastCoefficientLaw pastΘ R hR a ≠ 0 := by
    apply finitePiPMF_ne_zero
    intro i
    apply finitePiPMF_ne_zero
    intro e
    exact coefficientPMF_ne_zero R _ hR _
  have hh := coefficientResponse_with_past_kl (firstOrderPastCoefficientLaw pastΘ R hR) hp
    R (fun i => signValue (freshθ i)) hR (fun i => signValue_sq (freshθ i)) (scaledFirstOrderFrontierReply θ₀ pastΘ A β x)
  simpa only [Fintype.card_fin] using hh

theorem scaledFirstOrderTruncatedReply_law_frontier (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (hk : k≤T) (x : Point (FirstOrderDimension d T)) :
    (firstOrderChainCoefficientLaw Θ R hR).toMeasure.map (fun z => scaledFirstOrderTruncatedReply Θ A β z k x) =
      scaledFirstOrderFrontierTrueLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩)
        (Θ ⟨k,by omega⟩) A β R hR x := by
  let π : FirstOrderCoefficients d T R →
      FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R) :=
    fun z => ((fun i : Fin k => z ⟨i.val,by omega⟩),z ⟨k,by omega⟩)
  let pastΘ : Fin k → (Fin d → Bool) := fun i => Θ ⟨i.val,by omega⟩
  have he : (fun z : FirstOrderCoefficients d T R => scaledFirstOrderTruncatedReply Θ A β z k x) =
      scaledFirstOrderFrontierReply θ₀ pastΘ A β x ∘ π :=
    funext (fun z => scaledFirstOrderTruncatedReply_frontier_map Θ θ₀ A β z hk x)
  rw [he, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hmarg := finitePiPMF_prefix_next (fun i : Fin (T+1) => firstOrderCoefficientLaw (Θ i) R hR)
    (show k<T+1 by omega)
  change (firstOrderChainCoefficientLaw Θ R hR).toMeasure.map π =
    (firstOrderPastCoefficientLaw pastΘ R hR).toMeasure.prod
      (firstOrderCoefficientLaw (Θ ⟨k,by omega⟩) R hR).toMeasure at hmarg
  rw [hmarg]
  rfl

/-- Scaling and flattening preserve the uniform information bound for the
actual full second-order response of the extended loss. -/
theorem scaledFirstOrderExtendedKernel_kl (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (hk : k≤T) (x : Point (FirstOrderDimension d T)) :
    klDiv (scaledFirstOrderExtendedKernel Θ A β R hR k x)
      (scaledFirstOrderReferenceKernel θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β R hR x) ≤
      ENNReal.ofReal ((d:ℝ)/R^2) := by
  change klDiv ((firstOrderChainCoefficientLaw Θ R hR).toMeasure.map
    (fun z => scaledFirstOrderTruncatedReply Θ A β z k x)) _ ≤ _
  rw [scaledFirstOrderTruncatedReply_law_frontier Θ θ₀ A β R hR hk x]
  exact scaledFirstOrderFrontier_kl θ₀ _ _ A β R hR x

theorem scaledFirstOrderReply_frontier_kl (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (hk : k≤T) (x : Point (FirstOrderDimension d T))
    (hfuture : ∀ i, k ≤ i.val → firstOrderBlockCompletion (Θ i) ((firstOrderDilation d T β x) i)=0) :
    klDiv ((firstOrderChainCoefficientLaw Θ R hR).toMeasure.map (fun z => richReply (scaledFirstOrderSample Θ A β) z x))
      (scaledFirstOrderReferenceKernel θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β R hR x) ≤
      ENNReal.ofReal ((d:ℝ)/R^2) := by
  have he : (fun z : FirstOrderCoefficients d T R => richReply (scaledFirstOrderSample Θ A β) z x) =
      (fun z => scaledFirstOrderTruncatedReply Θ A β z k x) :=
    funext (fun z => scaledFirstOrderReply_truncate Θ A β z k x hfuture)
  rw [he]
  exact scaledFirstOrderExtendedKernel_kl Θ θ₀ A β R hR hk x

theorem scaledFirstOrderReply_progress_kl (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (x : Point (FirstOrderDimension d T))
    (hp : firstOrderProgress Θ (firstOrderDilation d T β x)≤T) :
    klDiv ((firstOrderChainCoefficientLaw Θ R hR).toMeasure.map (fun z => richReply (scaledFirstOrderSample Θ A β) z x))
      (scaledFirstOrderReferenceKernel θ₀
        (fun i : Fin (firstOrderProgress Θ (firstOrderDilation d T β x)) => Θ ⟨i.val,by omega⟩) A β R hR x) ≤
      ENNReal.ofReal ((d:ℝ)/R^2) :=
  scaledFirstOrderReply_frontier_kl Θ θ₀ A β R hR hp x (firstOrderProgress_future_zero Θ _)

end
end SecondOrder

