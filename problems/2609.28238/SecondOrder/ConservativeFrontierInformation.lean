import SecondOrder.ConservativeReplies
import SecondOrder.FinitePrefixLaw

open MeasureTheory InformationTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {T m : ℕ} {E : Fin (T+1) → Type*} {Θ : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]
  [MeasurableSpace (ScalarRichResponse (PiLp 2 E))]
  [MeasurableSingletonClass (ScalarRichResponse (PiLp 2 E))]

namespace ConservativeFeatureData

def pastLaw (D : ConservativeFeatureData T m E Θ) {k : ℕ} (hk : k ≤ T) (pastθ : Fin k → Θ)
    (R : ℝ) (hR : 2 ≤ R) : PMF (Fin k → Fin m → SignedCoefficient R) :=
  finitePiPMF (fun i => D.blockLaw ⟨i.val,by omega⟩ (pastθ i) R hR)

def frontierTrueLaw (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ₀ : Θ) {k : ℕ} (hk : k ≤ T)
    (pastθ : Fin k → Θ) (freshθ : Θ) (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    Measure (ScalarRichResponse (PiLp 2 E)) :=
  ((D.pastLaw hk pastθ R hR).toMeasure.prod (D.blockLaw ⟨k,by omega⟩ freshθ R hR).toMeasure).map
    (D.frontierReply reg gate θ₀ pastθ x)

/-- Only past hidden blocks appear. The next coefficient array is fair,
and all earlier coefficient laws remain unchanged. -/
def frontierReferenceLaw (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ₀ : Θ) {k : ℕ} (hk : k ≤ T)
    (pastθ : Fin k → Θ) (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    Measure (ScalarRichResponse (PiLp 2 E)) :=
  ((D.pastLaw hk pastθ R hR).toMeasure.prod
    (finitePiPMF (fun _ : Fin m => fairCoefficientPMF R hR)).toMeasure).map
    (D.frontierReply reg gate θ₀ pastθ x)

theorem frontierReferenceLaw_base_independent (D : ConservativeFeatureData T m E Θ)
    (reg : PiLp 2 E → ℝ) (gate : (i : Fin (T+1)) → Θ → E i → ℝ)
    (θ₀ θ₁ : Θ) {k : ℕ} (hk : k ≤ T) (pastθ : Fin k → Θ) (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    D.frontierReferenceLaw reg gate θ₀ hk pastθ R hR x=D.frontierReferenceLaw reg gate θ₁ hk pastθ R hR x := by
  have he : D.frontierReply reg gate θ₀ pastθ (R := R) x=D.frontierReply reg gate θ₁ pastθ x :=
    funext (D.frontierReply_base_independent reg gate θ₀ θ₁ pastθ hk x)
  unfold frontierReferenceLaw
  rw [he]

theorem frontier_kl (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ₀ : Θ) {k : ℕ} (hk : k ≤ T)
    (pastθ : Fin k → Θ) (freshθ : Θ) (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    klDiv (D.frontierTrueLaw reg gate θ₀ hk pastθ freshθ R hR x)
      (D.frontierReferenceLaw reg gate θ₀ hk pastθ R hR x) ≤ ENNReal.ofReal ((m:ℝ)/R^2) := by
  have hp : ∀ a, D.pastLaw hk pastθ R hR a≠0 :=
    finitePiPMF_ne_zero _ (fun i => D.blockLaw_ne_zero ⟨i.val,by omega⟩ (pastθ i) R hR)
  simpa only [Fintype.card_fin] using coefficientResponse_with_past_kl (D.pastLaw hk pastθ R hR) hp
    R (D.sign ⟨k,by omega⟩ freshθ) hR (D.sign_sq ⟨k,by omega⟩ freshθ)
    (D.frontierReply reg gate θ₀ pastθ x)

/-- Exact marginalization of the full independent coefficient array. -/
theorem truncatedReply_law_frontier (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) (θ₀ : Θ)
    {k : ℕ} (hk : k ≤ T) (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    (D.arrayLaw θ R hR).toMeasure.map (fun z => D.truncatedReply reg gate θ z k x)=
      D.frontierTrueLaw reg gate θ₀ hk (fun i : Fin k => θ ⟨i.val,by omega⟩)
        (θ ⟨k,by omega⟩) R hR x := by
  let π : (Fin (T+1) → Fin m → SignedCoefficient R) →
      (Fin k → Fin m → SignedCoefficient R) × (Fin m → SignedCoefficient R) :=
    fun z => ((fun i : Fin k => z ⟨i.val,by omega⟩),z ⟨k,by omega⟩)
  let pastθ : Fin k → Θ := fun i => θ ⟨i.val,by omega⟩
  have he : (fun z : Fin (T+1) → Fin m → SignedCoefficient R => D.truncatedReply reg gate θ z k x)=
      D.frontierReply reg gate θ₀ pastθ x ∘ π :=
    funext (fun z => D.truncatedReply_frontier_map reg gate θ θ₀ hk z x)
  rw [he,←Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hmarg := finitePiPMF_prefix_next (fun i : Fin (T+1) => D.blockLaw i (θ i) R hR)
    (show k<T+1 by omega)
  change (D.arrayLaw θ R hR).toMeasure.map π=(D.pastLaw hk pastθ R hR).toMeasure.prod
    (D.blockLaw ⟨k,by omega⟩ (θ ⟨k,by omega⟩) R hR).toMeasure at hmarg
  rw [hmarg]
  rfl

/-- Uniform information bound for the actual extended rich reply law,
including queries away from the frontier. The universal constant is one. -/
theorem truncatedReply_frontier_kl (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) (θ₀ : Θ)
    {k : ℕ} (hk : k ≤ T) (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    klDiv ((D.arrayLaw θ R hR).toMeasure.map (fun z => D.truncatedReply reg gate θ z k x))
      (D.frontierReferenceLaw reg gate θ₀ hk (fun i : Fin k => θ ⟨i.val,by omega⟩) R hR x) ≤
      ENNReal.ofReal ((m:ℝ)/R^2) := by
  rw [D.truncatedReply_law_frontier reg gate θ θ₀ hk R hR x]
  exact D.frontier_kl reg gate θ₀ hk _ _ R hR x

end ConservativeFeatureData
end
end SecondOrder
