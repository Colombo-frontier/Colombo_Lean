import SecondOrder.ScaledCurvatureFrontier

open MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T k : ℕ}

def scaledCurvatureFrontierTrueLaw (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (freshθ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (x : Point (CurvatureDimension m T)) :
    Measure (RichReply (CurvatureDimension m T)) :=
  ((curvaturePastCoefficientLaw pastΘ R hR).toMeasure.prod
    (periodicCoefficientLaw freshθ.1 R hR).toMeasure).map (scaledCurvatureFrontierReply θ₀ pastΘ A β x)

def scaledCurvatureReferenceKernel (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) : Kernel (Point (CurvatureDimension m T)) (RichReply (CurvatureDimension m T)) :=
  sampledResponseKernel ((curvaturePastCoefficientLaw pastΘ R hR).toMeasure.prod
    (finitePiPMF (fun _ : UpperPair (2*m) => fairCoefficientPMF R hR)).toMeasure)
      (scaledCurvatureFrontierReply θ₀ pastΘ A β) (scaledCurvatureFrontierReply_measurable θ₀ pastΘ A β R)

def scaledCurvatureExtendedKernel (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ)
    (hR : 2≤R) (k : ℕ) : Kernel (Point (CurvatureDimension m T)) (RichReply (CurvatureDimension m T)) :=
  sampledResponseKernel (curvatureCoefficientLaw Θ R hR).toMeasure
    (fun x z => scaledCurvatureTruncatedReply Θ A β z k x) (scaledCurvatureTruncatedReply_measurable Θ A β R k)

instance scaledCurvatureReferenceKernel_markov (θ₀ : BalancedVector m)
    (pastΘ : Fin k → BalancedVector m) (A β R : ℝ) (hR : 2≤R) :
    IsMarkovKernel (scaledCurvatureReferenceKernel (T := T) θ₀ pastΘ A β R hR) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

instance scaledCurvatureExtendedKernel_markov (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) (k : ℕ) : IsMarkovKernel (scaledCurvatureExtendedKernel Θ A β R hR k) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

theorem scaledCurvatureReferenceKernel_base_independent (θ₀ θ₁ : BalancedVector m)
    (pastΘ : Fin k → BalancedVector m) (hk : k≤T) (A β R : ℝ) (hR : 2≤R)
    (x : Point (CurvatureDimension m T)) :
    scaledCurvatureReferenceKernel θ₀ pastΘ A β R hR x =
      scaledCurvatureReferenceKernel θ₁ pastΘ A β R hR x := by
  have he : scaledCurvatureFrontierReply θ₀ pastΘ A β (R := R) x =
      scaledCurvatureFrontierReply θ₁ pastΘ A β x :=
    funext (scaledCurvatureFrontierReply_base_independent θ₀ θ₁ pastΘ A β hk x)
  change Measure.map _ _ = Measure.map _ _
  rw [he]

theorem scaledCurvatureFrontier_kl (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (freshθ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (x : Point (CurvatureDimension m T)) :
    klDiv (scaledCurvatureFrontierTrueLaw θ₀ pastΘ freshθ A β R hR x)
      (scaledCurvatureReferenceKernel θ₀ pastΘ A β R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) := by
  have hp : ∀ a, curvaturePastCoefficientLaw pastΘ R hR a ≠ 0 := by
    apply finitePiPMF_ne_zero
    intro i
    apply finitePiPMF_ne_zero
    intro e
    exact coefficientPMF_ne_zero R _ hR _
  have hh := coefficientResponse_with_past_kl (curvaturePastCoefficientLaw pastΘ R hR) hp
    R (pairSign freshθ.1) hR (pairSign_sq freshθ.1) (scaledCurvatureFrontierReply θ₀ pastΘ A β x)
  rw [upperPair_card_real] at hh
  convert hh using 1 <;> congr 1 <;> ring

theorem scaledCurvatureTruncatedReply_law_frontier (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (hk : k≤T) (x : Point (CurvatureDimension m T)) :
    (curvatureCoefficientLaw Θ R hR).toMeasure.map (fun z => scaledCurvatureTruncatedReply Θ A β z k x) =
      scaledCurvatureFrontierTrueLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩)
        (Θ ⟨k,by omega⟩) A β R hR x := by
  let π : CurvatureCoefficients m T R →
      CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R) :=
    fun z => ((fun i : Fin k => z ⟨i.val,by omega⟩),z ⟨k,by omega⟩)
  let pastΘ : Fin k → BalancedVector m := fun i => Θ ⟨i.val,by omega⟩
  have he : (fun z : CurvatureCoefficients m T R => scaledCurvatureTruncatedReply Θ A β z k x) =
      scaledCurvatureFrontierReply θ₀ pastΘ A β x ∘ π :=
    funext (fun z => scaledCurvatureTruncatedReply_frontier_map Θ θ₀ A β z hk x)
  rw [he, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hmarg := finitePiPMF_prefix_next (fun i : Fin (T+1) => periodicCoefficientLaw (Θ i).1 R hR)
    (show k<T+1 by omega)
  change (curvatureCoefficientLaw Θ R hR).toMeasure.map π =
    (curvaturePastCoefficientLaw pastΘ R hR).toMeasure.prod
      (periodicCoefficientLaw (Θ ⟨k,by omega⟩).1 R hR).toMeasure at hmarg
  rw [hmarg]
  rfl

/-- Scaling and flattening preserve the uniform information bound for the
actual full second-order response of the extended loss. -/
theorem scaledCurvatureExtendedKernel_kl (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (hk : k≤T) (x : Point (CurvatureDimension m T)) :
    klDiv (scaledCurvatureExtendedKernel Θ A β R hR k x)
      (scaledCurvatureReferenceKernel θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) := by
  change klDiv ((curvatureCoefficientLaw Θ R hR).toMeasure.map
    (fun z => scaledCurvatureTruncatedReply Θ A β z k x)) _ ≤ _
  rw [scaledCurvatureTruncatedReply_law_frontier Θ θ₀ A β R hR hk x]
  exact scaledCurvatureFrontier_kl θ₀ _ _ A β R hR x

theorem scaledCurvatureReply_frontier_kl (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (hk : k≤T) (x : Point (CurvatureDimension m T))
    (hfuture : ∀ i, k ≤ i.val → periodicCompletion (Θ i) ((curvatureDilation m T β x) i)=0) :
    klDiv ((curvatureCoefficientLaw Θ R hR).toMeasure.map (fun z => richReply (scaledCurvatureSample Θ A β) z x))
      (scaledCurvatureReferenceKernel θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) := by
  have he : (fun z : CurvatureCoefficients m T R => richReply (scaledCurvatureSample Θ A β) z x) =
      (fun z => scaledCurvatureTruncatedReply Θ A β z k x) :=
    funext (fun z => scaledCurvatureReply_truncate Θ A β z k x hfuture)
  rw [he]
  exact scaledCurvatureExtendedKernel_kl Θ θ₀ A β R hR hk x

theorem scaledCurvatureReply_progress_kl (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (x : Point (CurvatureDimension m T))
    (hp : curvatureProgress Θ (curvatureDilation m T β x)≤T) :
    klDiv ((curvatureCoefficientLaw Θ R hR).toMeasure.map (fun z => richReply (scaledCurvatureSample Θ A β) z x))
      (scaledCurvatureReferenceKernel θ₀
        (fun i : Fin (curvatureProgress Θ (curvatureDilation m T β x)) => Θ ⟨i.val,by omega⟩) A β R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) :=
  scaledCurvatureReply_frontier_kl Θ θ₀ A β R hR hp x (curvatureProgress_future_zero Θ _)

end
end SecondOrder
