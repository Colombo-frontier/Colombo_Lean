import SecondOrder.CurvatureFrontierDependence
import SecondOrder.FinitePrefixLaw

open MeasureTheory InformationTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T k : ℕ}

def curvaturePastCoefficientLaw (pastΘ : Fin k → BalancedVector m) (R : ℝ) (hR : 2≤R) :
    PMF (CurvaturePastCoefficients m k R) :=
  finitePiPMF (fun i => periodicCoefficientLaw (pastΘ i).1 R hR)

def curvatureFrontierTrueLaw (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (freshθ : BalancedVector m) (R : ℝ) (hR : 2≤R) (x : CurvatureSpace m T) :
    Measure (CurvatureRichResponse m T) :=
  ((curvaturePastCoefficientLaw pastΘ R hR).toMeasure.prod
    (periodicCoefficientLaw freshθ.1 R hR).toMeasure).map (curvatureFrontierReply θ₀ pastΘ x)

/-- The reference law preserves the entire past law and uses fair coefficients
only for the fresh array. It has no fresh hidden-vector argument. -/
def curvatureFrontierReferenceLaw (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (R : ℝ) (hR : 2≤R) (x : CurvatureSpace m T) : Measure (CurvatureRichResponse m T) :=
  ((curvaturePastCoefficientLaw pastΘ R hR).toMeasure.prod
    (finitePiPMF (fun _ : UpperPair (2*m) => fairCoefficientPMF R hR)).toMeasure).map
      (curvatureFrontierReply θ₀ pastΘ x)

theorem curvatureFrontierReferenceLaw_base_independent (θ₀ θ₁ : BalancedVector m)
    (pastΘ : Fin k → BalancedVector m) (hk : k≤T) (R : ℝ) (hR : 2≤R) (x : CurvatureSpace m T) :
    curvatureFrontierReferenceLaw θ₀ pastΘ R hR x =
      curvatureFrontierReferenceLaw θ₁ pastΘ R hR x := by
  have he : curvatureFrontierReply θ₀ pastΘ (R := R) x = curvatureFrontierReply θ₁ pastΘ x :=
    funext (curvatureFrontierReply_base_independent θ₀ θ₁ pastΘ hk x)
  unfold curvatureFrontierReferenceLaw
  rw [he]

theorem curvatureFrontier_kl (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (freshθ : BalancedVector m) (R : ℝ) (hR : 2≤R) (x : CurvatureSpace m T) :
    klDiv (curvatureFrontierTrueLaw θ₀ pastΘ freshθ R hR x)
      (curvatureFrontierReferenceLaw θ₀ pastΘ R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) := by
  have hp : ∀ a, curvaturePastCoefficientLaw pastΘ R hR a ≠ 0 := by
    apply finitePiPMF_ne_zero
    intro i
    apply finitePiPMF_ne_zero
    intro e
    exact coefficientPMF_ne_zero R _ hR _
  have hh := coefficientResponse_with_past_kl (curvaturePastCoefficientLaw pastΘ R hR) hp
    R (pairSign freshθ.1) hR (pairSign_sq freshθ.1) (curvatureFrontierReply θ₀ pastΘ x)
  rw [upperPair_card_real] at hh
  convert hh using 1 <;> congr 1 <;> ring

/-- The actual full-array sampling experiment has exactly the same response
law as the past-and-fresh experiment; unused arrays are marginalized out. -/
theorem curvatureTruncatedReply_law_frontier (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : CurvatureSpace m T) :
    (curvatureCoefficientLaw Θ R hR).toMeasure.map (fun z => curvatureTruncatedReply Θ z k x) =
      curvatureFrontierTrueLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩)
        (Θ ⟨k,by omega⟩) R hR x := by
  let π : CurvatureCoefficients m T R →
      CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R) :=
    fun z => ((fun i : Fin k => z ⟨i.val,by omega⟩),z ⟨k,by omega⟩)
  let pastΘ : Fin k → BalancedVector m := fun i => Θ ⟨i.val,by omega⟩
  have he : (fun z : CurvatureCoefficients m T R => curvatureTruncatedReply Θ z k x) =
      curvatureFrontierReply θ₀ pastΘ x ∘ π :=
    funext (fun z => curvatureTruncatedReply_frontier_map Θ θ₀ z hk x)
  rw [he, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hmarg := finitePiPMF_prefix_next (fun i : Fin (T+1) => periodicCoefficientLaw (Θ i).1 R hR)
    (show k<T+1 by omega)
  change (curvatureCoefficientLaw Θ R hR).toMeasure.map π =
    (curvaturePastCoefficientLaw pastΘ R hR).toMeasure.prod
      (periodicCoefficientLaw (Θ ⟨k,by omega⟩).1 R hR).toMeasure at hmarg
  rw [hmarg]
  rfl

theorem curvatureTruncatedReply_frontier_kl (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : CurvatureSpace m T) :
    klDiv ((curvatureCoefficientLaw Θ R hR).toMeasure.map (fun z => curvatureTruncatedReply Θ z k x))
      (curvatureFrontierReferenceLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) := by
  rw [curvatureTruncatedReply_law_frontier Θ θ₀ R hR hk x]
  exact curvatureFrontier_kl θ₀ _ _ R hR x

/-- The actual full-array sampling experiment has exactly the same response
law as the past-and-fresh experiment; unused arrays are marginalized out. -/
theorem curvatureRichReply_law_frontier (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : CurvatureSpace m T)
    (hfuture : ∀ i, k ≤ i.val → periodicCompletion (Θ i) (x i)=0) :
    (curvatureCoefficientLaw Θ R hR).toMeasure.map (fun z => curvatureRichReply Θ z x) =
      curvatureFrontierTrueLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩)
        (Θ ⟨k,by omega⟩) R hR x := by
  have he : (fun z : CurvatureCoefficients m T R => curvatureRichReply Θ z x) =
      (fun z => curvatureTruncatedReply Θ z k x) :=
    funext (fun z => curvatureRichReply_truncate Θ z k x hfuture)
  rw [he]
  exact curvatureTruncatedReply_law_frontier Θ θ₀ R hR hk x

/-- The manuscript's one-call frontier information bound, for the actual
joint value/gradient/Hessian response of the conservative chain loss. -/
theorem curvatureRichReply_frontier_kl (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : CurvatureSpace m T)
    (hfuture : ∀ i, k ≤ i.val → periodicCompletion (Θ i) (x i)=0) :
    klDiv ((curvatureCoefficientLaw Θ R hR).toMeasure.map (fun z => curvatureRichReply Θ z x))
      (curvatureFrontierReferenceLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) := by
  rw [curvatureRichReply_law_frontier Θ θ₀ R hR hk x hfuture]
  exact curvatureFrontier_kl θ₀ _ _ R hR x

end
end SecondOrder
