import Bilevel.MultiscaleFrameExpected

/-! Actual original-call property for every Borel adaptive algorithm and
private seed, with arbitrary output and infinite-call executions allowed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.MultiscaleMean
open SingleFrameSource ChiHierarchyIndex ChiHierarchyExecution ChiHierarchyHaar CompensatedMean BorelAdaptive
variable {n D : ℕ}

def InnerRateProperty (P : Parameters (E:=EuclideanGaussian.Space D) n)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D) (p : ℝ) (hp1 : p≤1) (ε cost : ℝ) : Prop :=
  ∀ [MeasurableSpace (LowerSpace (EuclideanGaussian.Space D))]
    [BorelSpace (LowerSpace (EuclideanGaussian.Space D))],
  ∀ {Private : Type u} {State : Type v} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (InnerQuery (EuclideanGaussian.Space D)) (InnerReply (EuclideanGaussian.Space D))
      (EuclideanGaussian.Space D))
    (initial : Private → State) (_hi : Measurable initial) (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (_haccuracy : ∀ a,(∫⁻ z,ENNReal.ofReal (Function.uncurry (innerFrameLoss P hD)
      (seededStopped alg (innerFrameReply P p hD) initial (a,z)))
      ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))≤ENNReal.ofReal ε),
    ∃ a : Orientations (counts n) 0 D,
      ENNReal.ofReal cost≤∫⁻ z,seededCalls alg (innerFrameReply P p hD) initial (a,z)
        ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))

theorem innerRateProperty_mono (P : Parameters (E:=EuclideanGaussian.Space D) n)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D) (p : ℝ) (hp1 : p≤1) (ε : ℝ)
    {a b : ℝ} (H : InnerRateProperty.{u,v} P hD p hp1 ε a) (hab : b≤a) :
    InnerRateProperty.{u,v} P hD p hp1 ε b := by
  intro instM instB Private State instP instS alg initial hi ρ instρ hacc
  obtain ⟨x,hx⟩ := @H instM instB Private State instP instS alg initial hi ρ instρ hacc
  exact ⟨x,(ENNReal.ofReal_le_ofReal hab).trans hx⟩

end Bilevel.MultiscaleMean
