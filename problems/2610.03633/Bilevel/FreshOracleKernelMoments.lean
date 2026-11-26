import Bilevel.FreshOracle
import Bilevel.ConditionalKernelRepair

/-! A genuine fresh sample pushforward has the conditional full-vector
moments used by the history-kernel upper algorithm, with unchanged variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.FreshOracle
set_option autoImplicit false
variable {Q A H C O E : Type*}
  [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace H] [MeasurableSpace C] [MeasurableSpace O]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure C} {σ : ℝ}

omit [CompleteSpace E] in
theorem Oracle.kernel_good (F : Oracle (Query:=A) (E:=E) ν σ)
    (K : Kernel (Q × H) O) [IsMarkovKernel K]
    (response : Q → C → O) (hr : ∀ q,Measurable (response q))
    (hK : ∀ q h,K (q,h)=ν.map (response q))
    (encode : Q → A) (read : O → E) (hm : Measurable read)
    (hread : ∀ q c,read (response q c)=F.sample (encode q) c) (q : Q) (h : H) :
    ConditionalKernelRepair.Good K (fun z => read z.2-F.truth (encode z.1.1)) σ (q,h) := by
  unfold ConditionalKernelRepair.Good
  dsimp only
  rw [hK]
  have hme : Measurable (fun o => read o-F.truth (encode q)) := hm.sub measurable_const
  have hms := hme.norm.pow_const 2
  refine ⟨?_,?_,?_⟩
  · apply (integrable_map_measure hms.aestronglyMeasurable (hr q).aemeasurable).mpr
    change Integrable (fun c => ‖read (response q c)-F.truth (encode q)‖^2) ν
    simpa only [hread] using F.square_integrable (encode q)
  · rw [integral_map (hr q).aemeasurable hme.aestronglyMeasurable]
    simpa only [hread] using F.mean (encode q)
  · rw [integral_map (hr q).aemeasurable hms.aestronglyMeasurable]
    simpa only [hread] using F.variance (encode q)

end Bilevel.FreshOracle
