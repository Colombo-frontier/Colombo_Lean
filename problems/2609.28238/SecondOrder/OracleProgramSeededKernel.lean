import SecondOrder.OracleProgramBoundedBind

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O Ω S T : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

/-- The output kernel also integrates an independent private seed. -/
def seededOutputKernel (μ : Measure Ω) (η : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S × T → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) :
    Kernel S O :=
  sampledResponseKernel (η.prod (drawsLaw μ N))
    (fun s w => output o₀ (runDraws q₀ reply (p (s,w.1)) N w.2))
    ((hp.runDrawsOutput y₀ a₀ reply hr N).comp
      ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))

theorem seededOutputKernel_apply (μ : Measure Ω) (η : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S × T → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) (s : S) :
    seededOutputKernel μ η q₀ y₀ o₀ a₀ reply hr p hp N s=
      seededOutputLaw μ η q₀ o₀ reply (fun t => p (s,t)) N := rfl

instance seededOutputKernel_markov (μ : Measure Ω) (η : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S × T → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) :
    IsMarkovKernel (seededOutputKernel μ η q₀ y₀ o₀ a₀ reply hr p hp N) := by
  unfold seededOutputKernel
  infer_instance

theorem seededOutputLaw_eq_bind (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) :
    seededOutputLaw μ η q₀ o₀ reply p N=
      η.bind (outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N) := by
  ext e he
  rw [seededOutputLaw,Measure.map_apply (hp.runDrawsOutput y₀ a₀ reply hr N) he,
    Measure.bind_apply he (outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N).measurable.aemeasurable,
    Measure.prod_apply (hp.runDrawsOutput y₀ a₀ reply hr N he)]
  apply lintegral_congr
  intro s
  rw [outputKernel_apply,outputLaw,Measure.map_apply (hp.outputRun y₀ a₀ reply hr N s) he]
  rfl

theorem seededOutputLaw_apply (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ)
    (e : Set O) (he : MeasurableSet e) :
    seededOutputLaw μ η q₀ o₀ reply p N e=
      ∫⁻ s, outputLaw μ q₀ o₀ reply (p s) N e ∂η := by
  rw [seededOutputLaw_eq_bind μ η q₀ y₀ o₀ a₀ reply hr p hp N,
    Measure.bind_apply he (outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N).measurable.aemeasurable]
  rfl

theorem seededOutputKernel_apply_set (μ : Measure Ω) (η : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S × T → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ)
    (s : S) (e : Set O) (he : MeasurableSet e) :
    seededOutputKernel μ η q₀ y₀ o₀ a₀ reply hr p hp N s e=
      ∫⁻ t, outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N (s,t) e ∂η := by
  rw [seededOutputKernel_apply]
  exact seededOutputLaw_apply μ η q₀ y₀ o₀ a₀ reply hr _
    (hp.comp (fun t => (s,t)) (measurable_const.prodMk measurable_id)) N e he

end
end OracleProgram
end SecondOrder
