import SecondOrder.OracleProgramSeededKernel

open MeasureTheory ProbabilityTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O Ω S T : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

theorem seededOutputLaw_prod_eq_bind (μ : Measure Ω) (η : Measure S) (θ : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] [IsProbabilityMeasure θ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S × T → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) :
    seededOutputLaw μ (η.prod θ) q₀ o₀ reply p N=
      η.bind (seededOutputKernel μ θ q₀ y₀ o₀ a₀ reply hr p hp N) := by
  let K := outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N
  let H := seededOutputKernel μ θ q₀ y₀ o₀ a₀ reply hr p hp N
  rw [seededOutputLaw_eq_bind μ (η.prod θ) q₀ y₀ o₀ a₀ reply hr p hp N]
  change (η.prod θ).bind K=η.bind H
  ext e he
  rw [Measure.bind_apply he K.measurable.aemeasurable,
    Measure.bind_apply he H.measurable.aemeasurable,
    lintegral_prod _ (K.measurable_coe he).aemeasurable]
  apply lintegral_congr
  intro s
  exact (seededOutputKernel_apply_set μ θ q₀ y₀ o₀ a₀ reply hr p hp N s e he).symm

end
end OracleProgram
end SecondOrder
