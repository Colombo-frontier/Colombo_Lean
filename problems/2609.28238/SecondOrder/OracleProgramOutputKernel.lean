import SecondOrder.FirstDrawsLaw
import SecondOrder.SampledResponseKernel

open MeasureTheory ProbabilityTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O Ω S : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace Ω] [MeasurableSpace S]

def outputKernel (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) : Kernel S O :=
  sampledResponseKernel (drawsLaw μ N)
    (fun s w => output o₀ (runDraws q₀ reply (p s) N w)) (hp.runDrawsOutput y₀ a₀ reply hr N)

theorem outputKernel_apply (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) (s : S) :
    outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N s=outputLaw μ q₀ o₀ reply (p s) N := rfl

instance outputKernel_markov (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) :
    IsMarkovKernel (outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N) := by
  unfold outputKernel
  infer_instance

theorem MeasurableFamily.outputRun {q₀ : Q} {o₀ : O} {p : S → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) (y₀ : Y) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2)) (N : ℕ) (s : S) :
    Measurable (fun w : Draws Ω N => OracleProgram.output o₀ (runDraws q₀ reply (p s) N w)) :=
  (hp.runDrawsOutput y₀ a₀ reply hr N).comp (measurable_const.prodMk measurable_id)

theorem outputLaw_first_step (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) (s : S) :
    outputLaw μ q₀ o₀ reply (p s) (N+1)=
      Measure.map (fun w : Ω × Draws Ω N =>
        output o₀ (runDraws q₀ reply (advance (p s) (reply (query q₀ (p s)) w.1)) N w.2))
        (μ.prod (drawsLaw μ N)) := by
  have ht := drawsPrepend_measurePreserving μ N
  unfold outputLaw
  rw [←ht.map_eq,Measure.map_map (hp.outputRun y₀ a₀ reply hr (N+1) s) ht.measurable]
  apply congrArg (fun g : Ω × Draws Ω N → O => Measure.map g (μ.prod (drawsLaw μ N)))
  funext w
  exact congrArg (output o₀) (runDraws_prepend q₀ reply (p s) N w.1 w.2)

theorem outputLaw_add_of_usesAtMost (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ)
    (s : S) (hN : UsesAtMost N (p s)) (M : ℕ) :
    outputLaw μ q₀ o₀ reply (p s) (N+M)=outputLaw μ q₀ o₀ reply (p s) N := by
  have ht := drawsAppend_measurePreserving μ N M
  have he : Measure.map Prod.fst ((drawsLaw μ N).prod (drawsLaw μ M))=drawsLaw μ N := by
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  unfold outputLaw
  rw [←ht.map_eq,Measure.map_map (hp.outputRun y₀ a₀ reply hr (N+M) s) ht.measurable]
  conv_rhs => rw [←he,Measure.map_map (hp.outputRun y₀ a₀ reply hr N s) measurable_fst]
  apply congrArg (fun g : Draws Ω N × Draws Ω M → O =>
    Measure.map g ((drawsLaw μ N).prod (drawsLaw μ M)))
  funext w
  exact runDraws_append_output_of_usesAtMost q₀ o₀ a₀ reply hN M w.1 w.2

end
end OracleProgram
end SecondOrder
