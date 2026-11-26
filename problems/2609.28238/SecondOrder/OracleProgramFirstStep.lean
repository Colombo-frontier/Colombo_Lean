import SecondOrder.OracleProgramOutputKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O Ω S : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace Ω] [MeasurableSpace S]

theorem MeasurableFamily.firstAdvance {q₀ : Q} {o₀ : O} {p : S → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) (y₀ : Y) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2)) :
    MeasurableFamily q₀ o₀ (fun w : S × Ω => OracleProgram.advance (p w.1)
      (reply (OracleProgram.query q₀ (p w.1)) w.2)) := by
  have ht : Measurable (fun s : S => (s,fun _ : ℕ => y₀)) := measurable_id.prodMk measurable_const
  have hq := (hp.query 0).comp ht
  have hreply := hr.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  exact hp.advance.comp _ (measurable_fst.prodMk hreply)

theorem MeasurableFamily.firstOutput {q₀ : Q} {o₀ : O} {p : S → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) (y₀ : Y) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2)) (N : ℕ) (s : S) :
    Measurable (fun w : Ω × Draws Ω N =>
      OracleProgram.output o₀ (runDraws q₀ reply
        (OracleProgram.advance (p s) (reply (OracleProgram.query q₀ (p s)) w.1)) N w.2)) := by
  have ht : Measurable (fun w : Ω × Draws Ω N => ((s,w.1),w.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  exact ((hp.firstAdvance y₀ reply hr).runDrawsOutput y₀ a₀ reply hr N).comp ht

theorem outputLaw_first_step_apply (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p)
    (N : ℕ) (s : S) (e : Set O) (he : MeasurableSet e) :
    outputLaw μ q₀ o₀ reply (p s) (N+1) e=
      ∫⁻ z, outputLaw μ q₀ o₀ reply (advance (p s) (reply (query q₀ (p s)) z)) N e ∂μ := by
  have hm := hp.firstOutput y₀ a₀ reply hr N s
  rw [outputLaw_first_step μ q₀ y₀ o₀ a₀ reply hr p hp N s,
    Measure.map_apply hm he,Measure.prod_apply (hm he)]
  apply lintegral_congr
  intro z
  have ht : Measurable (fun w : Draws Ω N => (z,w)) := measurable_const.prodMk measurable_id
  have hmz := hm.comp ht
  change Measurable (fun w : Draws Ω N =>
    output o₀ (runDraws q₀ reply (advance (p s) (reply (query q₀ (p s)) z)) N w)) at hmz
  rw [outputLaw,Measure.map_apply hmz he]
  rfl

theorem lintegral_outputLaw_first_step (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p)
    (N : ℕ) (s : S) (g : O → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ o, g o ∂outputLaw μ q₀ o₀ reply (p s) (N+1))=
      ∫⁻ z, ∫⁻ o, g o ∂outputLaw μ q₀ o₀ reply (advance (p s) (reply (query q₀ (p s)) z)) N ∂μ := by
  have hm := hp.firstOutput y₀ a₀ reply hr N s
  have hgm : Measurable (fun w : Ω × Draws Ω N =>
    g (output o₀ (runDraws q₀ reply (advance (p s) (reply (query q₀ (p s)) w.1)) N w.2))) := hg.comp hm
  rw [outputLaw_first_step μ q₀ y₀ o₀ a₀ reply hr p hp N s,lintegral_map hg hm,
    lintegral_prod _ hgm.aemeasurable]
  apply lintegral_congr
  intro z
  have ht : Measurable (fun w : Draws Ω N => (z,w)) := measurable_const.prodMk measurable_id
  exact (lintegral_map hg (hm.comp ht)).symm

end
end OracleProgram
end SecondOrder
