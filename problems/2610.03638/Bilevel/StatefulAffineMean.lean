import Bilevel.HistoryStep

/-! Exact centering for a stateful original-call affine update. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful.HistoryOracle
variable {Query History Obs E Param : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs] [MeasurableSpace Param]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

theorem step_mean (q : Param → Query) (hq : Measurable q) (d : Param → E)
    (hd : Measurable d) (η : Param → ℝ) (hη : Measurable η)
    (p : Param) (h : History) (center : E) :
    Integrable (fun z => z.1-center) ((O.step q hq d hd η hη).law (p,h)) ∧
    (∫ z,z.1-center ∂(O.step q hq d hd η hη).law (p,h))=
      d p-η p • O.truth (q p)-center := by
  have hg : StronglyMeasurable (fun v : E => v-center) :=
    (by fun_prop : Measurable (fun v : E => v-center)).stronglyMeasurable
  have hM := O.call_mean (q p) h
  have he : (fun z : Outcome E History => d p-η p • z.1-center)=
      (fun z => (d p-η p • O.truth (q p)-center)-η p • (z.1-O.truth (q p))) := by
    funext z
    module
  constructor
  · rw [step,Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    change Integrable (fun z => d p-η p • z.1-center) (O.call.law (q p,h))
    rw [he]
    exact (integrable_const _).sub (hM.1.smul (η p))
  · rw [step,Procedure.map_output_integral _ _ _ _ _ _ hg]
    change (∫ z,d p-η p • z.1-center ∂O.call.law (q p,h))=_
    rw [he]
    have hs := integral_sub (integrable_const (μ := O.call.law (q p,h)) (d p-η p • O.truth (q p)-center)) (hM.1.smul (η p))
    simp only [Pi.sub_apply,Pi.smul_apply] at hs
    rw [hs,integral_smul,hM.2]
    simp only [integral_const,measureReal_univ_eq_one,one_smul,smul_zero,sub_zero]

end Bilevel.Stateful.HistoryOracle



