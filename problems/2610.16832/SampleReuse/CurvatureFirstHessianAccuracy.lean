import SampleReuse.CurvatureFirstTapes
import SampleReuse.CurvatureFirstTrajectoryMeasurable
import SampleReuse.TreeSamplingConfidence

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem macroHessianLocation_predictable {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (g : SampleTape ((T+1)*Bg) Ω) (signs : ℕ → Bool) (x₀ : Point d) :
    PredictableLocations (macroHessianLocation hBg hBH P ε γ scaleG scaleH F g signs x₀) := by
  constructor
  · intro t _
    exact ((curvatureMacroRun_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH x₀ t).comp
      (((derivativeTapes_measurable _ _).comp (measurable_const.prodMk measurable_id)).prodMk measurable_const)).fst
  · intro t ht h h' heq
    exact macroHessianLocation_depends hBg hBH P ε γ scaleG scaleH F g signs x₀ ht h h' heq

theorem macroHessianEstimate_eq {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (g : SampleTape ((T+1)*Bg) Ω) (h : SampleTape ((T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (t : ℕ) :
    inspectionHessian hBH P scaleH F (derivativeTapes g h) t
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t) =
      sampledAncestorEstimate hBH scaleH P.hessianNoise P.hessianLip (fun z => hessian (F z))
        (macroHessianLocation hBg hBH P ε γ scaleG scaleH F g signs x₀) h t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero =>
      simp only [inspectionHessian,checkpointValue,if_true,checkpointPacket,
        sampledAncestorEstimate,ancestorEstimate,treeRootPacket,batchMeanTape,macroHessianLocation,
        derivativeTapes_hessian]
    | succ t =>
      have hc := curvatureMacroRun_hessianCache_entry hBg hBH P ε γ scaleG scaleH F
        (derivativeTapes g h) signs x₀ (ancestorParent_lt (Nat.succ_pos t))
      simp only [inspectionHessian,checkpointValue,Nat.succ_ne_zero,if_false]
      rw [hc]
      change inspectionHessian hBH P scaleH F (derivativeTapes g h) (ancestorParent (t+1)) _ + _ = _
      rw [ih _ (ancestorParent_lt (Nat.succ_pos t))]
      simp only [sampledAncestorEstimate,ancestorEstimate,checkpointPacket,checkpointBatchSize,
        Nat.succ_ne_zero,if_false,treeChordPacket,adaptiveBatchMean,batchMeanTape,
        macroHessianLocation,derivativeTapes_hessian]
      rw [hc]
      simp only [Nat.add_one_ne_zero,if_false]
      rfl

theorem Admissible.curvatureFirst_hessian_accuracy {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    (ε γ scaleG scaleH : ℝ) (z₀ : Ω) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scaleH = confidenceBatchScale d (η/(binaryDepth T+1)) (δ/(T+1)))
    (hcap : BH = batchSize scaleH (P.hessianNoise^2))
    (g : SampleTape ((T+1)*Bg) Ω) (signs : ℕ → Bool) :
    1-δ ≤ (sampleTapeLaw ((T+1)*BH) μ).real {h | ∀ t ≤ T,
      let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t
      ‖inspectionHessian hBH P scaleH F (derivativeTapes g h) t s-hessian f s.1‖ ≤ η} := by
  simp_rw [macroHessianEstimate_eq]
  exact had.hessian_tree_success z₀ hη hδ hscale hcap hBH _
    (macroHessianLocation_predictable hBg hBH P ε γ scaleG scaleH F
      had.gradient_measurable had.hessian_measurable g signs x₀)

end
end SampleReuse
