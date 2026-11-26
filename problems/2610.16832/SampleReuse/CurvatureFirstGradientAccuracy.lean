import SampleReuse.CurvatureFirstGradientCache
import SampleReuse.TreeSamplingConfidence
import SampleReuse.CheckpointRecurrence

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem macroGradientLocation_of_present {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    (k : ℕ) (g : SampleTape ((T+1)*Bg) Ω)
    (ht : macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ≤ T) :
    macroGradientLocation hBg hBH P ε γ scaleG scaleH F h signs x₀ k g =
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀
        (macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g)).1 := by
  simp only [macroGradientLocation,if_pos ht]

set_option maxHeartbeats 2000000 in
theorem macroGradientEstimate_eq {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (g : SampleTape ((T+1)*Bg) Ω) (h : SampleTape ((T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (k : ℕ)
    (ht : macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ≤ T) :
    inspectionGradient hBg P scaleG F (derivativeTapes g h)
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀
        (macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g)) =
      sampledAncestorEstimate hBg scaleG P.gradientNoise P.gradientLip (fun z => gradient (F z))
        (macroGradientLocation hBg hBH P ε γ scaleG scaleH F h signs x₀) g k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hk := macroGradientTime_clock_eq hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ht
    have hx := macroGradientLocation_of_present hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ht
    cases k with
    | zero =>
      simp only [inspectionGradient,hk,checkpointValue,if_true,checkpointPacket,
        sampledAncestorEstimate,ancestorEstimate,treeRootPacket,batchMeanTape,derivativeTapes_gradient,hx]
    | succ k =>
      have hj : ancestorParent (k+1) <
          (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀
            (macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ (k+1) g)).2.1 := by
        rw [hk]
        exact ancestorParent_lt (Nat.succ_pos k)
      have htime := macroGradientTime_before hBg hBH P ε γ scaleG scaleH F h signs x₀ _ _ g hj
      have hjT := htime.le.trans ht
      have hentry := macroGradientCache_entry_before hBg hBH P ε γ scaleG scaleH F h signs x₀ _ _ g ht hj
      have hxj := macroGradientLocation_of_present hBg hBH P ε γ scaleG scaleH F h signs x₀ _ g hjT
      unfold inspectionGradient
      rw [hk,checkpointValue_packet_parent hBg scaleG P.gradientNoise P.gradientLip
        (fun z => gradient (F z)) (gradientReserve T Bg BH) (Nat.succ_pos k) _ _ _ _ _ hentry]
      change inspectionGradient hBg P scaleG F (derivativeTapes g h) _ + _ = _
      rw [ih _ (ancestorParent_lt (Nat.succ_pos k)) hjT]
      unfold sampledAncestorEstimate
      rw [ancestorEstimate]
      congr 1
      unfold treeChordPacket adaptiveBatchMean
      rw [hx,hxj]
      simp only [batchMeanTape,derivativeTapes_gradient]

theorem Admissible.curvatureFirst_gradient_accuracy {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    (ε γ scaleG scaleH : ℝ) (z₀ : Ω) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scaleG = confidenceBatchScale d (η/(binaryDepth T+1)) (δ/(T+1)))
    (hcap : Bg = batchSize scaleG (P.gradientNoise^2))
    (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) :
    1-δ ≤ (sampleTapeLaw ((T+1)*Bg) μ).real {g | ∀ k ≤ T,
      macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ≤ T →
      let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀
        (macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g)
      ‖inspectionGradient hBg P scaleG F (derivativeTapes g h) s-gradient f s.1‖ ≤ η} := by
  have hb := had.gradient_tree_success z₀ hη hδ hscale hcap hBg _
    (macroGradientLocation_predictable hBg hBH P ε γ scaleG scaleH F
      had.gradient_measurable had.hessian_measurable h signs x₀)
  apply hb.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro g hg k hk ht
  dsimp only
  rw [macroGradientEstimate_eq hBg hBH P ε γ scaleG scaleH F g h signs x₀ k ht]
  have hkg := hg k hk
  rw [macroGradientLocation_of_present hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ht] at hkg
  exact hkg

end
end SampleReuse
