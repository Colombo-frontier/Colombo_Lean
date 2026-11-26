import SecondOrder.OjaCandidate

open MeasureTheory
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def ojaCurvatureTolerance (P : Parameters) (γ : ℝ) : ℝ := γ/(4*eigenHessianBound P)

theorem ojaCurvatureTolerance_pos (P : Parameters) {γ : ℝ} (hγ : 0 < γ) :
    0 < ojaCurvatureTolerance P γ := by
  have hB := eigenHessianBound_pos P
  exact div_pos hγ (by positivity)

theorem oja_negative_threshold_algebra {B γ ℓ R : ℝ} (hB : 0 < B)
    (hℓ : (B+γ)/(2*B) < ℓ) (hR : ℓ-(γ/(4*B))/2 ≤ R) :
    (B+3*γ/4)/(2*B) ≤ R := by
  have he : (B+γ)/(2*B) - (γ/(4*B))/2 = (B+3*γ/4)/(2*B) := by field_simp; ring
  linarith

/-- Only the base candidate run is counted here; independent validation
and confidence amplification are separate operations still to be added. -/
theorem oja_negative_candidate_query_bound {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (hd : 0 < d) {γ : ℝ} (hγ : 0 < γ)
    (hγB : γ ≤ 4*eigenHessianBound P) (x : Point d)
    (w : (Draws Ω (ojaIterationCount d (ojaCurvatureTolerance P γ)) × (Fin d → Bool)) ×
      Fin (ojaIterationCount d (ojaCurvatureTolerance P γ))) :
    ((ojaCandidateTrace P f (ojaLearningRate d (ojaCurvatureTolerance P γ)) x
      (ojaIterationCount d (ojaCurvatureTolerance P γ)) w).length : ℝ) ≤
        104976*(eigenHessianBound P)^2*(1+Real.log (4*(d:ℝ)))^2/γ^2 := by
  rw [ojaCandidateTrace_length]
  have hB := eigenHessianBound_pos P
  have he := ojaCurvatureTolerance_pos P hγ
  have he1 : ojaCurvatureTolerance P γ ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*eigenHessianBound P)).mpr
    simpa using hγB
  have hn := ojaIterationCount_bound hd he he1
  convert hn using 1
  unfold ojaCurvatureTolerance
  field_simp
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.topRayleigh_gt_of_not_certificate (h : CommonLoss μ P ν F f)
    (hd : 0 < d) (x : Point d) (γ : ℝ) (hbad : ¬ RayleighCertificate γ (hessian F x)) :
    (eigenHessianBound P+γ)/(2*eigenHessianBound P) <
      topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) := by
  by_contra hn
  have htop := (h.mean_shifted_top_eigenpair hd x).2.2.1
  have hbound : ∀ v, ⟪shiftedHessian (eigenHessianBound P) (hessian F x) v,v⟫_ℝ ≤
      ((eigenHessianBound P+γ)/(2*eigenHessianBound P))*‖v‖^2 := by
    intro v
    exact (htop v).trans (mul_le_mul_of_nonneg_right (le_of_not_gt hn) (sq_nonneg _))
  exact hbad ((shiftedHessian_certificate_iff (eigenHessianBound_pos P) (hessian F x) γ).mp hbound)

/-- Whenever the Hessian certificate is false, one completely specified
base run returns a direction with curvature ≤-3γ/4 with probability ≥1/96.
The extra γ/4 of margin is reserved for subsequent independent validation.
The algorithm does not receive the failed-certificate hypothesis. -/
theorem CommonLoss.oja_negative_candidate (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {γ : ℝ} (hγ : 0 < γ) (x : Point d) (hbad : ¬ RayleighCertificate γ (hessian F x)) :
    (1:ℝ)/96 ≤ (ojaCandidateLaw μ d (ojaIterationCount d (ojaCurvatureTolerance P γ))
      (ojaIterationCount_pos hd (ojaCurvatureTolerance_pos P hγ))).real {w |
        ‖ojaCandidate P f (ojaLearningRate d (ojaCurvatureTolerance P γ)) x
          (ojaIterationCount d (ojaCurvatureTolerance P γ)) w‖ = 1 ∧
        ⟪hessian F x (ojaCandidate P f (ojaLearningRate d (ojaCurvatureTolerance P γ)) x
          (ojaIterationCount d (ojaCurvatureTolerance P γ)) w),
            ojaCandidate P f (ojaLearningRate d (ojaCurvatureTolerance P γ)) x
              (ojaIterationCount d (ojaCurvatureTolerance P γ)) w⟫_ℝ ≤ -(3*γ/4)} := by
  have hp := h.oja_candidate_accuracy hd (ojaCurvatureTolerance_pos P hγ) x
  have htop := h.topRayleigh_gt_of_not_certificate hd x γ hbad
  refine hp.trans ?_
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro w hw
  refine ⟨hw.1,?_⟩
  apply (shiftedHessian_negative_iff (eigenHessianBound_pos P) (hessian F x) (3*γ/4) hw.1).mp
  exact oja_negative_threshold_algebra (eigenHessianBound_pos P) htop hw.2

end
end SecondOrder
