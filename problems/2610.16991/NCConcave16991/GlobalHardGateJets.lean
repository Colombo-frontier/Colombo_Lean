import NCConcave16991.GlobalHardJet

/-! # Actual bounded jets for the state gates and state coupling -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationHessian LocalizationStepSecond
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalar_score_jet (g g' : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hd : ∀ t, HasDerivAt g (g' t) t) (A D C : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hvalue : ∀ t, |g t| ≤ A) (hfirst : ∀ t, |g' t| ≤ D)
    (hsecond : ∀ x y, |g' x - g' y| ≤ C * |x - y|)
    (v : E) (hv : ‖v‖ = 1) : JetBound (fun x ↦ g (stateScore v x)) A D (C + 2 * D) := by
  refine ⟨hg.comp (stateScore_contDiff v), hA, hD, by positivity,
    fun x ↦ hvalue _, ?_, ?_⟩
  · intro x
    rw [scalar_score_fderiv g g' hd, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (hfirst _) (radialScore_fderiv_norm_le (by norm_num : (0 : ℝ) < 10) v hv x)
      (norm_nonneg _) hD).trans_eq (mul_one _)
  · exact scalar_score_fderiv_sub_bound g g' hd D C hD hC (fun t _ ↦ hfirst t) hsecond v hv

theorem gateDerivative_sub_bound (x y : ℝ) : |deriv gate x - deriv gate y| ≤ 200 * |x - y| := by
  apply scalar_derivative_sub_bound (deriv gate) (deriv (deriv gate)) 200 _ gateSecond_bound x y
  intro t
  exact ((contDiff_infty_iff_deriv.mp gate_contDiff).2.differentiable (by simp) t).hasDerivAt

theorem gate_score_jet (v : E) (hv : ‖v‖ = 1) :
    JetBound (fun x ↦ gate (stateScore v x)) 1 10 220 := by
  convert scalar_score_jet gate (deriv gate) gate_contDiff
    (fun t ↦ (gate_contDiff.differentiable (by simp) t).hasDerivAt)
    1 10 200 (by norm_num) (by norm_num) (by norm_num)
    (fun t ↦ by rw [abs_of_nonneg (gate_nonneg t)]; exact gate_le_one t)
    (fun t ↦ by rw [abs_of_nonneg (gate_deriv_bound t).1]; exact (gate_deriv_bound t).2)
    gateDerivative_sub_bound v hv using 1 <;> norm_num

theorem stateClampDerivative_sub_bound (x y : ℝ) :
    |stateClampDerivative x - stateClampDerivative y| ≤ 16 * |x - y| :=
  scalar_derivative_sub_bound _ _ _ stateClampDerivative_hasDerivAt stateClampSecond_abs_bound x y

theorem stateClamp_score_jet (v : E) (hv : ‖v‖ = 1) :
    JetBound (fun x ↦ stateClamp (stateScore v x)) (5 / 2) 1 18 := by
  convert scalar_score_jet stateClamp stateClampDerivative stateClamp_contDiff stateClamp_hasDerivAt
    (5 / 2) 1 16 (by norm_num) (by norm_num) (by norm_num) stateClamp_abs_bound
    (fun t ↦ by rw [abs_of_nonneg (stateClampDerivative_bounds t).1]; exact (stateClampDerivative_bounds t).2)
    stateClampDerivative_sub_bound v hv using 1 <;> norm_num

theorem one_sub_gate_score_jet (v : E) (hv : ‖v‖ = 1) :
    JetBound (fun x ↦ 1 - gate (stateScore v x)) 1 10 220 := by
  apply (gate_score_jet v hv).one_sub 1 (by norm_num)
  intro x
  rw [abs_of_nonneg (sub_nonneg.mpr (gate_le_one _))]
  linarith [gate_nonneg (stateScore v x)]

theorem one_sub_stateClamp_score_jet (v : E) (hv : ‖v‖ = 1) :
    JetBound (fun x ↦ 1 - stateClamp (stateScore v x)) (7 / 2) 1 18 := by
  apply (stateClamp_score_jet v hv).one_sub (7 / 2) (by norm_num)
  intro x
  have hh := abs_sub (1 : ℝ) (stateClamp (stateScore v x))
  norm_num at hh
  linarith [stateClamp_abs_bound (stateScore v x)]

theorem precedingFactor_score_jet (v : E) (hv : ‖v‖ = 1) :
    JetBound (fun x ↦ precedingFactor (stateScore v x)) (7 / 2) 36 808 := by
  convert (one_sub_stateClamp_score_jet v hv).mul (one_sub_gate_score_jet v hv) using 1 <;>
    norm_num [precedingFactor]

variable {H A : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Actual neighboring-state coupling, for any two coordinate contractions.
The dimensions of the two state spaces need not agree. -/
theorem stateCoupling_score_jet (v : A) (hv : ‖v‖ = 1) (w : E) (hw : ‖w‖ = 1)
    (P : H →L[ℝ] A) (hP : ‖P‖ ≤ 1) (Q : H →L[ℝ] E) (hQ : ‖Q‖ ≤ 1) :
    JetBound (fun x ↦ stateCoupling (stateScore v (P x)) (stateScore w (Q x)))
      602 12212 395256 := by
  have hc := ((gate_score_jet w hw).comp_contraction Q hQ).mul
    ((precedingFactor_score_jet v hv).comp_contraction P hP)
  convert hc.const_mul stateWeight using 1 <;> norm_num [stateCoupling, stateWeight, mul_assoc]

end

end NCConcave16991.GlobalHard
