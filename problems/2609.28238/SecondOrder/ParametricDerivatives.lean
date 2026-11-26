import SecondOrder.BlockMixtureInterior

namespace SecondOrder
noncomputable section
variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiation in the second variable preserves joint parameter regularity. -/
theorem contDiff_parametric_fderiv {f : P → E → F} {m n : WithTop ℕ∞}
    (hf : ContDiff ℝ m (Function.uncurry f)) (hmn : n+1 ≤ m) :
    ContDiff ℝ n (fun z : P × E => fderiv ℝ (f z.1) z.2) := by
  have hh : ContDiff ℝ m (fun z : (P × E) × E => f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv contDiff_snd hmn

theorem continuous_parametric_derivatives {f : P → E → F}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    Continuous (fun z : P × E => fderiv ℝ (f z.1) z.2) ∧
      Continuous (fun z : P × E => fderiv ℝ (fderiv ℝ (f z.1)) z.2) := by
  have hfirst := contDiff_parametric_fderiv hf (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)
  have hsecond := contDiff_parametric_fderiv (f := fun t x => fderiv ℝ (f t) x)
    hfirst (show (0:WithTop ℕ∞)+1 ≤ 1 by norm_num)
  exact ⟨hfirst.continuous, hsecond.continuous⟩

theorem continuous_parametric_derivative_norms {f : P → E → F}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (x : E) :
    Continuous (fun t : P => ‖fderiv ℝ (f t) x‖) ∧
      Continuous (fun t : P => ‖fderiv ℝ (fderiv ℝ (f t)) x‖) := by
  letI : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
  have hh := continuous_parametric_derivatives (f := f) hf
  have hc₁ : Continuous (fun t : P => fderiv ℝ (f t) x) :=
    hh.1.comp (continuous_id.prodMk continuous_const)
  have hc₂ : Continuous (fun t : P => fderiv ℝ (fderiv ℝ (f t)) x) :=
    hh.2.comp (continuous_id.prodMk continuous_const)
  exact ⟨hc₁.norm, continuous_norm.comp hc₂⟩

end
end SecondOrder
