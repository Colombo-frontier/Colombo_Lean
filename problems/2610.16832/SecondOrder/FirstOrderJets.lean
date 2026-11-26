import SecondOrder.FirstOrderPotentialGeometry

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def ScaledThirdJet (C S : ℝ) (f : E → ℝ) (x : E) : Prop :=
  ‖f x‖≤C ∧ ‖iteratedFDeriv ℝ 1 f x‖≤C ∧
    ‖iteratedFDeriv ℝ 2 f x‖≤C ∧ ‖iteratedFDeriv ℝ 3 f x‖≤C*S

theorem ScaledThirdJet.comp_linear {f : F → ℝ} {C S : ℝ} (hf : ContDiff ℝ 3 f)
    (L : E →L[ℝ] F) (hL : ‖L‖≤1) (x : E) (hb : ScaledThirdJet C S f (L x)) :
    ScaledThirdJet C S (f ∘ L) x := by
  refine ⟨hb.1,?_,?_,?_⟩
  · exact (iteratedFDeriv_linear_contraction f L hL 1 (hf.of_le (show (1:WithTop ℕ∞)≤3 by decide)) x).trans hb.2.1
  · exact (iteratedFDeriv_linear_contraction f L hL 2 (hf.of_le (show (2:WithTop ℕ∞)≤3 by decide)) x).trans hb.2.2.1
  · exact (iteratedFDeriv_linear_contraction f L hL 3 hf x).trans hb.2.2.2

theorem scaledThirdJet_product_second {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    {C S : ℝ} (hC : 0≤C) (x : E) (hfx : ScaledThirdJet C S f x) (hgx : ScaledThirdJet C S g x) :
    ‖iteratedFDeriv ℝ 2 (fun y => f y*g y) x‖≤4*C^2 := by
  have hh := norm_iteratedFDeriv_mul_le (n := 2) hf hg x (show (2:WithTop ℕ∞)≤3 by decide)
  norm_num [Finset.sum_range_succ,norm_iteratedFDeriv_zero] at hh
  change ‖iteratedFDeriv ℝ 2 (fun y => f y*g y) x‖≤
    ‖f x‖*‖iteratedFDeriv ℝ 2 g x‖+2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at hh
  rw [norm_iteratedFDeriv_zero] at hh
  obtain ⟨hf0,hf1,hf2,hf3⟩ := hfx
  obtain ⟨hg0,hg1,hg2,hg3⟩ := hgx
  apply hh.trans
  calc
    _ ≤ C*C+2*C*C+C*C := by gcongr
    _ = _ := by ring

theorem scaledThirdJet_product_third {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    {C S : ℝ} (hC : 0≤C) (hS : 1≤S) (x : E)
    (hfx : ScaledThirdJet C S f x) (hgx : ScaledThirdJet C S g x) :
    ‖iteratedFDeriv ℝ 3 (fun y => f y*g y) x‖≤8*C^2*S := by
  have hh := norm_iteratedFDeriv_mul_le (n := 3) hf hg x (show (3:WithTop ℕ∞)≤3 by decide)
  norm_num [Finset.sum_range_succ,norm_iteratedFDeriv_zero] at hh
  change ‖iteratedFDeriv ℝ 3 (fun y => f y*g y) x‖≤
    ‖f x‖*‖iteratedFDeriv ℝ 3 g x‖+3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
      3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 3 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at hh
  rw [norm_iteratedFDeriv_zero] at hh
  obtain ⟨hf0,hf1,hf2,hf3⟩ := hfx
  obtain ⟨hg0,hg1,hg2,hg3⟩ := hgx
  apply hh.trans
  calc
    _ ≤ C*(C*S)+3*C*C+3*C*C+(C*S)*C := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hS (sq_nonneg C)]

end General

def firstOrderJetConstant : ℝ := 44*completionDerivativeBound

theorem firstOrderJetConstant_ge_one : 1≤firstOrderJetConstant := by
  norm_num [firstOrderJetConstant,completionDerivativeBound]

variable {d : ℕ}

theorem firstOrderBlockCompletion_jet (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ScaledThirdJet firstOrderJetConstant (Real.sqrt d) (firstOrderBlockCompletion θ) x := by
  refine ⟨?_,?_,?_,firstOrderBlockCompletion_third_bound θ hd x⟩
  · rw [Real.norm_eq_abs,abs_of_nonneg (firstOrderBlockCompletion_mem θ x).1]
    exact (firstOrderBlockCompletion_mem θ x).2.trans firstOrderJetConstant_ge_one
  · rw [norm_first_iteratedFDeriv,←norm_gradient_eq_fderiv]
    exact (firstOrderBlockCompletion_gradient_bound θ hd x).trans (by norm_num [firstOrderJetConstant,completionDerivativeBound])
  · rw [←norm_fderiv_gradient]
    exact (firstOrderBlockCompletion_hessian_bound θ hd x).trans (by norm_num [firstOrderJetConstant,completionDerivativeBound])

theorem firstOrderBlockPotential_jet (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ScaledThirdJet firstOrderJetConstant (Real.sqrt d) (firstOrderBlockPotential θ) x := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [Real.norm_eq_abs]
    have hh := firstOrderBlockPotential_range θ x
    apply (abs_le.mpr ⟨hh.1,hh.2.trans (by norm_num : (-2:ℝ)≤10)⟩).trans
    norm_num [firstOrderJetConstant,completionDerivativeBound]
  · rw [norm_first_iteratedFDeriv,←norm_gradient_eq_fderiv]
    exact (firstOrderBlockPotential_gradient_bound θ hd x).trans (by norm_num [firstOrderJetConstant,completionDerivativeBound])
  · rw [←norm_fderiv_gradient]
    exact (firstOrderBlockPotential_hessian_bound θ hd x).trans (by norm_num [firstOrderJetConstant,completionDerivativeBound])
  · exact (firstOrderBlockPotential_third_bound θ hd x).trans
      (mul_le_mul_of_nonneg_right (by norm_num [firstOrderJetConstant,completionDerivativeBound]) (Real.sqrt_nonneg (d:ℝ)))

end
end SecondOrder
