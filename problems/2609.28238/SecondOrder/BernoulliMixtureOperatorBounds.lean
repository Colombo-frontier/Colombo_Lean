import SecondOrder.BernoulliMixtureBounds

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem secondBilinear_abs_le {f : E → ℝ} (x u v : E) :
    |secondBilinear f x u v| ≤ ‖fderiv ℝ (fderiv ℝ f) x‖*‖u‖*‖v‖ := by
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x u‖*‖v‖ := (fderiv ℝ (fderiv ℝ f) x u).le_opNorm v
    _ ≤ _ := mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ f) x).le_opNorm u) (norm_nonneg v)

/-- An interior finite-mixture estimate whose constants have no cardinality
factor. The two gate hypotheses are the aggregate Fisher and Hessian energies. -/
theorem bernoulliMixture_operator_bounds (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ w, ContDiff ℝ 2 (V w))
    (x : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1)
    (v₀ v₁ v₂ ell h : ℝ) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (hell : 0 ≤ ell) (hh : 0 ≤ h)
    (hval : ∀ w, |V w x| ≤ v₀) (hder : ∀ w, ‖fderiv ℝ (V w) x‖ ≤ v₁)
    (hsecond : ∀ w, ‖fderiv ℝ (fderiv ℝ (V w)) x‖ ≤ v₂)
    (hF : ∀ u, bernoulliFisherEnergy (fun i => p i x) (fun i => fderiv ℝ (p i) x u) ≤ ell^2*‖u‖^2)
    (hH : ∀ u v, (∑ i, |secondBilinear (p i) x u v|) ≤ h*‖u‖*‖v‖) :
    ‖fderiv ℝ (bernoulliMixture p V) x‖ ≤ v₁+v₀*ell ∧
    ‖fderiv ℝ (fderiv ℝ (bernoulliMixture p V)) x‖ ≤ v₂+2*v₁*ell+2*v₀*(h+ell^2) := by
  have hs (u : E) :
      Real.sqrt (bernoulliFisherEnergy (fun i => p i x) (fun i => fderiv ℝ (p i) x u)) ≤ ell*‖u‖ := by
    apply (Real.sqrt_le_iff).2
    exact ⟨mul_nonneg hell (norm_nonneg u), by simpa only [mul_pow] using hF u⟩
  have hd (w : ι → Bool) (u : E) : |fderiv ℝ (V w) x u| ≤ v₁*‖u‖ :=
    ((fderiv ℝ (V w) x).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hder w) (norm_nonneg u))
  have hd2 (w : ι → Bool) (u v : E) : |secondBilinear (V w) x u v| ≤ v₂*‖u‖*‖v‖ :=
    (secondBilinear_abs_le x u v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hsecond w) (norm_nonneg u)) (norm_nonneg v))
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    calc
      _ ≤ v₁*‖u‖+v₀*Real.sqrt (bernoulliFisherEnergy (fun i => p i x) (fun i => fderiv ℝ (p i) x u)) :=
        bernoulliMixture_fderiv_abs_le p V hp hV x u hp0 hp1 v₀ (v₁*‖u‖) hv₀ hval (fun w => hd w u)
      _ ≤ v₁*‖u‖+v₀*(ell*‖u‖) := add_le_add_left (mul_le_mul_of_nonneg_left (hs u) hv₀) _
      _ = _ := by ring
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hh0 := bernoulliMixture_second_abs_le p V hp hV x u v hp0 hp1
      v₀ (v₁*‖u‖) (v₁*‖v‖) (v₂*‖u‖*‖v‖) hv₀ (by positivity) (by positivity)
      hval (fun w => hd w u) (fun w => hd w v) (fun w => hd2 w u v)
    change |secondBilinear (bernoulliMixture p V) x u v| ≤ _
    apply hh0.trans
    calc
      _ ≤ v₂*‖u‖*‖v‖ + (v₁*‖u‖)*(ell*‖v‖) + (v₁*‖v‖)*(ell*‖u‖) +
          v₀*(2*(h*‖u‖*‖v‖)+2*(ell*‖u‖)*(ell*‖v‖)) := by
        gcongr
        · exact hs v
        · exact hs u
        · exact hH u v
        · exact hs u
        · exact hs v
      _ = _ := by ring

end
end SecondOrder
