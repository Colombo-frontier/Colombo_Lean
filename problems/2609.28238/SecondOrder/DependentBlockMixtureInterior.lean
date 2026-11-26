import SecondOrder.DependentBlockGateEnergies
import SecondOrder.BlockMixtureInterior

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

/-- Interior form of the selector estimate, allowing any finite-state selection
of payload functions. Constants are independent of the number of blocks. -/
theorem dependentBlockMixture_interior (p : (i : ι) → E i → ℝ)
    (V : (ι → Bool) → PiLp 2 E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ w, ContDiff ℝ 2 (V w))
    (x : PiLp 2 E) (hp0 : ∀ i, 0 < p i (x i)) (hp1 : ∀ i, p i (x i) < 1)
    (v₀ v₁ v₂ ell h : ℝ) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (hell : 0 ≤ ell) (hh : 0 ≤ h)
    (hval : ∀ w, |V w x| ≤ v₀) (hder : ∀ w, ‖gradient (V w) x‖ ≤ v₁)
    (hsecond : ∀ w, ‖fderiv ℝ (gradient (V w)) x‖ ≤ v₂)
    (hF : ∀ i, ‖gradient (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (gradient (p i)) (x i)‖ ≤ h) :
    let N := bernoulliMixture (fun i (y : PiLp 2 E) => p i (y i)) V
    ContDiff ℝ 2 N ∧ |N x| ≤ v₀ ∧
      ‖gradient N x‖ ≤ v₁+v₀*ell ∧
      ‖fderiv ℝ (gradient N) x‖ ≤ v₂+2*v₁*ell+2*v₀*(h+ell^2) := by
  letI : NormedSpace ℝ (PiLp 2 E) := inferInstance
  let q := fun i (y : PiLp 2 E) => p i (y i)
  have hq (i : ι) : ContDiff ℝ 2 (q i) := (hp i).comp (dependentBlockProj (E := E) i).contDiff
  have hder' (w : ι → Bool) : ‖fderiv ℝ (V w) x‖ ≤ v₁ := by
    simpa only [norm_gradient_eq_fderiv] using hder w
  have hsecond' (w : ι → Bool) : ‖fderiv ℝ (fderiv ℝ (V w)) x‖ ≤ v₂ := by
    simpa only [norm_hessian_eq_second_fderiv] using hsecond w
  have hF' (i : ι) : ‖fderiv ℝ (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)) := by
    simpa only [norm_gradient_eq_fderiv] using hF i
  have hH' (i : ι) : ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ≤ h := by
    simpa only [norm_hessian_eq_second_fderiv] using hH i
  have hb := bernoulliMixture_operator_bounds q V hq hV x hp0 hp1
    v₀ v₁ v₂ ell h hv₀ hv₁ hv₂ hell hh hval hder' hsecond'
    (dependentBlockGate_fisher_energy p hp x hp0 hp1 ell hF') (dependentBlockGate_second_energy p hp x h hh hH')
  refine ⟨contDiff_bernoulliMixture q V hq hV, ?_, ?_, ?_⟩
  · have he : bernoulliMixture q V x =
        pmfMean (bernoulliProduct (fun i => q i x) (fun i => (hp0 i).le) (fun i => (hp1 i).le))
          (fun w => V w x) := by
      simp only [bernoulliMixture, pmfMean, smul_eq_mul, ← bernoulliDensity_eq_toReal]
    rw [he]
    exact (abs_pmfMean_le _ _).trans (pmfMean_le_const _ v₀ hval)
  · simpa only [norm_gradient_eq_fderiv] using hb.1
  · simpa only [norm_hessian_eq_second_fderiv] using hb.2

end
end SecondOrder
