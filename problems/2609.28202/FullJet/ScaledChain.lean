import FullJet.ChainAverage
import FullJet.ChainGradient

open scoped ContDiff BigOperators

namespace FullJet

section Scaling
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Fréchet derivative scaling bound for a smooth function. -/
theorem scaled_iteratedFDeriv_bound {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (H α β : ℝ) (hH : 0 ≤ H) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ H) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => α * f (β • y)) x‖ ≤ α * β ^ k * H := by
  let L : E →L[ℝ] E := β • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ β := by
    calc
      _ = |β| * ‖ContinuousLinearMap.id ℝ E‖ := by
        change ‖β • ContinuousLinearMap.id ℝ E‖ = _
        simpa only [Real.norm_eq_abs] using norm_smul β (ContinuousLinearMap.id ℝ E)
      _ ≤ β * 1 := by
        rw [abs_of_nonneg hβ]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) hβ
      _ = β := mul_one _
  have horder : (k : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)
  have hc := (hf.comp L.contDiff).of_le horder
  change ‖iteratedFDeriv ℝ k (fun y => α • (f ∘ L) y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt]
  have hn := norm_smul α (iteratedFDeriv ℝ k (f ∘ L) x)
  rw [hn, Real.norm_eq_abs, abs_of_nonneg hα,
    L.iteratedFDeriv_comp_right hf x horder]
  have hb := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  have hp : (∏ _l : Fin k, ‖L‖) ≤ β ^ k := by
    simpa using pow_le_pow_left₀ (norm_nonneg L) hL k
  have hb' : ‖(iteratedFDeriv ℝ k f (L x)).compContinuousLinearMap (fun _ => L)‖ ≤ H * β ^ k :=
    hb.trans (mul_le_mul (hbound _) hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hH)
  exact (mul_le_mul_of_nonneg_left hb' hα).trans_eq (by ring)

theorem average_rescale {n : ℕ} (f : Fin n → E → ℝ) (α β : ℝ) (x : E) :
    average (fun i y => α * f i (β • y)) x = α * average f (β • x) := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem norm_fderiv_rescale {f : E → ℝ} (hf : Differentiable ℝ f)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (x : E) :
    ‖fderiv ℝ (fun y => α * f (β • y)) x‖ = α * β * ‖fderiv ℝ f (β • x)‖ := by
  let L : E →L[ℝ] E := β • ContinuousLinearMap.id ℝ E
  have hc := (hf (β • x)).hasFDerivAt.comp x L.hasFDerivAt
  have h : HasFDerivAt (fun y => α * f (β • y)) ((α * β) • fderiv ℝ f (β • x)) x := by
    convert hc.const_mul α using 1
    ext v
    simp [L, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul, mul_assoc]
  rw [h.fderiv]
  have hn := norm_smul (α * β) (fderiv ℝ f (β • x))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hα hβ)] using hn

end Scaling

section Chain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℕ}

noncomputable def scaledComponentChain (θ s : Fin (T + 1) → E) (ρ lam α β : ℝ)
    (x : BlockSpace T E) : ℝ := α * componentChain θ s ρ lam (β • x)

theorem scaledComponentChain_contDiff (θ s : Fin (T + 1) → E) (ρ lam α β : ℝ) :
    ContDiff ℝ ∞ (scaledComponentChain θ s ρ lam α β) :=
  contDiff_const.mul ((componentChain_contDiff θ s ρ lam).comp
    (contDiff_const.smul contDiff_id))

theorem scaledComponentChain_derivative_bound (θ s : Fin (T + 1) → E)
    (hθ : ∀ j, ‖θ j‖ ≤ 1) (hs : ∀ j, ‖s j‖ ≤ 1)
    (ρ lam α β : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (k : ℕ) (hk : 3 ≤ k) (x : BlockSpace T E) :
    ‖iteratedFDeriv ℝ k (scaledComponentChain θ s ρ lam α β) x‖ ≤
      α * β ^ k * (chainDerivativeBound k / ρ) :=
  scaled_iteratedFDeriv_bound (componentChain_contDiff θ s ρ lam) k
    (chainDerivativeBound k / ρ) α β (div_nonneg (chainDerivativeBound_nonneg k) hρ.le)
    hα hβ (fun z => componentChain_derivative_bound θ s hθ hs ρ lam hρ hρ1 k hk z) x

/-- The scaled, finite-sum hard chain belongs to the actual target function class.
Only construction constraints and the chosen numerical budgets are premises. -/
theorem scaledChain_admissible {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p)
    (θ : Fin (T + 1) → E) (s : Fin n → Fin (T + 1) → E)
    (hθ : ∀ j, ‖θ j‖ ≤ 1) (hs : ∀ i j, ‖s i j‖ ≤ 1)
    (ρ lam α β Δ L : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hlam : 0 ≤ lam) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (htable : ∀ j, ∑ i, s i j = ((n : ℝ) * ρ) • θ j)
    (hgap : α * (2 * (T + 1 : ℕ)) ≤ Δ)
    (hsmooth : α * β ^ (p + 1) * (chainDerivativeBound (p + 1) / ρ) ≤ L) :
    Admissible p n Δ L (fun i => scaledComponentChain θ (s i) ρ lam α β) := by
  have hC : 0 ≤ α * β ^ (p + 1) * (chainDerivativeBound (p + 1) / ρ) :=
    mul_nonneg (mul_nonneg hα (pow_nonneg hβ _))
      (div_nonneg (chainDerivativeBound_nonneg _) hρ.le)
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro i
    exact (scaledComponentChain_contDiff θ (s i) ρ lam α β).of_le (by
      exact_mod_cast (show (p : ℕ∞) ≤ ⊤ from le_top))
  · intro i x y
    have h := component_smoothness_of_bound p (scaledComponentChain_contDiff θ (s i) ρ lam α β)
      (α * β ^ (p + 1) * (chainDerivativeBound (p + 1) / ρ)) 1 hC zero_lt_one
      (fun z => by
        simpa only [div_one] using
          (scaledComponentChain_derivative_bound θ (s i) hθ (hs i) ρ lam α β hρ hρ1 hα hβ
            (p + 1) (by omega) z)) x y
    simp only [div_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hsmooth (norm_nonneg _))
  · intro x
    change average (fun i y => α * componentChain θ (s i) ρ lam (β • y)) 0 -
      average (fun i y => α * componentChain θ (s i) ρ lam (β • y)) x ≤ Δ
    rw [average_rescale, average_rescale, smul_zero,
      componentChain_average hn θ s ρ lam hρ.ne' htable,
      componentChain_average hn θ s ρ lam hρ.ne' htable, ← mul_sub]
    exact (mul_le_mul_of_nonneg_left (baseChain_gap θ hθ lam hlam (β • x)) hα).trans hgap

/-- The unfinished-stage barrier for the actual scaled finite-sum objective. -/
theorem scaledChain_gradient_lower_bound [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    (θ : Fin (T + 1) → E) (s : Fin n → Fin (T + 1) → E)
    (hθ : ∀ j, ‖θ j‖ = 1) (ρ α β : ℝ) (hρ : ρ ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (htable : ∀ j, ∑ i, s i j = ((n : ℝ) * ρ) • θ j)
    (x : BlockSpace T E) (hunfinished : ∃ j, alignment (θ j) ((β • x) j) < 9 / 32) :
    α * β / 4 ≤ ‖gradient (average (fun i => scaledComponentChain θ (s i) ρ (33 / 16) α β)) x‖ := by
  have heq : average (fun i => scaledComponentChain θ (s i) ρ (33 / 16) α β) =
      fun y => α * baseChain θ (33 / 16) (β • y) := by
    funext y
    change average (fun i z => α * componentChain θ (s i) ρ (33 / 16) (β • z)) y = _
    rw [average_rescale, componentChain_average hn θ s ρ (33 / 16) hρ htable]
  rw [heq, gradient, LinearIsometryEquiv.norm_map]
  rw [norm_fderiv_rescale (by
    rw [baseChain_eq_componentChain]
    exact (componentChain_contDiff θ θ 1 (33 / 16)).differentiable (by simp)) α β hα hβ]
  have h := mul_le_mul_of_nonneg_left (baseChain_fderiv_lower_bound θ hθ (β • x) hunfinished)
    (mul_nonneg hα hβ)
  simpa only [div_eq_mul_inv, one_mul] using h

end Chain

end FullJet
