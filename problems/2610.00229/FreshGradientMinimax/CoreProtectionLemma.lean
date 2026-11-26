import FreshGradientMinimax.CoreCertificate

/-! Complete C.2: the explicit formula, exact maximization, strong concavity,
the common radial exterior, and the original derivative constants for every
paper truncation. Joint C1 and global gradient differences cover the joins. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem coreCapHeight_paper (n : ℕ) {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam) :
    coreCapHeight n μ (Real.sqrt (lam / μ)) = 768 * (n + 1 : ℝ) * lam := by
  unfold coreCapHeight
  calc
    _ = (768 * (n + 1 : ℝ)) * (μ * Real.sqrt (lam / μ) ^ 2) := by ring
    _ = _ := by rw [coreScale_sq hμ hlam]

theorem core_C2_cap_outside {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : 2 * Real.sqrt ((768 * (n + 1 : ℝ) * lam) / μ) ≤ ‖y‖) :
    coreProtectedCap V μ (Real.sqrt (lam / μ)) mask u y =
      (2 * μ * ‖y‖ ^ 2 - 4 * (768 * (n + 1 : ℝ) * lam)) - (768 * (n + 1 : ℝ) * lam) / 2 := by
  have hr : 2 * Real.sqrt (coreCapHeight n μ (Real.sqrt (lam / μ)) / μ) ≤ ‖y‖ := by
    simpa only [coreCapHeight_paper n hμ hlam.le] using hy
  have h := coreProtectedCap_outside_radius V hμ (Real.sqrt_pos.mpr (div_pos hlam hμ)) mask hm u y hr
  simpa only [coreProtectedWall, coreCapHeight_paper n hμ hlam.le] using h

theorem paperTruncatedCore_strongConcave {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (j : ℕ) (u : Euclid (n + 1)) :
    StrongConcaveGradient (paperTruncatedCore V μ lam j u) (gradient (paperTruncatedCore V μ lam j u)) μ := by
  have ht := Real.sqrt_pos.mpr (div_pos hlam hμ)
  have hg : gradient (paperTruncatedCore V μ lam j u) =
      maskedCoreGradY V μ (Real.sqrt (lam / μ)) (coreLinkPrefix n j) u :=
    funext (maskedCore_gradient_y V hμ ht (coreSeedPrefix n j) (coreLinkPrefix n j) u)
  rw [hg]
  exact maskedCore_strongConcave V hμ ht (coreSeedPrefix n j) (coreLinkPrefix n j) (coreLinkPrefix_bound n j) u

theorem lemma_C2 {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) :
    (∀ u : Euclid (n + 1),
      StrongConcaveGradient (paperCoreObjective V μ lam u) (gradient (paperCoreObjective V μ lam u)) μ ∧
      IsGreatest (Set.range (paperCoreObjective V μ lam u)) (lam * coreChain u)) ∧
    CoreDerivativeBounds (paperCoreObjective V μ lam) lam μ ∧
    (∀ j : ℕ, CoreDerivativeBounds (paperTruncatedCore V μ lam j) lam μ) ∧
    (∀ (j : ℕ) (u : Euclid (n + 1)) (y : Euclid dy),
      2 * Real.sqrt ((768 * (n + 1 : ℝ) * lam) / μ) ≤ ‖y‖ →
      coreProtectedCap V μ (Real.sqrt (lam / μ)) (coreLinkPrefix n j) u y =
        (2 * μ * ‖y‖ ^ 2 - 4 * (768 * (n + 1 : ℝ) * lam)) - (768 * (n + 1 : ℝ) * lam) / 2) ∧
    (∀ (u : Euclid (n + 1)) (y : Euclid dy),
      ‖fderiv ℝ (gradient (fun v => paperCoreObjective V μ lam v y)) u‖ ≤ 10 ^ 6 * lam ∧
      ‖fderiv ℝ (fun z => gradient (fun v => paperCoreObjective V μ lam v z) u) y‖ ≤ 2000 * Real.sqrt (μ * lam) ∧
      ‖fderiv ℝ (fun v => gradient (paperCoreObjective V μ lam v) y) u‖ ≤ 2000 * Real.sqrt (μ * lam) ∧
      ‖fderiv ℝ (gradient (paperCoreObjective V μ lam u)) y‖ ≤ 50 * μ) := by
  refine ⟨fun u => ⟨core_C2_strongConcave V hμ hlam u, core_C2_exact_max V hμ hlam u⟩,
    paperCore_derivative_bounds V hμ hlam, paperTruncatedCore_derivative_bounds V hμ hlam, ?_, ?_⟩
  · intro j u y hy
    exact core_C2_cap_outside V hμ hlam (coreLinkPrefix n j) (coreLinkPrefix_bound n j) u y hy
  · exact coreDerivativeBounds_hessian hlam.le hμ.le (paperCore_derivative_bounds V hμ hlam)

end FreshGradientMinimax
