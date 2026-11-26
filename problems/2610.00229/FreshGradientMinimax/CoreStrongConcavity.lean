import FreshGradientMinimax.CoreCapDerivatives

/-! Strong concavity and stationary maximizers of the actual protected core. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem coreProtectedQ_convex {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) :
    ConvexOn ℝ Set.univ (coreProtectedQ V μ t mask u) := by
  exact quadratic_minus_smooth_convex
    (fun y => coreInteraction_hasFDerivAt_y V (2 * μ * t) (by positivity) mask u y)
    (scaledInteractionGradY_sub_y V hμ ht mask hm u) (by linarith : 3 * μ / 8 ≤ μ)

theorem coreProtectedWall_convex (n : ℕ) {dy : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) :
    ConvexOn ℝ Set.univ (@coreProtectedWall n dy μ t) := by
  have h := (half_quadratic_convex (E := Euclid dy) (μ := 4 * μ) (by positivity)).add_const
    (-(4 * coreCapHeight n μ t))
  convert h using 1
  funext y
  unfold coreProtectedWall
  simp only [Pi.add_apply]
  ring

theorem coreProtectedCap_convex {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) :
    ConvexOn ℝ Set.univ (coreProtectedCap V μ t mask u) :=
  smoothMaximum_comp_convex (coreCapHeight_pos n hμ ht)
    (coreProtectedQ_convex V hμ ht mask hm u) (coreProtectedWall_convex n hμ.le t)

theorem coreProtected_strongConcave {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) :
    StrongConcaveGradient (coreProtectedObjective V μ t u) (coreProtectedGradY V μ t u) μ := by
  have h := convex_penalty_strongConcave
    (coreProtectedCap_convex V hμ ht (fun _ => 1) (by intro i; norm_num) u)
    (coreProtectedCap_hasFDerivAt_y V hμ ht (fun _ => 1) u) μ ((μ * t ^ 2) * coreSeed u) 0
  unfold coreProtectedObjective coreProtectedGradY
  simpa only [inner_zero_left, add_zero,
    zero_sub, neg_smul] using h

theorem coreDualWitness_stationary {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) :
    coreProtectedGradY V μ t u (coreDualWitness V t u) = 0 := by
  apply gradient_zero_at_global_max _ (coreProtectedObjective_hasFDerivAt_y V hμ ht u _)
  intro y
  rw [coreDualWitness_value V hμ ht u]
  exact coreProtectedObjective_upper V hμ ht u y

theorem coreProtectedGradY_zero {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) : coreProtectedGradY V μ t 0 0 = 0 := by
  simpa only [coreDualWitness_zero] using coreDualWitness_stationary V hμ ht 0

theorem coreDualWitness_unique {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : ∀ z, coreProtectedObjective V μ t u z ≤ coreProtectedObjective V μ t u y) :
    y = coreDualWitness V t u := by
  apply strong_concave_maximum_unique hμ (coreProtected_strongConcave V hμ ht u)
    (coreProtectedObjective_hasFDerivAt_y V hμ ht u) y _ hy
  intro z
  rw [coreDualWitness_value V hμ ht u]
  exact coreProtectedObjective_upper V hμ ht u z

theorem core_C2_strongConcave {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (u : Euclid (n + 1)) :
    StrongConcaveGradient (paperCoreObjective V μ lam u) (gradient (paperCoreObjective V μ lam u)) μ := by
  have ht := Real.sqrt_pos.mpr (div_pos hlam hμ)
  have hg : gradient (paperCoreObjective V μ lam u) =
      coreProtectedGradY V μ (Real.sqrt (lam / μ)) u :=
    funext (coreProtectedObjective_gradient_y V hμ ht u)
  rw [hg]
  exact coreProtected_strongConcave V hμ ht u

theorem core_C2_gradient_y_zero {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) : gradient (paperCoreObjective V μ lam 0) 0 = 0 := by
  unfold paperCoreObjective
  rw [coreProtectedObjective_gradient_y V hμ (Real.sqrt_pos.mpr (div_pos hlam hμ))]
  exact coreProtectedGradY_zero V hμ (Real.sqrt_pos.mpr (div_pos hlam hμ))

end FreshGradientMinimax
