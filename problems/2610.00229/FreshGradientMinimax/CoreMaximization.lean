import FreshGradientMinimax.CoreProtection

/-! Exact global maximization of the actual protected square-link objective.
The witness is in the clip's linear region, and capping leaves it unchanged. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem coreInteraction_full_upper {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) (y : Euclid dy) :
    coreInteraction V (2 * μ * t) (32 * t) (fun _ => 1) u y ≤
      2 * μ * t * ‖coreLinks u‖ * ‖y‖ := by
  have hn := (clipVector_norm_le (by positivity : 0 < 32 * t) (frameCoordinates V y)).trans
    (frameCoordinates_norm_bound V y)
  have h := (real_inner_le_norm (clipVector (32 * t) (frameCoordinates V y)) (coreLinks u)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  unfold coreInteraction weightedCoreLinks
  rw [coordinateMultiplier_one]
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * μ * t)
  nlinarith only [hh]

theorem coreProtectedObjective_upper {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) (y : Euclid dy) :
    coreProtectedObjective V μ t u y ≤ (μ * t ^ 2) * coreChain u := by
  have hcap := smoothMaximum_ge_left (coreCapHeight_pos n hμ ht)
    (coreProtectedQ V μ t (fun _ => 1) u y) (coreProtectedWall n μ t y)
  change coreProtectedQ V μ t (fun _ => 1) u y ≤ coreProtectedCap V μ t (fun _ => 1) u y at hcap
  have hi := coreInteraction_full_upper V hμ ht u y
  have hsq := mul_nonneg hμ.le (sq_nonneg (‖y‖ - t * ‖coreLinks u‖))
  rw [coreChain_seed_links_identity]
  unfold coreProtectedObjective coreProtectedQ at *
  nlinarith only [hcap, hi, hsq]

theorem coreDualWitness_value {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) :
    coreProtectedObjective V μ t u (coreDualWitness V t u) = (μ * t ^ 2) * coreChain u := by
  rw [coreProtectedObjective, coreDualWitness_cap V hμ ht u, coreProtectedQ,
    coreDualWitness_interaction V μ ht u, coreDualWitness_norm_sq, coreChain_seed_links_identity]
  ring

theorem coreProtected_exact_max {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) :
    IsGreatest (Set.range (coreProtectedObjective V μ t u)) ((μ * t ^ 2) * coreChain u) := by
  refine ⟨⟨coreDualWitness V t u, coreDualWitness_value V hμ ht u⟩, ?_⟩
  rintro z ⟨y, rfl⟩
  exact coreProtectedObjective_upper V hμ ht u y

theorem coreProtected_sup_value {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) :
    sSup (Set.range (coreProtectedObjective V μ t u)) = (μ * t ^ 2) * coreChain u :=
  (coreProtected_exact_max V hμ ht u).csSup_eq

theorem coreDualWitness_zero {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (t : ℝ) :
    coreDualWitness V t (0 : Euclid (n + 1)) = 0 := by
  simp only [coreDualWitness, coreLinks_zero, smul_zero, map_zero]

theorem coreScale_sq {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam) :
    μ * Real.sqrt (lam / μ) ^ 2 = lam := by
  rw [Real.sq_sqrt (div_nonneg hlam hμ.le)]
  field_simp

theorem coreScale_amplitude {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam) :
    μ * Real.sqrt (lam / μ) = Real.sqrt (μ * lam) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (mul_nonneg hμ.le hlam)]
  calc
    _ = μ * (μ * Real.sqrt (lam / μ) ^ 2) := by ring
    _ = _ := by rw [coreScale_sq hμ hlam]

def paperCoreObjective {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (μ lam : ℝ) : Euclid (n + 1) → Euclid dy → ℝ :=
  coreProtectedObjective V μ (Real.sqrt (lam / μ))

theorem coreProtected_paper_formula {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (u : Euclid (n + 1)) (y : Euclid dy) :
    paperCoreObjective V μ lam u y = lam * coreSeed u - μ / 2 * ‖y‖ ^ 2 -
      smoothMaximum (768 * (n + 1 : ℝ) * lam)
        (μ / 2 * ‖y‖ ^ 2 - coreInteraction V (2 * Real.sqrt (μ * lam))
          (32 * Real.sqrt (lam / μ)) (fun _ => 1) u y)
        (2 * μ * ‖y‖ ^ 2 - 4 * (768 * (n + 1 : ℝ) * lam)) := by
  have hH : coreCapHeight n μ (Real.sqrt (lam / μ)) = 768 * (n + 1 : ℝ) * lam := by
    unfold coreCapHeight
    calc
      _ = (768 * (n + 1 : ℝ)) * (μ * Real.sqrt (lam / μ) ^ 2) := by ring
      _ = _ := by rw [coreScale_sq hμ hlam.le]
  have ha : 2 * μ * Real.sqrt (lam / μ) = 2 * Real.sqrt (μ * lam) := by
    rw [mul_assoc, coreScale_amplitude hμ hlam.le]
  simp only [paperCoreObjective, coreProtectedObjective, coreProtectedCap, coreProtectedQ,
    coreProtectedWall, hH, coreScale_sq hμ hlam.le, ha]

theorem core_C2_exact_max {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (u : Euclid (n + 1)) :
    IsGreatest (Set.range (paperCoreObjective V μ lam u)) (lam * coreChain u) := by
  have h := coreProtected_exact_max V hμ (Real.sqrt_pos.mpr (div_pos hlam hμ)) u
  simpa only [paperCoreObjective, coreScale_sq hμ hlam.le] using h

end FreshGradientMinimax

