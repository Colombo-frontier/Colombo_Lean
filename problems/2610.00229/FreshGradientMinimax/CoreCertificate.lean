import FreshGradientMinimax.CoreTruncation
import FreshGradientMinimax.CoreJointRegularity

/-! Certificates of the actual derivatives with the constants stated in C.2.
These are proved properties of the explicit formulas, not construction inputs. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

structure CoreDerivativeBounds {n dy : ℕ} (f : Euclid (n + 1) → Euclid dy → ℝ) (lam μ : ℝ) : Prop where
  joint_contDiff : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => f z.1 z.2)
  u_norm : ∀ u y, ‖gradient (fun v => f v y) u‖ ≤ 8000 * lam * Real.sqrt (n + 1 : ℝ)
  uu_lipschitz : ∀ u v y, ‖gradient (fun a => f a y) u - gradient (fun a => f a y) v‖ ≤ 10 ^ 6 * lam * ‖u - v‖
  uy_lipschitz : ∀ u y z, ‖gradient (fun a => f a y) u - gradient (fun a => f a z) u‖ ≤
    2000 * Real.sqrt (μ * lam) * ‖y - z‖
  yu_lipschitz : ∀ u v y, ‖gradient (f u) y - gradient (f v) y‖ ≤ 2000 * Real.sqrt (μ * lam) * ‖u - v‖
  yy_lipschitz : ∀ u y z, ‖gradient (f u) y - gradient (f u) z‖ ≤ 50 * μ * ‖y - z‖

theorem maskedCore_derivative_bounds {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (hw : ∀ e, |w e| ≤ 1)
    (mask : Fin (n + n) → ℝ) (hm : ∀ i, |mask i| ≤ 1) :
    CoreDerivativeBounds (maskedCoreObjective V μ t w mask) (μ * t ^ 2) μ := by
  have ha : Real.sqrt (μ * (μ * t ^ 2)) = μ * t := by
    rw [show μ * (μ * t ^ 2) = (μ * t) ^ 2 by ring, Real.sqrt_sq (by positivity : 0 ≤ μ * t)]
  refine ⟨maskedCore_joint_contDiff V hμ ht w mask, ?_, ?_, ?_, ?_, ?_⟩
  · intro u y
    rw [maskedCore_gradient_u V hμ ht]
    exact maskedCoreGradU_norm V hμ ht w hw mask hm u y
  · intro u v y
    simp only [maskedCore_gradient_u V hμ ht]
    exact maskedCoreGradU_sub_u V hμ ht w hw mask hm u v y
  · intro u y z
    rw [ha]
    simp only [maskedCore_gradient_u V hμ ht, ← mul_assoc]
    exact maskedCoreGradU_sub_y V hμ ht w mask hm u y z
  · intro u v y
    rw [ha]
    simp only [maskedCore_gradient_y V hμ ht, ← mul_assoc]
    exact maskedCoreGradY_sub_u V hμ ht mask hm u v y
  · intro u y z
    simp only [maskedCore_gradient_y V hμ ht]
    exact maskedCoreGradY_sub_y V hμ ht mask hm u y z

theorem paperCore_derivative_bounds {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) : CoreDerivativeBounds (paperCoreObjective V μ lam) lam μ := by
  have h := maskedCore_derivative_bounds V hμ (Real.sqrt_pos.mpr (div_pos hlam hμ))
    ((WithLp.equiv 2 _).symm (fun _ : Fin n => (1 : ℝ))) (by intro e; norm_num)
    (fun _ => 1) (by intro e; norm_num)
  simpa only [maskedCore_full, coreScale_sq hμ hlam.le, paperCoreObjective] using h

theorem paperTruncatedCore_derivative_bounds {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (j : ℕ) :
    CoreDerivativeBounds (paperTruncatedCore V μ lam j) lam μ := by
  have h := maskedCore_derivative_bounds V hμ (Real.sqrt_pos.mpr (div_pos hlam hμ))
    (coreSeedPrefix n j) (coreSeedPrefix_bound n j) (coreLinkPrefix n j) (coreLinkPrefix_bound n j)
  simpa only [paperTruncatedCore, truncatedCoreObjective, coreScale_sq hμ hlam.le] using h

theorem coreDerivativeBounds_hessian {n dy : ℕ} {f : Euclid (n + 1) → Euclid dy → ℝ}
    {lam μ : ℝ} (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) (hf : CoreDerivativeBounds f lam μ)
    (u : Euclid (n + 1)) (y : Euclid dy) :
    ‖fderiv ℝ (gradient (fun v => f v y)) u‖ ≤ 10 ^ 6 * lam ∧
    ‖fderiv ℝ (fun z => gradient (fun v => f v z) u) y‖ ≤ 2000 * Real.sqrt (μ * lam) ∧
    ‖fderiv ℝ (fun v => gradient (f v) y) u‖ ≤ 2000 * Real.sqrt (μ * lam) ∧
    ‖fderiv ℝ (gradient (f u)) y‖ ≤ 50 * μ := by
  have huu : LipschitzWith ⟨10 ^ 6 * lam, by positivity⟩ (gradient (fun v => f v y)) :=
    lipschitzWith_iff_norm_sub_le.mpr (fun u v => hf.uu_lipschitz u v y)
  have huy : LipschitzWith ⟨2000 * Real.sqrt (μ * lam), by positivity⟩
      (fun z => gradient (fun v => f v z) u) :=
    lipschitzWith_iff_norm_sub_le.mpr (hf.uy_lipschitz u)
  have hyu : LipschitzWith ⟨2000 * Real.sqrt (μ * lam), by positivity⟩
      (fun v => gradient (f v) y) :=
    lipschitzWith_iff_norm_sub_le.mpr (fun u v => hf.yu_lipschitz u v y)
  have hyy : LipschitzWith ⟨50 * μ, by positivity⟩ (gradient (f u)) :=
    lipschitzWith_iff_norm_sub_le.mpr (hf.yy_lipschitz u)
  exact ⟨norm_fderiv_le_of_lipschitz ℝ huu, norm_fderiv_le_of_lipschitz ℝ huy,
    norm_fderiv_le_of_lipschitz ℝ hyu, norm_fderiv_le_of_lipschitz ℝ hyy⟩

end FreshGradientMinimax
