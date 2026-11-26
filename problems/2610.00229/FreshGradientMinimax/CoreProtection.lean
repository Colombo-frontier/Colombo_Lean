import FreshGradientMinimax.CoreInteraction
import FreshGradientMinimax.SmoothMaximum

/-! The actual dual protection in C.2, parameterized by t = sqrt(lambda / mu).
Thus lambda = mu*t^2, a_s = 2*mu*t, and R_0 = 32*t. All radial terms use
the full ambient norm. The same wall and height work for every mask. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def coreCapHeight (n : ℕ) (μ t : ℝ) : ℝ := 768 * (n + 1 : ℝ) * μ * t ^ 2

def coreProtectedQ {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : ℝ :=
  μ / 2 * ‖y‖ ^ 2 - coreInteraction V (2 * μ * t) (32 * t) mask u y

def coreProtectedWall (n : ℕ) {dy : ℕ} (μ t : ℝ) (y : Euclid dy) : ℝ :=
  2 * μ * ‖y‖ ^ 2 - 4 * coreCapHeight n μ t

def coreProtectedCap {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : ℝ :=
  smoothMaximum (coreCapHeight n μ t) (coreProtectedQ V μ t mask u y) (coreProtectedWall n μ t y)

def coreProtectedObjective {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ)
    (u : Euclid (n + 1)) (y : Euclid dy) : ℝ :=
  (μ * t ^ 2) * coreSeed u - μ / 2 * ‖y‖ ^ 2 - coreProtectedCap V μ t (fun _ => 1) u y

def coreDualWitness {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (t : ℝ) (u : Euclid (n + 1)) : Euclid dy := V (t • coreLinks u)

theorem coreCapHeight_pos (n : ℕ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) :
    0 < coreCapHeight n μ t := by unfold coreCapHeight; positivity

theorem coreInteraction_height_bound {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy) :
    |coreInteraction V (2 * μ * t) (32 * t) mask u y| ≤ coreCapHeight n μ t := by
  have h := coreInteraction_bound V (by positivity : 0 ≤ 2 * μ * t)
    (by positivity : 0 < 32 * t) mask hm u y
  unfold coreCapHeight
  nlinarith only [h, mul_pos hμ (sq_pos_of_pos ht)]

theorem coreProtectedCap_outside {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : 4 * coreCapHeight n μ t ≤ μ * ‖y‖ ^ 2) :
    coreProtectedCap V μ t mask u y = coreProtectedWall n μ t y - coreCapHeight n μ t / 2 := by
  apply smoothMaximum_right (coreCapHeight_pos n hμ ht)
  have h := (abs_le.mp (coreInteraction_height_bound V hμ ht mask hm u y)).1
  unfold coreProtectedWall coreProtectedQ
  nlinarith only [hy, h]

theorem coreProtectedCap_outside_radius {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : 2 * Real.sqrt (coreCapHeight n μ t / μ) ≤ ‖y‖) :
    coreProtectedCap V μ t mask u y = coreProtectedWall n μ t y - coreCapHeight n μ t / 2 := by
  apply coreProtectedCap_outside V hμ ht mask hm u y
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.sqrt (coreCapHeight n μ t / μ)) hy 2
  have hr := Real.sq_sqrt (div_nonneg (coreCapHeight_pos n hμ ht).le hμ.le)
  have hmult := mul_le_mul_of_nonneg_left hs hμ.le
  have hid : μ * (coreCapHeight n μ t / μ) = coreCapHeight n μ t := by field_simp
  rw [mul_pow, hr] at hmult
  nlinarith only [hmult, hid]

theorem coreDualWitness_norm_sq {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (t : ℝ) (u : Euclid (n + 1)) : ‖coreDualWitness V t u‖ ^ 2 = t ^ 2 * ‖coreLinks u‖ ^ 2 := by
  simp only [coreDualWitness, V.norm_map, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem coreDualWitness_clip {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {t : ℝ} (ht : 0 < t) (u : Euclid (n + 1)) :
    clipVector (32 * t) (frameCoordinates V (coreDualWitness V t u)) = t • coreLinks u := by
  rw [coreDualWitness, frameCoordinates_frame]
  apply clipVector_identity (by positivity)
  intro i
  change |t * coreLinks u i| ≤ _
  rw [abs_mul, abs_of_pos ht]
  have h := mul_le_mul_of_nonneg_left (coreLinks_coordinate_bound u i) ht.le
  nlinarith only [h, ht]

theorem coreDualWitness_interaction {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (μ : ℝ) {t : ℝ} (ht : 0 < t) (u : Euclid (n + 1)) :
    coreInteraction V (2 * μ * t) (32 * t) (fun _ => 1) u (coreDualWitness V t u) =
      2 * μ * ‖coreDualWitness V t u‖ ^ 2 := by
  unfold coreInteraction weightedCoreLinks
  rw [coordinateMultiplier_one, coreDualWitness_clip V ht u, real_inner_smul_left,
    real_inner_self_eq_norm_sq, coreDualWitness_norm_sq]
  ring

theorem coreDualWitness_height {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) :
    24 * μ * ‖coreDualWitness V t u‖ ^ 2 ≤ coreCapHeight n μ t := by
  have h := mul_le_mul_of_nonneg_left (coreLinks_norm_sq_bound u)
    (by positivity : 0 ≤ μ * t ^ 2)
  rw [coreDualWitness_norm_sq]
  unfold coreCapHeight
  nlinarith only [h, mul_pos hμ (sq_pos_of_pos ht)]

theorem coreDualWitness_cap {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) :
    coreProtectedCap V μ t (fun _ => 1) u (coreDualWitness V t u) =
      coreProtectedQ V μ t (fun _ => 1) u (coreDualWitness V t u) := by
  apply smoothMaximum_left
  have h := coreDualWitness_height V hμ ht u
  have hH := (coreCapHeight_pos n hμ ht).le
  unfold coreProtectedWall coreProtectedQ
  rw [coreDualWitness_interaction V μ ht u]
  nlinarith only [h, hH]

end FreshGradientMinimax
