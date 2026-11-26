import FreshGradientMinimax.PathParameters

/-! The paper-parameterized signed path family and its actual local primal
derivative approximation. All signals and cap parameters are explicit. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax

def pathHardObjective {n dy : ℕ} (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (k : ℕ)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) :
    NCObjective 1 dy L μ := by
  have hL : 0 < L := by linarith
  exact pathObjective V (pathSignsFromVertices (tailVertexSigns k s)) 0 (Fin.last n)
    L μ (4 * ε) (pathHardSignal L μ ε n) (pathHardFlatWidth L μ ε n) (pathHardRadius L μ ε n)
    hμ hκ (pathSignsFromVertices_abs (tailVertexSigns_sq k hs))
    (pathHardFlatWidth_pos hL hμ hε n).le (pathHardRadius_pos hL hμ hε n)

theorem pathHardObjective_initial_residual {n dy : ℕ} (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (k : ℕ)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) :
    ‖(pathHardObjective V k s L μ ε hμ hκ hε hs).gradY 0 0‖ = pathHardSignal L μ ε n := by
  have hL : 0 < L := by linarith
  simp only [pathHardObjective, pathObjective_initial_residual,
    abs_of_pos (pathHardSignal_pos hL hμ hε n)]

theorem pathHard_quadratic_gradient {n k : ℕ} (hk0 : 0 < k) (hkn : k ≤ n)
    {s L μ : ℝ} (hs : s ^ 2 = 1) (hL : 0 < L) (hμ : 0 < μ) (ε x : ℝ) :
    L / 4 * x + 4 * ε + L / 8 *
      normalInverse (pathIncidence (pathSignsFromVertices (tailVertexSigns (n := n + 1) k s)))
        μ (L / 8192) hμ (by positivity)
        (pathSignal 0 (Fin.last n) (L / 8) x (pathHardSignal L μ ε n)) 0 =
      pathHardSlope L μ hL hμ n * x + (4 + 2 * s) * ε := by
  simp only [pathSignal, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [normalPath_inverse_diagonal (tailVertexSigns_sq k hs) hμ (by positivity),
    signedPath_endpoint hk0 hkn hs hμ (by positivity)]
  change L / 4 * x + 4 * ε + L / 8 * ((L / 8 * x) *
    normalInverse (pathIncidence (fun _ : Fin (n + 2) => 1)) μ (L / 8192) hμ (by positivity)
      (EuclideanSpace.single 0 1) 0 + pathHardSignal L μ ε n * (s * pathTransmission μ (L / 8192) n)) = _
  calc
    _ = pathHardSlope L μ hL hμ n * x + 4 * ε +
        s * ((L / 8) * pathHardSignal L μ ε n * pathTransmission μ (L / 8192) n) := by
      unfold pathHardSlope; ring
    _ = _ := by rw [pathHardSignal_calibration hL hμ]; ring

theorem pathHardObjective_primalApproximation {n dy k : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (hk0 : 0 < k) (hkn : k ≤ n)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1)
    (hL : 0 < L) (x : Euclid 1)
    (hx : realCoord x ∈ Set.Icc (-8 * ε / pathHardSlope L μ hL hμ n) 0) :
    |realCoord ((pathHardObjective V k s L μ ε hμ hκ hε hs).primalGradient x) -
      (pathHardSlope L μ hL hμ n * realCoord x + (4 + 2 * s) * ε)| ≤ ε / 8 := by
  have hcore := pathHardSignal_core hL hμ hε (pathHardSlope_lower hL hμ n) hx
    (0 : Fin (n + 1)) (Fin.last n)
  have h := pathObjective_primalApproximation V (pathSignsFromVertices (tailVertexSigns k s))
    0 (Fin.last n) L μ (4 * ε) (pathHardSignal L μ ε n) (pathHardFlatWidth L μ ε n)
    (pathHardRadius L μ ε n) hμ hκ (pathSignsFromVertices_abs (tailVertexSigns_sq k hs))
    (pathHardFlatWidth_pos hL hμ hε n).le (pathHardRadius_pos hL hμ hε n) x hcore (by positivity)
  have he : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  rw [he, pathHardFlatWidth_error hL hμ, pathHard_quadratic_gradient hk0 hkn hs hL hμ] at h
  exact h

end FreshGradientMinimax
