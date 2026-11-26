import FreshGradientMinimax.SignedPath
import FreshGradientMinimax.PathApproximation

/-! The paper's explicit signal, flatness, radius, and primal slope. The path
dimension is n+1, so the incidence has n+2 rows. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def pathTransmission (μ β : ℝ) (n : ℕ) : ℝ :=
  Real.sinh (pathTheta μ β) / (β * Real.sinh (((n : ℝ) + 2) * pathTheta μ β))

def pathHardSignal (L μ ε : ℝ) (n : ℕ) : ℝ :=
  2 * ε / ((L / 8) * pathTransmission μ (L / 8192) n)

def pathHardFlatWidth (L μ ε : ℝ) (n : ℕ) : ℝ :=
  ε * μ / (16 * (L / 8) * (L / 8192) * Real.sqrt (n + 2))

def pathHardRadius (L μ ε : ℝ) (n : ℕ) : ℝ := 8 * (pathHardSignal L μ ε n + 4 * ε) / μ

def pathHardSlope (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (n : ℕ) : ℝ :=
  L / 4 + (L / 8) ^ 2 * normalInverse (pathIncidence (fun _ : Fin (n + 2) => 1)) μ (L / 8192)
    hμ (by positivity) (EuclideanSpace.single 0 1) 0

theorem pathTransmission_pos {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) (n : ℕ) :
    0 < pathTransmission μ β n := by
  unfold pathTransmission
  rw [← positivePath_endpoint_entry hμ hβ n]
  exact positivePath_endpoint_positive hμ hβ n

theorem pathHardSignal_pos {L μ ε : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) (n : ℕ) :
    0 < pathHardSignal L μ ε n :=
  div_pos (by positivity) (mul_pos (by positivity) (pathTransmission_pos hμ (by positivity) n))

theorem pathHardSignal_calibration {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (ε : ℝ) (n : ℕ) :
    (L / 8) * pathHardSignal L μ ε n * pathTransmission μ (L / 8192) n = 2 * ε := by
  have ht := (pathTransmission_pos hμ (by positivity : 0 < L / 8192) n).ne'
  unfold pathHardSignal
  field_simp
  ring

theorem pathHardFlatWidth_pos {L μ ε : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) (n : ℕ) :
    0 < pathHardFlatWidth L μ ε n := by unfold pathHardFlatWidth; positivity

theorem pathHardFlatWidth_error {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (ε : ℝ) (n : ℕ) :
    (L / 8) * (2 * (L / 8192) * pathHardFlatWidth L μ ε n * Real.sqrt (n + 2) / μ) = ε / 8 := by
  have hs : Real.sqrt ((n : ℝ) + 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold pathHardFlatWidth
  field_simp
  ring

theorem pathHardRadius_pos {L μ ε : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) (n : ℕ) :
    0 < pathHardRadius L μ ε n := by
  have hM := pathHardSignal_pos hL hμ hε n
  unfold pathHardRadius
  positivity

theorem pathHardSlope_lower {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (n : ℕ) :
    L / 4 ≤ pathHardSlope L μ hL hμ n := by
  have hi := normalPath_diagonal_nonneg (fun _ : Fin (n + 2) => 1) hμ
    (show 0 ≤ L / 8192 by positivity) (0 : Fin (n + 1))
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hi)

theorem pathHardSlope_pos {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (n : ℕ) :
    0 < pathHardSlope L μ hL hμ n := (by positivity : 0 < L / 4).trans_le (pathHardSlope_lower hL hμ n)

theorem pathLocal_coupling_bound {L ε q x : ℝ} (hL : 0 < L) (hqL : L / 4 ≤ q)
    (hx : x ∈ Set.Icc (-8 * ε / q) 0) : (L / 8) * |x| ≤ 4 * ε := by
  have hq : 0 < q := (by positivity : 0 < L / 4).trans_le hqL
  have hx' : -(8 * ε / q) ≤ x := by convert hx.1 using 1; ring
  have hl : -x ≤ 8 * ε / q := by linarith only [hx']
  have h := (le_div_iff₀ hq).mp hl
  have hm := mul_le_mul_of_nonneg_right hqL (neg_nonneg.mpr hx.2)
  rw [abs_of_nonpos hx.2]
  nlinarith only [h, hm]

theorem pathHardSignal_core {n : ℕ} {L μ ε q x : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) (hqL : L / 4 ≤ q)
    (hx : x ∈ Set.Icc (-8 * ε / q) 0) (i j : Fin (n + 1)) :
    ‖pathSignal i j (L / 8) x (pathHardSignal L μ ε n)‖ ≤ μ * pathHardRadius L μ ε n := by
  have hM := pathHardSignal_pos hL hμ hε n
  have hn := pathSignal_norm i j (show 0 ≤ L / 8 by positivity) x (pathHardSignal L μ ε n)
  rw [abs_of_pos hM] at hn
  have hc := pathLocal_coupling_bound hL hqL hx
  have he : μ * pathHardRadius L μ ε n = 8 * (pathHardSignal L μ ε n + 4 * ε) := by
    unfold pathHardRadius; field_simp
  rw [he]
  linarith

end FreshGradientMinimax
