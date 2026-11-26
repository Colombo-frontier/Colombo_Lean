import MatchingBounds1005.PathCalibration

/-! Explicit calibration with `ε = t³`. This positive reparameterization avoids
fractional-power conventions and gives exactly the manuscript's scaling. -/
noncomputable section
open scoped InnerProductSpace BigOperators

namespace MatchingBounds1005.EpsilonCalibration
open PathGreen

def amplitude (a t : ℝ) : ℝ := a / t
def curvature (a t : ℝ) : ℝ := 8192 * a * t ^ 2
def pathScale (a L t : ℝ) : ℝ := Real.sqrt (curvature a t / L)
def phaseCount (a t : ℝ) : ℕ := ⌊a / (1440 * 8192 * t ^ 4)⌋₊

variable (a L t : ℝ) (ha : 0 < a) (hL : 0 < L) (ht : 0 < t)

include ha ht in
theorem amplitude_pos : 0 < amplitude a t := div_pos ha ht

include ha ht in
theorem curvature_pos : 0 < curvature a t := by unfold curvature; positivity

include ha hL ht in
theorem pathScale_pos : 0 < pathScale a L t := by
  exact Real.sqrt_pos.mpr (div_pos (curvature_pos a t ha ht) hL)

include ha hL ht in
theorem pathScale_identity : L * pathScale a L t ^ 2 = curvature a t := by
  rw [pathScale, Real.sq_sqrt (div_pos (curvature_pos a t ha ht) hL).le]
  field_simp

include ht in
theorem amplitude_ge_one (hsmall : t ≤ a) : 1 ≤ amplitude a t := by
  exact (le_div_iff₀ ht).mpr (by simpa using hsmall)

include ha hL ht in
theorem pathScale_small (hsmall : curvature a t ≤ L / 16) : pathScale a L t ≤ 1 / 4 := by
  have heq := pathScale_identity a L t ha hL ht
  have hp := (pathScale_pos a L t ha hL ht).le
  have hq : pathScale a L t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    nlinarith only [heq, hsmall, hL]
  exact (sq_le_sq₀ hp (by norm_num)).mp hq

include ha ht in
theorem phaseCount_scaled : (phaseCount a t : ℝ) * (1440 * 8192 * t ^ 4) ≤ a := by
  have hf := Nat.floor_le (by positivity : 0 ≤ a / (1440 * 8192 * t ^ 4))
  exact (le_div_iff₀ (by positivity)).mp hf

include ht in
theorem phaseCount_pos (hsmall : 1440 * 8192 * t ^ 4 ≤ a) : 1 ≤ phaseCount a t := by
  apply Nat.le_floor
  norm_num only [Nat.cast_one]
  exact (le_div_iff₀ (by positivity)).mpr (by norm_num at hsmall ⊢; exact hsmall)

section Geometry
variable (hhsmall : pathScale a L t ≤ 1 / 4)

def geometry := actualBlockGeometry L (pathScale a L t) (amplitude a t) hL
  (pathScale_pos a L t ha hL ht) hhsmall (amplitude_pos a t ha ht)

local notation "G" => geometry a L t ha hL ht hhsmall

theorem calibrated_tau_upper : (G).tau ≤ 18 * 8192 * t ^ 4 / a := by
  have hb := (actual_tau_bounds L (pathScale a L t) (amplitude a t) hL
    (pathScale_pos a L t ha hL ht) hhsmall (amplitude_pos a t ha ht)).2
  change (G).tau ≤ _ at hb
  rw [pathScale_identity a L t ha hL ht] at hb
  convert hb using 1 <;> unfold curvature amplitude <;> field_simp <;> ring

theorem calibrated_kappa_upper : (G).kappa ≤ 2592 * 8192 * t ^ 4 / a := by
  have hb := actual_kappa_upper L (pathScale a L t) (amplitude a t) hL
    (pathScale_pos a L t ha hL ht) hhsmall (amplitude_pos a t ha ht)
  change (G).kappa ≤ _ at hb
  rw [pathScale_identity a L t ha hL ht] at hb
  convert hb using 1 <;> unfold curvature amplitude <;> field_simp <;> ring

theorem calibrated_nonlinear_budget : (G).tau * amplitude a t ^ 4 ≤ 18 * 8192 * a ^ 3 := by
  have htau := calibrated_tau_upper a L t ha hL ht hhsmall
  calc
    _ ≤ (18 * 8192 * t ^ 4 / a) * amplitude a t ^ 4 :=
      mul_le_mul_of_nonneg_right htau (by positivity)
    _ = _ := by unfold amplitude; field_simp; ring

theorem calibrated_phase_gap : 10 * (phaseCount a t : ℝ) * (G).tau ≤ 1 / 8 := by
  have htau := calibrated_tau_upper a L t ha hL ht hhsmall
  have hN := phaseCount_scaled a t ha ht
  have hm := mul_le_mul_of_nonneg_left htau (by positivity : 0 ≤ 10 * (phaseCount a t : ℝ))
  have heq : 10 * (phaseCount a t : ℝ) * (18 * 8192 * t ^ 4 / a) =
      ((phaseCount a t : ℝ) * (1440 * 8192 * t ^ 4)) / (8 * a) := by ring
  rw [heq] at hm
  apply hm.trans
  apply (div_le_iff₀ (by positivity : 0 < 8 * a)).mpr
  nlinarith only [hN]

theorem calibrated_gap (hsmall : 10368 * 8192 * t ^ 4 ≤ a) :
    10 * (phaseCount a t : ℝ) * (G).tau + (G).kappa / 2 ≤ 1 / 4 := by
  have hk := calibrated_kappa_upper a L t ha hL ht hhsmall
  have hk' := (le_div_iff₀ ha).mp hk
  have hκ : (G).kappa / 2 ≤ 1 / 8 := by nlinarith only [hk', hsmall, ha]
  have hphase := calibrated_phase_gap a L t ha hL ht hhsmall
  linarith

/-- Source `ana:eq:large-base-cert`, with the actual objective and gradient.
Here `ε=t³`; the bound is uniform in the number of blocks. -/
theorem calibrated_gradient (hr : t ≤ a) (n : ℕ)
    (z : BlockGeometry.BlockSpace (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) n)
    (htail : ⟪(G).a, z (Fin.last n)⟫_ℝ = 0) :
    32 * t ^ 3 ≤ ‖gradient ((G).euclideanObjective (amplitude a t) n) z‖ := by
  have hbase := actual_gradient_bound L (pathScale a L t) (amplitude a t) hL
    (pathScale_pos a L t ha hL ht) hhsmall (amplitude_pos a t ha ht)
    (amplitude a t) (amplitude_ge_one a t ht hr) n z htail
  change _ ≤ ‖gradient ((G).euclideanObjective (amplitude a t) n) z‖ at hbase
  rw [pathScale_identity a L t ha hL ht] at hbase
  have heq : curvature a t / (208 * amplitude a t) = (8192 / 208 : ℝ) * t ^ 3 := by
    unfold curvature amplitude
    field_simp
    ring
  rw [heq] at hbase
  have ht3 : 0 ≤ t ^ 3 := by positivity
  linarith

end Geometry
end MatchingBounds1005.EpsilonCalibration
