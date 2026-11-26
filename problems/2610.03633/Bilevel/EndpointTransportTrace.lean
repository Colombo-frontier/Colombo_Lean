import Bilevel.EndpointTransportResponse

/-! Exact endpoint readouts and radial-penalty substitution for the full-vector
wrapper, valid for every ambient vector. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse

open EndpointTransportMatrix RadialWrapper

theorem response_norm_ratio {n D : ℕ} (δ c R : ℝ) (Q : Rotations n D) (v : Block D) :
    ‖physicalResponse δ c Q v‖^2 / (gamma n * R)^2 =
      ‖gain n δ c • v‖^2 / R^2 := by
  simp only [physicalResponse_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hg : gamma n ≠ 0 := (gamma_positive n).ne'
  rw [mul_assoc]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hg)]

theorem response_wrapper_scale {n D : ℕ} (δ c R : ℝ) (Q : Rotations n D)
    (v : Block D) :
    RadialWrapper.scale (gamma n * R) (physicalResponse δ c Q v) =
      RadialWrapper.scale R (gain n δ c • v) := by
  unfold RadialWrapper.scale
  rw [response_norm_ratio]

/-- The two physical endpoint readouts coincide with the old wrapped readout.
No membership in a hidden frame is assumed for either vector. -/
theorem response_exact_readouts {n D : ℕ} (δ c R : ℝ) (Q : Rotations n D)
    (v w : Block D) :
    2 * ⟪Q 0 w, (compress (gamma n * R) (physicalResponse δ c Q v)) 0⟫ =
      ⟪w, compress R (gain n δ c • v)⟫ ∧
    ⟪Q (Fin.last (n+1)) w,
      (compress (gamma n * R) (physicalResponse δ c Q v)) (Fin.last (n+1))⟫ =
      ⟪w, compress R (gain n δ c • v)⟫ := by
  have hfirst : (2:ℝ) * (c/δ * endpointColumn n (0 : Index n)) = gain n δ c := by
    rw [endpointColumn_first]
    unfold gain
    ring
  have hlast : c/δ * endpointColumn n (Fin.last (n+1)) = gain n δ c := by
    rw [endpointColumn_last]
    rfl
  unfold compress
  rw [response_wrapper_scale]
  simp only [physicalResponse, response,
    PiLp.smul_apply, WithLp.equiv_symm_pi_apply, smul_smul, real_inner_smul_right,
    LinearIsometryEquiv.inner_map_map]
  constructor
  · rw [← hfirst]
    ring
  · rw [hlast]

/-- The adjusted physical radial penalty is exactly the old penalty on graph. -/
theorem response_exact_bowl {n D : ℕ} (δ c ν R : ℝ) (Q : Rotations n D)
    (v : Block D) :
    bowl (ν / gamma n ^ 2) (gamma n * R) (physicalResponse δ c Q v) =
      bowl ν R (gain n δ c • v) := by
  unfold bowl
  rw [response_norm_ratio]
  have hg : gamma n ≠ 0 := (gamma_positive n).ne'
  field_simp
  ring

end Bilevel.EndpointTransportResponse
