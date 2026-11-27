import SphereSmoothingSharp
import UpperPublicParameters

/-! Exact manuscript U2, including orthogonal assembly and public constants. -/
open MeasureTheory
open Task006.HaarRebalancing Task006.UpperPublicParameters
namespace Task006.Full.SampleInstance
variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

theorem orthogonalCentralSecant_gradient_error_sharp (hL : 0 ≤ L) (hR : 0 ≤ R)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) (hd : 0 < d)
    {x : Space d} (hx : ‖x‖ ≤ R-(ρ+δ)) (Q : OrthogonalGroup d) :
    ‖orthogonalReconstruct Q (fun i => centralSecant (ballSmooth I.objective ρ) x (column Q i) δ) -
      I.smoothedGradient hL hR ρ x‖ ≤ Real.sqrt d * ((d:ℝ)*L*δ/(2*ρ)) := by
  apply orthogonalReconstruct_error hd Q _ _
    (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hL) hδ.le) (by positivity))
  intro i
  rw [real_inner_comm]
  exact I.centralSecant_smoothedGradient_error_sharp hL hR hρ hρR hδ (by omega) hx
    ((orthonormal_column Q).norm_eq_one i).le

end Task006.Full.SampleInstance
namespace Task006.UpperPublicParameters

theorem public_finite_difference_scale_sharp {d : ℕ} {L R A : ℝ} (hd : 0 < d)
    (hR : 0 < R) (hA : 0 < A) :
    Real.sqrt d*((d:ℝ)*L*publicDelta d R A/(2*publicRho R A)) = L/(96*A) := by
  calc
    _ = (Real.sqrt d*((d:ℝ)*L*publicDelta d R A/publicRho R A))/2 := by ring
    _ = _ := by rw [public_finite_difference_scale hd hR hA]; ring

theorem public_U2_exact {d : ℕ} {L R eps A : ℝ} (hd : 0 < d) (hR : 0 < R)
    (heps : 0 < eps) (hA : 0 < A) (hAeq : A=L*R/eps) :
    2*R*(Real.sqrt d*((d:ℝ)*L*publicDelta d R A/(2*publicRho R A))) = eps/48 := by
  rw [public_finite_difference_scale_sharp hd hR hA]
  have hid : A*eps=L*R := (eq_div_iff heps.ne').1 hAeq
  field_simp [hA.ne']
  nlinarith [hid]

end Task006.UpperPublicParameters
