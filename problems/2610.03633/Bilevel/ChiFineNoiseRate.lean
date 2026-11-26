import Bilevel.ChiFineCouplingCore
import Bilevel.ChiFineParameterBudget
import Bilevel.ChiHierarchySignal

/-! The finest normal width yields the actual informative gradient scale
epsilon²/(L theta kappa³). The force identity is compatible with either
the narrow rec geometry or independent macro/middle widths. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ZeroChainSchedule

theorem fine_informative_amplitude {μ θ ell β dn Cf c Bs : ℝ}
    (hμ : 0 < μ) (hθ : 0 < θ) (hell : 0 < ell) (hβ : 0 < β) (hdn : 0 < dn)
    (_hCf : 0 < Cf) (hc : 0 < c) (hBs : 0 ≤ Bs) (J : ℕ)
    (hv : 1 ≤ fineParameter (θ*μ) (3*μ/2) ell dn Cf J) :
    4*μ*(2*SmallGapLiftSupport.C*Bs^(J+2)*ell*β*
      width c β (fineParameter (θ*μ) (3*μ/2) ell dn Cf J)
        (levels (fineParameter (θ*μ) (3*μ/2) ell dn Cf J))/dn) ≤
      12*SmallGapLiftSupport.C*Real.exp 2*c*Bs^(J+2)*Cf^(J+1)*((J:ℝ)+1)*μ*(ell*β)^2/(θ*dn^2) := by
  have hw := (final_width_bounds c β _ hc.le hβ.le hv).2
  have hC := SmallGapLiftSupport.C_pos
  have hh := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ 8*μ*SmallGapLiftSupport.C*Bs^(J+2)*ell*β/dn by positivity)
  have hJ : (0:ℝ) < (J:ℝ)+1 := by positivity
  calc
    _ ≤ (8*μ*SmallGapLiftSupport.C*Bs^(J+2)*ell*β/dn)*
        (Real.exp 2*c*β/fineParameter (θ*μ) (3*μ/2) ell dn Cf J) := by
      convert hh using 1
      ring
    _ = _ := by unfold fineParameter; field_simp; ring

theorem fine_informative_source_rate {L μ κ θ ell β Cf c Bs Cb ε t : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hκ : 0 < κ) (hθ : 0 < θ)
    (hell : 0 < ell) (hβ : 0 < β) (hCf : 0 < Cf) (hc : 0 < c) (hBs : 0 ≤ Bs)
    (ht : 0 < t) (hμeq : μ=L/κ) (J : ℕ) (hJ : 1 ≤ J)
    (hforce : ell*β=Cb*ε/((κ/6)*t^J))
    (hv : 1 ≤ fineParameter (θ*μ) (3*μ/2) ell (normalCoefficient L J) Cf J) :
    4*μ*(2*SmallGapLiftSupport.C*Bs^(J+2)*ell*β*
      width c β (fineParameter (θ*μ) (3*μ/2) ell (normalCoefficient L J) Cf J)
        (levels (fineParameter (θ*μ) (3*μ/2) ell (normalCoefficient L J) Cf J))/normalCoefficient L J) ≤
      (13824*SmallGapLiftSupport.C*Real.exp 2*c*Bs^(J+2)*Cf^(J+1)*(J:ℝ)*((J:ℝ)+1)*Cb^2/t^(2*J))*
        (ε^2/(L*θ*κ^3)) := by
  apply (fine_informative_amplitude hμ hθ hell hβ (normalCoefficient_pos hL hJ) hCf hc hBs J hv).trans_eq
  rw [hforce,hμeq]
  have hs : (Real.sqrt (2*(J:ℝ)))^2=2*(J:ℝ) := Real.sq_sqrt (by positivity)
  have htp : t^(2*J)=(t^J)^2 := by rw [Nat.mul_comm 2 J,pow_mul]
  rw [htp]
  unfold normalCoefficient
  simp only [div_pow,mul_pow,hs]
  field_simp
  ring

end Bilevel.ChiExtensionCalibration
