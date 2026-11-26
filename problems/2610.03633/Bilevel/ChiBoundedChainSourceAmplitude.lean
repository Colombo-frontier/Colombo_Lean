import Bilevel.ChiBoundedChainSourceCalibration

/-! The actual source local payload amplitude, including both receivers.
Radial composition preserves this uniform bound. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

def sourceAmplitudeConstant (A K ζ cn η : ℝ) : ℝ :=
  gaussianBound*cn+3*A*(3*ζ+η)+2*A*K*η^2/ζ

theorem source_payload_amplitude (A K ζ cn η lp hp r : ℝ) (n : ℕ)
    (hA : 0≤A) (hK : 0<K) (hζ : 0<ζ) (_hcn : 0<cn) (hη : 0<η)
    (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r)
    (hn : (n:ℝ)+1≤cn*r/η^2) (z : Space n) :
    |payload n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp (K*(η*(lp*hp))/(ζ*lp)) z|≤
      sourceAmplitudeConstant A K ζ cn η*(lp*hp^2) := by
  have hr0 : 0<r := by linarith
  have hvalue := payload_abs_bound n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp
    (K*(η*(lp*hp))/(ζ*lp)) (by positivity) hA (by positivity) (by positivity)
    (by positivity) hhp (by positivity) z
  have he : (cn*r/η^2)*((r*lp)*(η*hp/r)^2)=cn*(lp*hp^2) := by field_simp;ring
  have hc : ((n:ℝ)+1)*((r*lp)*(η*hp/r)^2)≤cn*(lp*hp^2) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right hn (by positivity)
  have hchain := mul_le_mul_of_nonneg_left hc gaussianBound_nonneg
  have hreceiver : (A*(3*(ζ*lp)*hp+η*(lp*hp)))*(3*hp)+
      (A*(η*(lp*hp)))*(2*(K*(η*(lp*hp))/(ζ*lp)))=
      (3*A*(3*ζ+η)+2*A*K*η^2/ζ)*(lp*hp^2) := by field_simp;ring
  unfold sourceAmplitudeConstant
  nlinarith only [hvalue,hchain,hreceiver]

theorem source_energy_ratio {lp hp r η : ℝ} (hr : 1≤r) :
    (r*lp)*(η*hp/r)^2=(η^2/r)*(lp*hp^2) := by
  have hr0 : 0<r := by linarith
  field_simp
  ring

theorem source_energy_ratio_le {lp hp r η : ℝ} (hlp : 0≤lp) (hr : 1≤r) :
    (r*lp)*(η*hp/r)^2≤η^2*(lp*hp^2) := by
  rw [source_energy_ratio hr]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact div_le_self (sq_nonneg η) hr

end Bilevel.ChiBoundedChain
