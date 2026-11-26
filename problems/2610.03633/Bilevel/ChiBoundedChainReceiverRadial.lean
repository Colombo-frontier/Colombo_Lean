import Bilevel.ChiBoundedChainWeightedLatent

/-! Actual signs and positive radial contribution of the revised receivers
and release term. This supplies the construction-specific radial budget. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiBoundedChain

theorem positiveReceiver_radial_nonpos (A ν g h hp t : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) :
    t*positiveReceiverSlope A ν g h hp t≤0 := by
  by_cases ht : t≤0
  · rw [positiveReceiverSlope_zero_left A ν g h hp t hh ht,mul_zero]
  · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (lt_of_not_ge ht))
      (positiveReceiverSlope_nonpos A ν g h hp t hA hν hg hh)

theorem negativeReceiver_radial_upper (A g h T t : ℝ)
    (hA : 0≤A) (hg : 0≤g) (hh : 0<h) (hT : 0<T) :
    t*negativeReceiverSlope A g h T t≤2*A*g*T := by
  by_cases ht : 0≤t
  · rw [negativeReceiverSlope_zero_right A g h T t hh ht,mul_zero]
    positivity
  by_cases htT : t≤-(2*T)
  · rw [negativeReceiverSlope_zero_left A g h T t hT htT,mul_zero]
    positivity
  have habs : |t|≤2*T := by rw [abs_of_nonpos (le_of_not_ge ht)];linarith
  have hs := negativeReceiverSlope_abs_bound A g h T t hA hg
  have hp := mul_le_mul habs hs (abs_nonneg _) (by positivity : 0≤2*T)
  calc
    _ ≤ |t*negativeReceiverSlope A g h T t| := le_abs_self _
    _ = |t| * |negativeReceiverSlope A g h T t| := abs_mul _ _
    _ ≤ (2*T)*(A*g) := hp
    _ = _ := by ring

theorem releaseCoefficient_radial_nonpos (hp Rp t : ℝ) (hhp : 0<hp) (hRp : Rp≤0) :
    t*releaseCoefficient hp Rp t≤0 := by
  by_cases ht : t≤hp
  · have hd : deriv releaseGate (t/hp)=0 := releaseGate_deriv_zero
      ((div_le_iff₀ hhp).mpr (by simpa using ht))
    simp [releaseCoefficient,hd]
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (releaseCoefficient_nonpos hp Rp t hhp hRp)

theorem weightedLatent_radial_formula (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ) (z : Space n) :
    ⟪z,gradient (weightedLatent n ℓ h A ν g hp T w Rp) z⟫=
      w*⟪z,gradient (chain n ℓ h) z⟫+
        w*(z (Fin.last n)*positiveReceiverSlope A ν g h hp (z (Fin.last n))+
          z (Fin.last n)*negativeReceiverSlope A g h T (z (Fin.last n)))+
        z (Fin.last n)*releaseCoefficient hp Rp (z (Fin.last n)) := by
  have hi : ⟪z,basis (Fin.last n)⟫=z (Fin.last n) := by rw [real_inner_comm,inner_basis]
  rw [weightedLatent_gradient,payload_gradient]
  simp only [inner_add_right,real_inner_smul_right,hi]
  ring

theorem weightedLatent_radial_upper (n : ℕ) (ℓ h A ν g hp T w Rp C : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (hT : 0<T)
    (hw : 0≤w) (hRp : Rp≤0) (z : Space n)
    (hc : ⟪z,gradient (chain n ℓ h) z⟫≤C) :
    ⟪z,gradient (weightedLatent n ℓ h A ν g hp T w Rp) z⟫≤w*(C+2*A*g*T) := by
  rw [weightedLatent_radial_formula]
  have h₀ := mul_le_mul_of_nonneg_left hc hw
  have h₁ := positiveReceiver_radial_nonpos A ν g h hp (z (Fin.last n)) hA hν hg hh
  have h₂ := negativeReceiver_radial_upper A g h T (z (Fin.last n)) hA hg hh hT
  have h₃ := releaseCoefficient_radial_nonpos hp Rp (z (Fin.last n)) hhp hRp
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hw
  nlinarith only [h₀,hsum,h₃]

end Bilevel.ChiBoundedChain
