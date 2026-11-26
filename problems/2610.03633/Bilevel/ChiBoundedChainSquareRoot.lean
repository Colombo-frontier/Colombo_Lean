import Bilevel.ChiBoundedChainSelectorJets

/-! Dimension-independent square-root first-derivative estimates for the
actual revised selector and incoming frontier residual. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential

theorem unit_le_sqrt {a : ℝ} (h₀ : 0≤a) (h₁ : a≤1) : a≤Real.sqrt a := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_le_mul_of_nonneg_left h₁ h₀]

theorem unit_mul_sqrt_le {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hb₁ : b≤1) :
    b*Real.sqrt a≤Real.sqrt (a*b) := by
  calc
    b*Real.sqrt a≤Real.sqrt b*Real.sqrt a :=
      mul_le_mul_of_nonneg_right (unit_le_sqrt hb hb₁) (Real.sqrt_nonneg a)
    _ = Real.sqrt (a*b) := by rw [Real.sqrt_mul ha];ring

theorem evenGate_sqrt_derivative : ∃ C : ℝ,0≤C ∧
    ∀ t,|deriv psi t-deriv psi (-t)|≤C*Real.sqrt (evenGate t) := by
  obtain ⟨C,hC,hb⟩ := psi_sqrt_derivative
  refine ⟨C,hC,fun t => ?_⟩
  by_cases ht : 0≤t
  · have hp : psi (-t)=0 := psi_zero (by linarith)
    have hd : deriv psi (-t)=0 := psi_deriv_zero (by linarith)
    simpa only [evenGate,hp,hd,sub_zero,add_zero] using hb t
  · have hp : psi t=0 := psi_zero (by linarith)
    have hd : deriv psi t=0 := psi_deriv_zero (by linarith)
    simpa only [evenGate,hp,hd,zero_sub,zero_add,abs_neg] using hb (-t)

theorem mask_sqrt_derivative : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n),‖maskDerivative i z‖≤C*Real.sqrt (tailMask i z) := by
  obtain ⟨C,hC⟩ := mask_control_exists
  obtain ⟨B,hB,hb⟩ := energyCutoff_sqrt_derivative
  have hC0 : 0≤C := by linarith [hC.one_le]
  refine ⟨2*C*B,by positivity,fun n i z => ?_⟩
  by_cases hz : 1≤tailEnergy i z
  · have hd : deriv energyCutoff (tailEnergy i z)=0 := by
      simpa only [iteratedDeriv_one] using energyCutoff_flat_right 1 (by norm_num) _ hz
    simp only [maskDerivative,hd,zero_smul,norm_zero]
    positivity
  · have he : ‖energyDerivative i z‖≤2*C := by
      rw [energyDerivative_eq_toDual,LinearIsometryEquiv.norm_map]
      exact energyGradient_norm_bound hC i z (le_of_not_ge hz)
    unfold maskDerivative
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs]
    have hm := mul_le_mul (hb (tailEnergy i z)) he (norm_nonneg _) (by positivity)
    change |deriv energyCutoff (tailEnergy i z)| * ‖energyDerivative i z‖≤_
    convert hm using 1
    dsimp only [tailMask]
    ring

theorem selector_sqrt_derivative : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n),
      ‖selectorDerivative n i z‖≤C*Real.sqrt (selector n i z) := by
  obtain ⟨B,hB,hb⟩ := evenGate_sqrt_derivative
  obtain ⟨C,hC,hc⟩ := mask_sqrt_derivative
  refine ⟨B+C,add_nonneg hB hC,fun n i z => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (hc n 0 z).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (Real.sqrt_nonneg _))
  · let a := evenGate (z j.castSucc)
    let b := tailMask j.succ z
    have ha : 0≤a ∧ a≤1 := evenGate_range _
    have hb' : 0≤b ∧ b≤1 := tailMask_range _ _
    have h₁ := mul_le_mul_of_nonneg_right (hb (z j.castSucc)) hb'.1
    have h₂ := mul_le_mul_of_nonneg_left (hc n j.succ z) ha.1
    have hterm : ‖((deriv psi (z j.castSucc)-deriv psi (-z j.castSucc))*b) •
        EuclideanSpace.proj (𝕜:=ℝ) j.castSucc‖≤(B*Real.sqrt a)*b := by
      apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hb'.1]
      exact (mul_le_mul_of_nonneg_left (ZeroChainResidualBounds.projection_norm_le _)
        (mul_nonneg (abs_nonneg (deriv psi (z j.castSucc)-deriv psi (-z j.castSucc))) hb'.1)).trans
        (by simpa only [mul_one] using h₁)
    have hterm₂ : ‖a • maskDerivative j.succ z‖≤a*(C*Real.sqrt b) := by
      apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
      rw [Real.norm_eq_abs,abs_of_nonneg ha.1]
      exact h₂
    have hsmall₁ := mul_le_mul_of_nonneg_left (unit_mul_sqrt_le ha.1 hb'.1 hb'.2) hB
    have hsmall₂ := mul_le_mul_of_nonneg_left (unit_mul_sqrt_le hb'.1 ha.1 ha.2) hC
    rw [mul_comm b a] at hsmall₂
    change ‖((deriv psi (z j.castSucc)-deriv psi (-z j.castSucc))*b) •
      EuclideanSpace.proj (𝕜:=ℝ) j.castSucc+a • maskDerivative j.succ z‖≤(B+C)*Real.sqrt (a*b)
    exact (norm_add_le _ _).trans (by linarith)

def residualTermDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  (-phi (z i)) • selectorDerivative n i z+
    (-selector n i z*phiSlope (z i)) • EuclideanSpace.proj (𝕜:=ℝ) i

theorem residualTerm_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (residualTerm n i) (residualTermDerivative n i z) z := by
  convert (selector_hasFDerivAt n i z).neg.mul
    ((phi_hasDerivAt (z i)).hasFDerivAt.comp z (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt) using 1
  ext v
  simp [residualTermDerivative,ContinuousLinearMap.comp_apply]
  ring

theorem residualTerm_sqrt_derivative : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n),
      ‖residualTermDerivative n i z‖≤C*Real.sqrt (selector n i z) := by
  obtain ⟨B,hB,hb⟩ := selector_sqrt_derivative
  let P := Real.sqrt (Real.exp 1)
  have hP : 0≤P := Real.sqrt_nonneg _
  have hG := gaussianBound_nonneg
  refine ⟨gaussianBound*B+P,by positivity,fun n i z => ?_⟩
  have hs := selector_range n i z
  have hp : |phi (z i)|≤gaussianBound := by
    rw [abs_of_nonneg (phi_nonneg _)]
    exact phi_bounded _
  have hp' : |phiSlope (z i)|≤P := by simpa only [phi_deriv] using phi_first_bound (z i)
  have h₁ : ‖(-phi (z i)) • selectorDerivative n i z‖≤gaussianBound*(B*Real.sqrt (selector n i z)) := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs,abs_neg]
    exact mul_le_mul hp (hb n i z) (norm_nonneg _) gaussianBound_nonneg
  have h₂ : ‖(-selector n i z*phiSlope (z i)) • EuclideanSpace.proj (𝕜:=ℝ) i‖≤P*Real.sqrt (selector n i z) := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg hs.1]
    have hh := mul_le_mul_of_nonneg_left (ZeroChainResidualBounds.projection_norm_le i)
      (mul_nonneg hs.1 (abs_nonneg (phiSlope (z i))))
    simp only [mul_one] at hh
    have hl := mul_le_mul_of_nonneg_left hp' hs.1
    have hr := mul_le_mul_of_nonneg_left (unit_le_sqrt hs.1 hs.2) hP
    exact hh.trans (by nlinarith)
  exact (norm_add_le _ _).trans (by linarith)

end Bilevel.ChiBoundedChain
