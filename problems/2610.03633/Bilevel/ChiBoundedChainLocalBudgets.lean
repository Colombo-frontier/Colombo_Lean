import Bilevel.ChiBoundedChainWeightedWrapper
import Bilevel.ChiBoundedChainReceiverRadial
import Bilevel.ChiBoundedChainSize
import Bilevel.ChiBoundedChainRadial

/-! Construction-specific latent norm and positive radial budgets. The
existence theorem discharges all chain/receiver/release analytic premises. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiBoundedChain

theorem releaseGate_deriv_compactSupport : HasCompactSupport (deriv releaseGate) := by
  apply SmallGapProfileBounds.compactSupport_of_tail 2
  intro t ht
  rcases le_total 0 t with hp|hn
  · apply ZeroChainResidualCutoffs.deriv_zero_of_constant_on
      ((releaseGate_contDiff (k:=1)).differentiable (by norm_num) t) (uniqueDiffOn_Ici 2)
      (fun _ hx => releaseGate_one hx)
    simpa only [abs_of_nonneg hp] using ht
  · exact releaseGate_deriv_zero (by linarith)

theorem releaseGate_deriv_bound : ∃ J : ℝ,0≤J ∧ ∀ t,|deriv releaseGate t|≤J :=
  SmallGapProfileBounds.bound_of_compactSupport releaseGate_deriv_compactSupport
    ((releaseGate_contDiff (k:=2)).continuous_deriv (by norm_num))

theorem releaseCoefficient_abs_bound (hp Rp t J : ℝ) (hhp : 0<hp)
    (hJ : |deriv releaseGate (t/hp)|≤J) : |releaseCoefficient hp Rp t|≤|Rp| * J/hp := by
  rw [releaseCoefficient,abs_div,abs_mul,abs_of_pos hhp]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (abs_nonneg Rp)) hhp.le

theorem payload_gradient_norm_le (n : ℕ) (ℓ h A ν g hp T G : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (z : Space n)
    (hG : ‖gradient (chain n ℓ h) z‖≤G) :
    ‖gradient (payload n ℓ h A ν g hp T) z‖≤G+A*(3*ν*hp+g)+A*g := by
  rw [payload_gradient]
  have hb : ‖basis (Fin.last n)‖=1 := by simp [basis,EuclideanSpace.norm_single]
  have hs : ‖(positiveReceiverSlope A ν g h hp (z (Fin.last n))+
      negativeReceiverSlope A g h T (z (Fin.last n))) • basis (Fin.last n)‖≤A*(3*ν*hp+g)+A*g := by
    rw [norm_smul,Real.norm_eq_abs,hb,mul_one]
    exact (abs_add _ _).trans (add_le_add
      (positiveReceiverSlope_abs_bound A ν g h hp _ hA hν hg hh hhp)
      (negativeReceiverSlope_abs_bound A g h T _ hA hg))
  exact (norm_add_le _ _).trans (by linarith)

def normBudget (Cg J : ℝ) (n : ℕ) (ℓ h A ν g hp w Rp : ℝ) : ℝ :=
  w*(Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1)+A*(3*ν*hp+g)+A*g)+|Rp| * J/hp

def radialBudget (Cr : ℝ) (n : ℕ) (ℓ h A g T w : ℝ) : ℝ :=
  w*(Cr*((n:ℝ)+1)*(ℓ*h^2)+2*A*g*T)

theorem weightedLatent_norm_budget (Cg J : ℝ) (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (hw : 0≤w)
    (z : Space n) (hchain : ‖gradient (chain n ℓ h) z‖≤Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1))
    (hJ : ∀ t,|deriv releaseGate t|≤J) :
    ‖gradient (weightedLatent n ℓ h A ν g hp T w Rp) z‖≤normBudget Cg J n ℓ h A ν g hp w Rp := by
  rw [weightedLatent_gradient]
  have hpayload := payload_gradient_norm_le n ℓ h A ν g hp T _ hA hν hg hh hhp z hchain
  have hb : ‖basis (Fin.last n)‖=1 := by simp [basis,EuclideanSpace.norm_single]
  have h₁ : ‖w • gradient (payload n ℓ h A ν g hp T) z‖≤
      w*(Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1)+A*(3*ν*hp+g)+A*g) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left hpayload hw
  have h₂ : ‖releaseCoefficient hp Rp (z (Fin.last n)) • basis (Fin.last n)‖≤|Rp| * J/hp := by
    rw [norm_smul,Real.norm_eq_abs,hb,mul_one]
    exact releaseCoefficient_abs_bound hp Rp _ J hhp (hJ _)
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

theorem actual_local_budgets : ∃ Cg Cr J : ℝ,0≤Cg ∧ 0≤Cr ∧ 0≤J ∧
    ∀ (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ),
      0≤ℓ → 0≤A → 0≤ν → 0≤g → 0<h → 0<hp → 0<T → 0≤w → Rp≤0 → ∀ z : Space n,
      ‖gradient (weightedLatent n ℓ h A ν g hp T w Rp) z‖≤normBudget Cg J n ℓ h A ν g hp w Rp ∧
      ⟪z,gradient (weightedLatent n ℓ h A ν g hp T w Rp) z⟫≤radialBudget Cr n ℓ h A g T w := by
  obtain ⟨Cg,hCg,hg⟩ := Size.chain_gradient_norm_uniform
  obtain ⟨Cr,hCr,hr⟩ := Radial.chain_radial_positive_uniform
  obtain ⟨J,hJ,hj⟩ := releaseGate_deriv_bound
  refine ⟨Cg,Cr,J,hCg,hCr,hJ,fun n ℓ h A ν g hp T w Rp hℓ hA hν hg0 hh hhp hT hw hRp z => ⟨?_,?_⟩⟩
  · exact weightedLatent_norm_budget Cg J n ℓ h A ν g hp T w Rp hA hν hg0 hh hhp hw z
      (hg n ℓ h hℓ hh z) hj
  · exact weightedLatent_radial_upper n ℓ h A ν g hp T w Rp _ hA hν hg0 hh hhp hT hw hRp z
      ((le_max_right _ _).trans (hr n ℓ h hℓ hh z))

end Bilevel.ChiBoundedChain
