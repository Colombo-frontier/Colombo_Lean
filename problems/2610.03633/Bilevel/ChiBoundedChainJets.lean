import Bilevel.ChiBoundedChainThird
import Bilevel.GradientJetBounds

/-! Exact physical scaling of the revised full-chain Hessian and third jet.
The numerical constants are independent of length, width, and curvature. -/
noncomputable section
namespace Bilevel.ChiBoundedChain.Jets
open Regularity Third

theorem full_jet_two_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Space n),
    ‖iteratedFDeriv ℝ 2 (value n) z‖≤C := by
  obtain ⟨C,hC⟩ := hessian_norm_uniform
  refine ⟨C,C.coe_nonneg,fun n z => ?_⟩
  rw [← GradientJetBounds.hessian_norm_eq (value_contDiff n 3) z]
  exact hC n z

theorem full_jet_three_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Space n),
    ‖iteratedFDeriv ℝ 3 (value n) z‖≤C := by
  obtain ⟨C,hC⟩ := third_derivative_norm_uniform
  refine ⟨C,C.coe_nonneg,fun n z => ?_⟩
  rw [← GradientJetBounds.third_norm_eq (value_contDiff n 3) z]
  exact hC n z

theorem chain_contDiff (n k : ℕ) (ℓ h : ℝ) : ContDiff ℝ k (chain n ℓ h) :=
  contDiff_const.mul ((value_contDiff n k).comp (contDiff_id.const_smul h⁻¹))

theorem chain_jet_two_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ℓ h : ℝ),
    0≤ℓ → 0<h → ∀ z : Space n,‖iteratedFDeriv ℝ 2 (chain n ℓ h) z‖≤C*ℓ := by
  obtain ⟨C,hC,hb⟩ := full_jet_two_uniform
  refine ⟨C,hC,fun n ℓ h hℓ hh z => ?_⟩
  have ht := ZeroChainResidualScaled.scaled_jet_bound (value_contDiff n 3)
    (ℓ*h^2) h C (by positivity) hh 2 (by norm_num) (hb n) z
  change ‖iteratedFDeriv ℝ 2 (chain n ℓ h) z‖≤C*(ℓ*h^2)/h^2 at ht
  convert ht using 1
  field_simp
  ring

theorem chain_jet_three_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ℓ h : ℝ),
    0≤ℓ → 0<h → ∀ z : Space n,‖iteratedFDeriv ℝ 3 (chain n ℓ h) z‖≤C*ℓ/h := by
  obtain ⟨C,hC,hb⟩ := full_jet_three_uniform
  refine ⟨C,hC,fun n ℓ h hℓ hh z => ?_⟩
  have ht := ZeroChainResidualScaled.scaled_jet_bound (value_contDiff n 3)
    (ℓ*h^2) h C (by positivity) hh 3 (by norm_num) (hb n) z
  change ‖iteratedFDeriv ℝ 3 (chain n ℓ h) z‖≤C*(ℓ*h^2)/h^3 at ht
  convert ht using 1
  field_simp
  ring

theorem chain_gradient_lipschitz_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ℓ h : ℝ),
    0≤ℓ → 0<h → ∀ x y : Space n,
      ‖gradient (chain n ℓ h) x-gradient (chain n ℓ h) y‖≤(C*ℓ)*‖x-y‖ := by
  obtain ⟨C,hC,hb⟩ := chain_jet_two_uniform
  exact ⟨C,hC,fun n ℓ h hℓ hh =>
    GradientJetBounds.gradient_lipschitz (chain_contDiff n 3 ℓ h) (C*ℓ) (hb n ℓ h hℓ hh)⟩

theorem chain_hessian_lipschitz_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ℓ h : ℝ),
    0≤ℓ → 0<h → ∀ x y : Space n,
      ‖fderiv ℝ (gradient (chain n ℓ h)) x-fderiv ℝ (gradient (chain n ℓ h)) y‖≤
        (C*ℓ/h)*‖x-y‖ := by
  obtain ⟨C,hC,hb⟩ := chain_jet_three_uniform
  exact ⟨C,hC,fun n ℓ h hℓ hh =>
    GradientJetBounds.hessian_lipschitz (chain_contDiff n 3 ℓ h) (C*ℓ/h) (hb n ℓ h hℓ hh)⟩

end Bilevel.ChiBoundedChain.Jets
