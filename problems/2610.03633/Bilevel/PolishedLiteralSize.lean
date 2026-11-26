import Bilevel.PolishedLiteralEndgame
import Bilevel.ZeroChainRegularity

/-! Dimension-uniform gradient and lower value bounds for the manuscript's
fixed exponential, one-sided chain. The factor exp(1) is retained. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential

theorem edge_abs_bound (a b : ℝ) : |edge a b| ≤ Real.exp 1*gaussianBound := by
  rw [edge,abs_mul,abs_neg,abs_of_nonneg (psi_nonneg _),abs_of_nonneg (phi_nonneg _)]
  exact mul_le_mul (psi_le_exp_one a) (phi_bounded b) (phi_nonneg b) (Real.exp_pos _).le

theorem value_lower (n : ℕ) (z : Space n) :
    -((n:ℝ)+1)*(Real.exp 1*gaussianBound) ≤ value n z := by
  have he : ∑ i : Fin n,edge (z i.castSucc) (z i.succ) ≥ -((n:ℝ)*(Real.exp 1*gaussianBound)) := by
    have hh := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
      (neg_abs_le (edge (z i.castSucc) (z i.succ))).trans'
        (neg_le_neg (edge_abs_bound (z i.castSucc) (z i.succ))))
    simpa using hh
  have hp := Finset.sum_nonneg (fun (i : Fin (n+1)) (_ : i ∈ Finset.univ) => penalty_nonneg (z i))
  have hφ : phi (z 0) ≤ Real.exp 1*gaussianBound :=
    (phi_bounded _).trans (le_mul_of_one_le_left gaussianBound_nonneg (Real.one_le_exp (by norm_num)))
  change -((n:ℝ)+1)*(Real.exp 1*gaussianBound) ≤ -phi (z 0)+_+_
  linarith

theorem value_zero (n : ℕ) : value n 0 = -phi 0 := by
  have hp : psi 0 = 0 := psi_zero (by norm_num)
  simp [value,edge,hp,penalty_zero_at_zero]

theorem chain_lower (n : ℕ) (ℓ h : ℝ) (hℓ : 0 ≤ ℓ) (z : Space n) :
    -((n:ℝ)+1)*(Real.exp 1*gaussianBound)*(ℓ*h^2) ≤ chain n ℓ h z := by
  change _ ≤ (ℓ*h^2)*value n (h⁻¹ • z)
  nlinarith [mul_le_mul_of_nonneg_left (value_lower n (h⁻¹ • z))
    (show 0 ≤ ℓ*h^2 by positivity)]

theorem coordinate_gradient_uniform_bound : ∃ B : ℝ,0≤B ∧
    ∀ (n : ℕ) (z : Space n) (j : Fin (n+1)),|gradient (value n) z j|≤B := by
  obtain ⟨K,h⟩ := ZeroChainRegularity.profile_control_exists
  have hbL (a b : ℝ) : |edgeLeft a b|≤K^2 := by
    rw [edgeLeft,abs_mul,abs_neg]
    exact (mul_le_mul (h.psi1 a) (h.phi0 b) (abs_nonneg _) h.nonnegative).trans_eq (by ring)
  have hbR (a b : ℝ) : |edgeRight a b|≤K^2 := by
    rw [edgeRight,abs_mul,abs_neg,← phi_deriv]
    exact (mul_le_mul (h.psi0 a) (h.phi1 b) (abs_nonneg _) h.nonnegative).trans_eq (by ring)
  refine ⟨K+2*K^2+1,by nlinarith [h.nonnegative],?_⟩
  intro n z j
  rw [actual_gradient,gradientField_apply]
  simp_rw [edgeGradient_apply,Finset.sum_add_distrib]
  have h0 : |if j=0 then -phiSlope (z 0) else 0|≤K := by
    split_ifs
    · simpa only [abs_neg,phi_deriv] using h.phi1 (z 0)
    · simpa only [abs_zero] using h.nonnegative
  have hl := Size.sum_injective_indicator_abs_le Fin.castSucc (Fin.castSucc_injective n) j
    (fun i => edgeLeft (z i.castSucc) (z i.succ)) (K^2) (sq_nonneg _) (fun i => hbL _ _)
  have hr := Size.sum_injective_indicator_abs_le Fin.succ (Fin.succ_injective n) j
    (fun i => edgeRight (z i.castSucc) (z i.succ)) (K^2) (sq_nonneg _) (fun i => hbR _ _)
  have ht : |theta (-z j)|≤1 := by rw [abs_of_nonneg (theta_range _).1];exact (theta_range _).2
  have ha := abs_add (if j=0 then -phiSlope (z 0) else 0)
    ((∑ i : Fin n,if j=i.castSucc then edgeLeft (z i.castSucc) (z i.succ) else 0)+
      (∑ i : Fin n,if j=i.succ then edgeRight (z i.castSucc) (z i.succ) else 0))
  have hab := abs_add (∑ i : Fin n,if j=i.castSucc then edgeLeft (z i.castSucc) (z i.succ) else 0)
    (∑ i : Fin n,if j=i.succ then edgeRight (z i.castSucc) (z i.succ) else 0)
  exact (abs_sub _ _).trans (by linarith)

theorem gradient_norm_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Space n),
    ‖gradient (value n) z‖≤C*Real.sqrt ((n:ℝ)+1) := by
  obtain ⟨C,hC,hb⟩ := coordinate_gradient_uniform_bound
  refine ⟨C,hC,fun n z => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  rw [ChiBoundedChain.Regularity.norm_sq_coordinates,mul_pow,Real.sq_sqrt (by positivity : 0≤(n:ℝ)+1)]
  calc
    ∑ j,(gradient (value n) z j)^2≤∑ _ : Fin (n+1),C^2 := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [hb n z j,sq_abs (gradient (value n) z j),abs_nonneg (gradient (value n) z j)]
    _ = _ := by simp;ring

theorem chain_gradient_norm_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ℓ h : ℝ),
    0≤ℓ → 0<h → ∀ z : Space n,
      ‖gradient (chain n ℓ h) z‖≤C*(ℓ*h)*Real.sqrt ((n:ℝ)+1) := by
  obtain ⟨C,hC,hb⟩ := gradient_norm_uniform
  refine ⟨C,hC,fun n ℓ h hℓ hh z => ?_⟩
  rw [chain_gradient n ℓ h hh,norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hℓ hh.le)]
  convert mul_le_mul_of_nonneg_left (hb n (h⁻¹ • z)) (mul_nonneg hℓ hh.le) using 1
  ring

end Bilevel.PolishedLiteral
