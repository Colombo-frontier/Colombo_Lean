import Bilevel.ChiBoundedChainSize

/-! The global radial estimate for the revised bounded chain. Compact
activation derivatives and the Gaussian tail bound every radial edge term;
the estimate holds at arbitrary query magnitudes. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain.Radial
open ZeroChainPotential Regularity

theorem psi_deriv_zero_of_ge {t : ℝ} (ht : 1≤t) : deriv psi t=0 :=
  ZeroChainResidualCutoffs.deriv_zero_of_constant_on (psi_hasDerivAt t).differentiableAt
    (uniqueDiffOn_Ici 1) (fun _ hx => psi_one hx) ht

theorem weighted_psi_deriv_bound {K : ℝ} (hK : 0≤K)
    (hb : ∀ t,|deriv psi t|≤K) (t : ℝ) : |t*deriv psi t|≤K := by
  by_cases ht : t≤1/2
  · rw [psi_deriv_zero ht,mul_zero,abs_zero]
    exact hK
  by_cases ht1 : 1≤t
  · rw [psi_deriv_zero_of_ge ht1,mul_zero,abs_zero]
    exact hK
  have hab : |t|≤1 := by rw [abs_of_nonneg (by linarith)];linarith
  rw [abs_mul]
  exact (mul_le_mul hab (hb t) (abs_nonneg _) zero_le_one).trans_eq (one_mul K)

theorem weighted_phi_deriv_bound (t : ℝ) : |t*phiSlope t|≤3*Real.sqrt (Real.exp 1) := by
  have hh := phi_second_bound t
  rw [phi_second_deriv,neg_mul,abs_neg] at hh
  exact hh

theorem weighted_edgeLeft_bound {K : ℝ} (hK : 0≤K)
    (hb : ∀ t,|t*deriv psi t|≤K) (a b : ℝ) :
    |a*edgeLeft a b|≤2*K*gaussianBound := by
  have h0 : |((-a)*deriv psi (-a))*phi (-b)|≤K*gaussianBound := by
    rw [abs_mul,abs_of_nonneg (phi_nonneg _)]
    exact mul_le_mul (hb (-a)) (phi_bounded (-b)) (phi_nonneg _) hK
  have h1 : |(a*deriv psi a)*phi b|≤K*gaussianBound := by
    rw [abs_mul,abs_of_nonneg (phi_nonneg _)]
    exact mul_le_mul (hb a) (phi_bounded b) (phi_nonneg _) hK
  have he : a*edgeLeft a b=((-a)*deriv psi (-a))*phi (-b)-(a*deriv psi a)*phi b := by
    unfold edgeLeft
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

theorem weighted_edgeRight_bound (a b : ℝ) :
    |b*edgeRight a b|≤6*Real.sqrt (Real.exp 1) := by
  have h0 : |psi (-a)*(b*phiSlope (-b))|≤3*Real.sqrt (Real.exp 1) := by
    rw [abs_mul,abs_of_nonneg (psi_nonneg _)]
    have hb : |b*phiSlope (-b)|≤3*Real.sqrt (Real.exp 1) := by
      simpa only [neg_mul,abs_neg] using weighted_phi_deriv_bound (-b)
    exact (mul_le_mul (psi_range (-a)).2 hb (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h1 : |psi a*(b*phiSlope b)|≤3*Real.sqrt (Real.exp 1) := by
    rw [abs_mul,abs_of_nonneg (psi_nonneg _)]
    exact (mul_le_mul (psi_range a).2 (weighted_phi_deriv_bound b)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he : b*edgeRight a b=-(psi (-a)*(b*phiSlope (-b)))-(psi a*(b*phiSlope b)) := by
    unfold edgeRight
    ring
  rw [he]
  have hh := abs_sub (-(psi (-a)*(b*phiSlope (-b)))) (psi a*(b*phiSlope b))
  rw [abs_neg] at hh
  linarith

theorem inner_basis_right {n : ℕ} (z : Space n) (i : Fin (n+1)) : ⟪z,basis i⟫=z i := by
  rw [real_inner_comm,inner_basis]

theorem radial_identity (n : ℕ) (z : Space n) :
    ⟪z,gradient (value n) z⟫=-(z 0*phiSlope (z 0))+
      ∑ i : Fin n,((z i.castSucc)*edgeLeft (z i.castSucc) (z i.succ)+
        (z i.succ)*edgeRight (z i.castSucc) (z i.succ)) := by
  rw [actual_gradient]
  simp only [gradientField,inner_add_right,inner_sum,real_inner_smul_right,inner_basis_right,
    edgeGradient,inner_add_right,real_inner_smul_right,inner_basis_right]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem radial_abs_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Space n),
    |⟪z,gradient (value n) z⟫|≤C*((n:ℝ)+1) := by
  obtain ⟨K,hK,hb⟩ := psi_common_bound
  have hpsi (t : ℝ) : |deriv psi t|≤K := by simpa only [Fin.val_one,iteratedDeriv_one] using hb 1 t
  let C := 2*K*gaussianBound+9*Real.sqrt (Real.exp 1)
  have hg := gaussianBound_nonneg
  have hC : 0≤C := by dsimp [C];positivity
  refine ⟨C,hC,fun n z => ?_⟩
  rw [radial_identity]
  have he (i : Fin n) : |(z i.castSucc)*edgeLeft (z i.castSucc) (z i.succ)+
      (z i.succ)*edgeRight (z i.castSucc) (z i.succ)|≤2*K*gaussianBound+6*Real.sqrt (Real.exp 1) :=
    (abs_add _ _).trans (add_le_add
      (weighted_edgeLeft_bound hK.le (weighted_psi_deriv_bound hK.le hpsi) _ _)
      (weighted_edgeRight_bound _ _))
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => he i)
  have ht := (abs_add (-(z 0*phiSlope (z 0)))
    (∑ i : Fin n,((z i.castSucc)*edgeLeft (z i.castSucc) (z i.succ)+
      (z i.succ)*edgeRight (z i.castSucc) (z i.succ)))).trans
      (add_le_add (by simpa only [abs_neg] using weighted_phi_deriv_bound (z 0))
        (Finset.abs_sum_le_sum_abs ..))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  dsimp [C]
  nlinarith [mul_nonneg hK.le hg,Real.sqrt_nonneg (Real.exp 1),
    (show 0≤(n:ℝ) by positivity)]

theorem chain_radial_positive_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ℓ h : ℝ),
    0≤ℓ → 0<h → ∀ z : Space n,
      max 0 ⟪z,gradient (chain n ℓ h) z⟫≤C*((n:ℝ)+1)*(ℓ*h^2) := by
  obtain ⟨C,hC,hb⟩ := radial_abs_uniform
  refine ⟨C,hC,fun n ℓ h hℓ hh z => ?_⟩
  have he : ⟪z,gradient (chain n ℓ h) z⟫=
      (ℓ*h^2)*⟪h⁻¹ • z,gradient (value n) (h⁻¹ • z)⟫ := by
    rw [chain_gradient n ℓ h hh,real_inner_smul_right,real_inner_smul_left]
    field_simp
    ring
  apply max_le
  · positivity
  rw [he]
  have hh0 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb n (h⁻¹ • z)))
    (show 0≤ℓ*h^2 by positivity)
  nlinarith

end Bilevel.ChiBoundedChain.Radial
