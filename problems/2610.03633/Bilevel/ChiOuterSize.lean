import Bilevel.ChiOuterEndgame

/-! Dimension-uniform gradient size and the global lower value bound for the
actual one-sided macro chain. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ZeroChainPotential

theorem edge_abs_bound (a b : ℝ) : |edge a b| ≤ gaussianBound := by
  rw [edge, abs_mul, abs_neg, abs_of_nonneg (psi_nonneg _), abs_of_nonneg (phi_nonneg _)]
  exact (mul_le_mul (psi_range a).2 (phi_bounded b) (phi_nonneg b) zero_le_one).trans_eq (one_mul _)

theorem value_lower (n : ℕ) (z : Space n) :
    -((n:ℝ)+1)*gaussianBound ≤ value n z := by
  have he : ∑ i : Fin n, edge (z i.castSucc) (z i.succ) ≥ -((n:ℝ)*gaussianBound) := by
    have hh := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
      (neg_abs_le (edge (z i.castSucc) (z i.succ))).trans'
        (neg_le_neg (edge_abs_bound (z i.castSucc) (z i.succ))))
    simpa using hh
  have hp := Finset.sum_nonneg (fun (i : Fin (n+1)) (_ : i ∈ Finset.univ) => penalty_nonneg (z i))
  have hφ := phi_bounded (z 0)
  change -((n:ℝ)+1)*gaussianBound ≤ -phi (z 0)+_+_
  change phi (z 0) ≤ gaussianBound at hφ
  linarith

theorem value_zero (n : ℕ) : value n 0 = -phi 0 := by
  have hp : psi 0 = 0 := psi_zero (by norm_num)
  simp [value, edge, hp, penalty_zero_at_zero]

theorem chain_lower (n : ℕ) (ℓ h : ℝ) (hℓ : 0 ≤ ℓ) (z : Space n) :
    -((n:ℝ)+1)*gaussianBound*(ℓ*h^2) ≤ chain n ℓ h z := by
  change _ ≤ (ℓ*h^2)*value n (h⁻¹ • z)
  nlinarith [mul_le_mul_of_nonneg_left (value_lower n (h⁻¹ • z))
    (show 0 ≤ ℓ*h^2 by positivity)]

theorem edgeLeft_abs_bound (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t, |deriv psi t| ≤ K)
    (a b : ℝ) : |edgeLeft a b| ≤ K*gaussianBound := by
  rw [edgeLeft, abs_mul, abs_neg, abs_of_nonneg (phi_nonneg b)]
  exact mul_le_mul (hb a) (phi_bounded b) (phi_nonneg b) hK

theorem edgeRight_abs_bound (a b : ℝ) : |edgeRight a b| ≤ Real.sqrt (Real.exp 1) := by
  rw [edgeRight, abs_mul, abs_neg, abs_of_nonneg (psi_nonneg a)]
  have hb : |phiSlope b| ≤ Real.sqrt (Real.exp 1) := by
    simpa only [phi_deriv] using phi_first_bound b
  exact (mul_le_mul (psi_range a).2 hb (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem coordinate_gradient_uniform_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ (n : ℕ) (z : Space n) (j : Fin (n+1)), |gradient (value n) z j| ≤ B := by
  obtain ⟨K,hK,hpsi⟩ := Regularity.psi_common_bound
  have hp : ∀ t, |deriv psi t| ≤ K := by
    intro t
    simpa only [Fin.val_one, iteratedDeriv_one] using hpsi 1 t
  have hG := gaussianBound_nonneg
  refine ⟨2*Real.sqrt (Real.exp 1)+K*gaussianBound+1, by positivity, ?_⟩
  intro n z j
  rw [actual_gradient, gradientField_apply]
  simp_rw [edgeGradient_apply, Finset.sum_add_distrib]
  have h0 : |if j = 0 then -phiSlope (z 0) else 0| ≤ Real.sqrt (Real.exp 1) := by
    split_ifs
    · simpa only [abs_neg, phi_deriv] using phi_first_bound (z 0)
    · simp only [abs_zero]
      positivity
  have hl := Size.sum_injective_indicator_abs_le Fin.castSucc (Fin.castSucc_injective n) j
    (fun i => edgeLeft (z i.castSucc) (z i.succ)) (K*gaussianBound)
    (mul_nonneg hK.le gaussianBound_nonneg) (fun i => edgeLeft_abs_bound K hK.le hp _ _)
  have hr := Size.sum_injective_indicator_abs_le Fin.succ (Fin.succ_injective n) j
    (fun i => edgeRight (z i.castSucc) (z i.succ)) (Real.sqrt (Real.exp 1))
    (Real.sqrt_nonneg _) (fun i => edgeRight_abs_bound _ _)
  have ht : |theta (-z j)| ≤ 1 := by rw [abs_of_nonneg (theta_range _).1]; exact (theta_range _).2
  have ha := abs_add (if j = 0 then -phiSlope (z 0) else 0)
    ((∑ i : Fin n, if j = i.castSucc then edgeLeft (z i.castSucc) (z i.succ) else 0)+
      (∑ i : Fin n, if j = i.succ then edgeRight (z i.castSucc) (z i.succ) else 0))
  have hab := abs_add (∑ i : Fin n, if j = i.castSucc then edgeLeft (z i.castSucc) (z i.succ) else 0)
    (∑ i : Fin n, if j = i.succ then edgeRight (z i.castSucc) (z i.succ) else 0)
  exact (abs_sub _ _).trans (by linarith)

theorem gradient_norm_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (z : Space n),
    ‖gradient (value n) z‖ ≤ C*Real.sqrt ((n:ℝ)+1) := by
  obtain ⟨C,hC,hb⟩ := coordinate_gradient_uniform_bound
  refine ⟨C,hC,fun n z => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  rw [Regularity.norm_sq_coordinates, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ)+1)]
  calc
    ∑ j, (gradient (value n) z j)^2 ≤ ∑ _ : Fin (n+1), C^2 := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [hb n z j, sq_abs (gradient (value n) z j), abs_nonneg (gradient (value n) z j)]
    _ = _ := by simp; ring

theorem chain_gradient_norm_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ℓ h : ℝ),
    0 ≤ ℓ → 0 < h → ∀ z : Space n,
      ‖gradient (chain n ℓ h) z‖ ≤ C*(ℓ*h)*Real.sqrt ((n:ℝ)+1) := by
  obtain ⟨C,hC,hb⟩ := gradient_norm_uniform
  refine ⟨C,hC,fun n ℓ h hℓ hh z => ?_⟩
  rw [chain_gradient n ℓ h hh, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hℓ hh.le)]
  convert mul_le_mul_of_nonneg_left (hb n (h⁻¹ • z)) (mul_nonneg hℓ hh.le) using 1
  ring

end Bilevel.ChiOuter
