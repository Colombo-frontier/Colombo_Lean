import Bilevel.ChiBoundedChainRegularity
import Bilevel.ChiBoundedChainEstimates

/-! Full Euclidean gradient size of the revised bounded chain. Sparse edge
incidence gives a constant per coordinate and hence sqrt(length) growth. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain.Size
open ZeroChainPotential Regularity

theorem sum_injective_indicator_abs_le {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (j : κ) (a : ι → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (ha : ∀ i, |a i| ≤ A) :
    |∑ i, if j = f i then a i else 0| ≤ A := by
  classical
  by_cases h : ∃ i, j = f i
  · obtain ⟨i, rfl⟩ := h
    have he : ∀ k, f i = f k ↔ k = i := fun k =>
      ⟨fun h => (hf h).symm, fun h => by rw [h]⟩
    simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true] using ha i
  · have he : ∀ i, j ≠ f i := by simpa using h
    simpa only [if_neg (he _), Finset.sum_const_zero, abs_zero] using hA

theorem edgeLeft_abs_bound (K : ℝ) (hK : 0 ≤ K) (hpsi : ∀ t, |deriv psi t| ≤ K)
    (a b : ℝ) : |edgeLeft a b| ≤ 2 * K * gaussianBound := by
  have h0 := mul_le_mul (hpsi (-a)) (phi_bounded (-b)) (phi_nonneg (-b)) hK
  have h1 := mul_le_mul (hpsi a) (phi_bounded b) (phi_nonneg b) hK
  have ht := abs_sub (-deriv psi (-a) * phi (-b)) (deriv psi a * phi b)
  simp only [abs_mul, abs_neg, abs_of_nonneg (phi_nonneg _)] at ht
  dsimp [edgeLeft, gaussianBound]
  linarith

theorem edgeRight_abs_bound (a b : ℝ) :
    |edgeRight a b| ≤ 2 * 1 * Real.sqrt (Real.exp 1) := by
  have hs (t : ℝ) : phiSlope t ≤ Real.sqrt (Real.exp 1) := by
    simpa only [phi_deriv, abs_of_nonneg (phiSlope_nonneg t)] using phi_first_bound t
  have h0 := mul_le_mul ((psi_range (-a)).2) (hs (-b)) (phiSlope_nonneg (-b)) zero_le_one
  have h1 := mul_le_mul ((psi_range a).2) (hs b) (phiSlope_nonneg b) zero_le_one
  have ht := abs_sub (-psi (-a) * phiSlope (-b)) (psi a * phiSlope b)
  simp only [abs_mul, abs_neg, abs_of_nonneg (phiSlope_nonneg _),
    abs_of_nonneg (psi_nonneg _)] at ht
  dsimp [edgeRight]
  linarith

/-- The infinity-norm gradient bound is independent of the chain length:
each coordinate receives at most one incoming and one outgoing edge. -/
theorem coordinate_gradient_uniform_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ (n : ℕ) (z : Space n) (j : Fin (n + 1)), |gradient (value n) z j| ≤ B := by
  obtain ⟨K, hK, hpsi⟩ := psi_common_bound
  have hψ : ∀ t, |deriv psi t| ≤ K := by
    intro t
    simpa only [Fin.val_one, iteratedDeriv_one] using hpsi 1 t
  have hK0 : 0 ≤ K := hK.le
  have hB := gaussianBound_nonneg
  refine ⟨Real.sqrt (Real.exp 1) + 2 * K * gaussianBound +
    2 * 1 * Real.sqrt (Real.exp 1), by positivity, ?_⟩
  intro n z j
  rw [actual_gradient, gradientField_apply]
  simp_rw [edgeGradient_apply, Finset.sum_add_distrib]
  have h0 : |if j = 0 then -phiSlope (z 0) else 0| ≤ Real.sqrt (Real.exp 1) := by
    split_ifs
    · simpa only [abs_neg, phi_deriv] using phi_first_bound (z 0)
    · simp only [abs_zero]
      positivity
  have hleft := sum_injective_indicator_abs_le Fin.castSucc (Fin.castSucc_injective n) j
    (fun i => edgeLeft (z i.castSucc) (z i.succ)) (2 * K * gaussianBound) (by positivity)
    (fun i => edgeLeft_abs_bound K hK0 hψ _ _)
  have hright := sum_injective_indicator_abs_le Fin.succ (Fin.succ_injective n) j
    (fun i => edgeRight (z i.castSucc) (z i.succ))
    (2 * 1 * Real.sqrt (Real.exp 1)) (by positivity) (fun i => edgeRight_abs_bound _ _)
  calc
    _ ≤ |if j = 0 then -phiSlope (z 0) else 0| +
        (|∑ i : Fin n, if j = i.castSucc then edgeLeft (z i.castSucc) (z i.succ) else 0| +
        |∑ i : Fin n, if j = i.succ then edgeRight (z i.castSucc) (z i.succ) else 0|) :=
      (abs_add _ _).trans (add_le_add_left (abs_add _ _) _)
    _ ≤ Real.sqrt (Real.exp 1) + ((2 * K * gaussianBound) +
        (2 * 1 * Real.sqrt (Real.exp 1))) := add_le_add h0 (add_le_add hleft hright)
    _ = _ := by ring


theorem gradient_norm_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Space n),
    ‖gradient (value n) z‖≤C*Real.sqrt ((n:ℝ)+1) := by
  obtain ⟨C,hC,hb⟩ := coordinate_gradient_uniform_bound
  refine ⟨C,hC,fun n z => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  rw [norm_sq_coordinates,mul_pow,Real.sq_sqrt (by positivity : 0≤(n:ℝ)+1)]
  calc
    ∑ j,(gradient (value n) z j)^2 ≤ ∑ _ : Fin (n+1),C^2 := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [hb n z j,sq_abs (gradient (value n) z j),abs_nonneg (gradient (value n) z j)]
    _ = _ := by simp;ring

theorem chain_gradient_norm_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ℓ h : ℝ),
    0≤ℓ → 0<h → ∀ z : Space n,‖gradient (chain n ℓ h) z‖≤C*(ℓ*h)*Real.sqrt ((n:ℝ)+1) := by
  obtain ⟨C,hC,hb⟩ := gradient_norm_uniform
  refine ⟨C,hC,fun n ℓ h hℓ hh z => ?_⟩
  rw [chain_gradient n ℓ h hh,norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hℓ hh.le)]
  convert mul_le_mul_of_nonneg_left (hb n (h⁻¹ • z)) (mul_nonneg hℓ hh.le) using 1
  ring

end Bilevel.ChiBoundedChain.Size
