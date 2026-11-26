import LowRank.GaussianFrobeniusHardness
import LowRank.FrobeniusOptimalResidual

/-! A measurable relative-error success event using the genuine optimal
Frobenius projector residual. The only outstanding probabilistic premise in
the final theorem is the Wishart spectral event estimate. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

def boundedOptimalFrobeniusSuccess (r s n k : ℕ) (L ε : ℝ)
    {S : Type*} [MeasurableSpace S]
    (policy : BoundedTwoSidedPolicy (r + n) (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S) :
    Set (S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :=
  {p | frobeniusSq (hardMatrix L (wishart p.2) * (1 - runBoundedHard r s n L policy p)) ≤
    (1 + ε) ^ 2 * optimalFrobeniusSq (hardMatrix L (wishart p.2)) k}

theorem measurableSet_boundedOptimalFrobeniusSuccess (r s n k : ℕ) (L ε : ℝ)
    {S : Type*} [MeasurableSpace S]
    (policy : BoundedTwoSidedPolicy (r + n) (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S) :
    MeasurableSet (boundedOptimalFrobeniusSuccess r s n k L ε policy) := by
  have hH : Measurable (fun p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ =>
      hardMatrix L (wishart p.2)) :=
    (measurable_hardMatrix (r + n) L).comp ((measurable_wishart (r + n) (s + n)).comp measurable_snd)
  have hP := measurable_runBoundedHard r s n L policy
  have hres : Measurable (fun p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ =>
      hardMatrix L (wishart p.2) * (1 - runBoundedHard r s n L policy p)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply, Matrix.sub_apply]
    apply Finset.measurable_sum
    intro a _
    exact ((measurable_pi_apply a).comp ((measurable_pi_apply i).comp hH)).mul
      (measurable_const.sub ((measurable_pi_apply j).comp ((measurable_pi_apply a).comp hP)))
  exact measurableSet_le ((continuous_frobeniusSq (r + n) (r + n)).measurable.comp
    hres)
    (measurable_const.mul ((measurable_optimalFrobeniusSq (r + n) k).comp hH))

theorem gaussian_optimal_frobenius_success_le_of_spectral_probability (k s n : ℕ) (L c₀ ε : ℝ)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (k + s + n)
      (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S)
    (hk : 0 < k) (hL : 0 < L) (hc : 0 < c₀) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hout : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank = k) n)
    (hn : (n : ℝ) ≤ (k + s + n : ℝ) / 100) (hkd : (k : ℝ) ≤ (k + s + n : ℝ) / 100)
    (hsmall : (2 * L / c₀) * ε * (k + s + n : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4)
    (hbad : (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
      {p | p.2 ∉ wishartSpectralEvent (k + s + n) (s + n) L c₀ k} ≤ 1 / 20) :
    (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
      (boundedOptimalFrobeniusSuccess (k + s) s n k L ε policy) ≤ 3 / 20 := by
  let μ := ν.prod (gaussianMatrixLaw (k + s + n) (s + n))
  have hmain := gaussian_frobenius_success_le_of_spectral_probability k s n L c₀ ε ν policy
    hk hL hc hε hε1 hout hn hkd hsmall hbad
  have hsub : ∀ᵐ p ∂μ, p ∈ boundedOptimalFrobeniusSuccess (k + s) s n k L ε policy →
      p ∈ boundedFrobeniusSuccess (k + s) s n L ε policy := by
    have hX := gaussianMatrixLaw_kernel_projector_spec_ae (k + s + n) (s + n) (by omega) (by omega)
    have hp := (Measure.quasiMeasurePreserving_snd (μ := ν)).ae hX
    filter_upwards [hp] with p hp
    intro hsuccess
    have hrank : (leftKernelProjector p.2).rank ≤ k := by
      rw [hp.2.2.2]
      omega
    have hopt := optimalFrobeniusSq_le (hardMatrix L (wishart p.2))
      (leftKernelProjector_isProjector p.2) hrank
    exact hsuccess.trans (mul_le_mul_of_nonneg_left hopt (sq_nonneg (1 + ε)))
  have hle : μ.real (boundedOptimalFrobeniusSuccess (k + s) s n k L ε policy) ≤
      μ.real (boundedFrobeniusSuccess (k + s) s n L ε policy) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact hle.trans hmain

end
end LowRank
