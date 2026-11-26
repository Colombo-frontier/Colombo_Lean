import NCBall.StochasticLipschitz
import NCBall.GaussianSampleMean
import NCBall.GaussianGoodEvent

/-! # Verification of the constructed stochastic function class

This assembles the actual function, Gaussian sample law, uniform analytic
constants, stochastic Lipschitz moment, gap and stationarity conclusions.
It is Lemma 7.2, not the adaptive query lower bound in Theorem 4.1.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff NNReal
namespace NCBall

/-- All function-class conclusions hold simultaneously for every good hidden
instance. No derivative bound, noise moment or sample-mean equation is assumed. -/
theorem function_class_verification {n : ℕ} (hn : 0 < n) {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) (hL : 0 ≤ L)
    (hregime : 200 * bumpConstant * (4 * η) ^ 2 ≤ H * Δ)
    (hscale : (4 * η) * (bumpConstant + 2) ≤ L / 4)
    (hlog : 2 * Real.log (8 * ((calibratedDepth (4 * η) H Δ : ℝ) + 1)) ≤ n)
    (U : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hgood : ∀ i < calibratedDepth (4 * η) H Δ, ‖U i‖ ≤ 2) :
    let M := calibratedDepth (4 * η) H Δ
    let ρ := calibratedRho (4 * η) H
    let f := chainValue M ρ (4 * η) (calibratedLam (4 * η)) (roomCenter ρ U) U
    let F := fun z : Fin M → Fin n → ℝ =>
      chainValue M ρ (4 * η) (calibratedLam (4 * η)) (roomCenter ρ U)
        (fun j => U j + (L / (4 * η)) • roomNoise z j)
    let ℓ := sampleLipschitzModulus (n := n) (M := M) (4 * η) L
    ContDiff ℝ ∞ f ∧
      (∀ z, ContDiff ℝ ∞ (F z)) ∧
      (∀ x, (∫ z, F z x ∂gaussianRooms n M) = f x) ∧
      LipschitzWith ⟨H, hH.le⟩ (gradient f) ∧
      f 0 - sInf (f '' closedBall 0 (37 * M * ρ)) ≤ Δ ∧
      (∀ z, LipschitzWith ⟨ℓ z, sampleLipschitzModulus_nonneg (by positivity) hL z⟩ (F z)) ∧
      Integrable (fun z => ℓ z ^ 2) (gaussianRooms n M) ∧
      (∫ z, ℓ z ^ 2 ∂gaussianRooms n M) ≤ L ^ 2 ∧
      gradient f (roomCenter ρ U M) = 0 ∧
      (∀ x, ‖gradient f x‖ ≤ η → x ∈ closedBall (roomCenter ρ U M) ρ) ∧
      (∀ j ≤ M, closedBall (roomCenter ρ U j) ρ ⊆ closedBall 0 (37 * M * ρ)) := by
  dsimp only
  have hγ : 0 < 4 * η := by positivity
  have hρ := calibratedRho_pos hγ hH
  have hd := deterministic_class_verification hη hH hΔ hregime U hU hgood
  have hsize : (calibratedDepth (4 * η) H Δ : ℝ) * Real.exp (-(n : ℝ) / 2) ≤ 1 :=
    (gaussian_size_from_log hlog).trans (by norm_num)
  exact ⟨chainValue_smooth _ _ _ _ _ _, fun _ => chainValue_smooth _ _ _ _ _ _,
    fun x => gaussian_sample_mean_eq_population hn _ _ _ _ _ _ x,
    hd.1, hd.2.1, fun z => gaussian_sample_lipschitz hρ hγ hL U hU hgood z,
    sampleLipschitzModulus_square_integrable hn _ _,
    gaussian_sample_lipschitz_second_moment hn hsize hγ.le hscale,
    hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩

end NCBall
