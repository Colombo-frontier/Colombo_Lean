import NCBall.FunctionClass
import NCBall.ShadowMeasurable
import NCBall.BoundedRadius

/-! # A single certificate for the stochastic objectives on the actual query ball -/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff BigOperators
namespace NCBall

structure SmoothStochasticClass {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (f : Space n → ℝ) (F : Ξ → Space n → ℝ) (ℓ : Ξ → ℝ)
    (R H L Δ : ℝ) : Prop where
  radius_pos : 0 < R
  smooth : ContDiff ℝ ∞ f
  sample_smooth : ∀ z, ContDiff ℝ ∞ (F z)
  jointly_measurable : Measurable (fun xz : Space n × Ξ => F xz.2 xz.1)
  sample_integrable : ∀ x, Integrable (fun z => F z x) μ
  sample_mean : ∀ x, (∫ z, F z x ∂μ) = f x
  gradient_lipschitz : ∀ x y, ‖gradient f x - gradient f y‖ ≤ H * ‖x - y‖
  modulus_measurable : Measurable ℓ
  modulus_nonneg : ∀ z, 0 ≤ ℓ z
  sample_lipschitz : ∀ z x y, |F z x - F z y| ≤ ℓ z * ‖x - y‖
  modulus_square_integrable : Integrable (fun z => ℓ z ^ 2) μ
  modulus_square_moment : (∫ z, ℓ z ^ 2 ∂μ) ≤ L ^ 2
  bounded_gap : ∃ xmin ∈ closedBall 0 R,
    (∀ x ∈ closedBall 0 R, f xmin ≤ f x) ∧ f 0 - f xmin ≤ Δ

def calibratedRadius (η H Δ : ℝ) : ℝ :=
  37 * calibratedDepth (4 * η) H Δ * calibratedRho (4 * η) H

def calibratedPopulation {n : ℕ} (η H Δ : ℝ) (U : ℕ → Space n) : Space n → ℝ :=
  chainValue (calibratedDepth (4 * η) H Δ) (calibratedRho (4 * η) H) (4 * η)
    (calibratedLam (4 * η)) (roomCenter (calibratedRho (4 * η) H) U) U

def calibratedSample {n : ℕ} (η H Δ L : ℝ) (U : ℕ → Space n)
    (z : Fin (calibratedDepth (4 * η) H Δ) → Fin n → ℝ) : Space n → ℝ :=
  chainValue (calibratedDepth (4 * η) H Δ) (calibratedRho (4 * η) H) (4 * η)
    (calibratedLam (4 * η)) (roomCenter (calibratedRho (4 * η) H) U)
    (fun j => U j + (L / (4 * η)) • roomNoise z j)

theorem gaussian_sample_value_integrable {n M : ℕ} (hn : 0 < n)
    (ρ γ lam σ : ℝ) (c U : ℕ → Space n) (x : Space n) :
    Integrable (fun z : Fin M → Fin n → ℝ =>
      chainValue M ρ γ lam c (fun j => U j + σ • roomNoise z j) x) (gaussianRooms n M) := by
  have hloc (j : ℕ) : Integrable (fun z : Fin M → Fin n → ℝ =>
      localBump (U j + σ • roomNoise z j) (ρ⁻¹ • (x - c j))) (gaussianRooms n M) :=
    ((integrable_const (U j)).add ((gaussian_roomNoise_integrable hn j).smul σ)).inner_const _ |>.const_mul _
  exact ((integrable_const (-γ * x 0)).add
    ((integrable_finset_sum (Finset.range M) (fun j _ => hloc j)).const_mul (lam * ρ))).add
      (integrable_const (γ * ρ * terminalBump (ρ⁻¹ • (x - c M))))

theorem gaussian_sample_jointly_measurable {n M : ℕ} (ρ γ lam σ : ℝ) (c U : ℕ → Space n) :
    Measurable (fun xz : Space n × (Fin M → Fin n → ℝ) =>
      chainValue M ρ γ lam c (fun j => U j + σ • roomNoise xz.2 j) xz.1) := by
  have hv (j : ℕ) : Measurable (fun xz : Space n × (Fin M → Fin n → ℝ) =>
      U j + σ • roomNoise xz.2 j) := measurable_const.add
    (((roomNoise_continuous n M j).measurable.comp measurable_snd).const_smul σ)
  have hm := shadowValue_measurable_data M ρ γ lam (fun _ : Space n × (Fin M → Fin n → ℝ) => M)
    (fun _ => c) _ Prod.fst measurable_const (fun _ => measurable_const) hv measurable_fst
  simpa only [shadowValue_all_unlocked M M le_rfl] using hm

theorem calibrated_class_verified {n : ℕ} (hn : 0 < n) {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) (hL : 0 ≤ L)
    (hregime : 200 * bumpConstant * (4 * η) ^ 2 ≤ H * Δ)
    (hscale : (4 * η) * (bumpConstant + 2) ≤ L / 4)
    (hlog : 2 * Real.log (8 * ((calibratedDepth (4 * η) H Δ : ℝ) + 1)) ≤ n)
    (U : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hgood : ∀ i < calibratedDepth (4 * η) H Δ, ‖U i‖ ≤ 2) :
    SmoothStochasticClass (gaussianRooms n (calibratedDepth (4 * η) H Δ))
      (calibratedPopulation η H Δ U) (calibratedSample η H Δ L U)
      (sampleLipschitzModulus (4 * η) L) (calibratedRadius η H Δ) H L Δ := by
  have hc := function_class_verification hn hη hH hΔ hL hregime hscale hlog U hU hgood
  have hγ : 0 < 4 * η := by positivity
  have hρ := calibratedRho_pos hγ hH
  have hM := calibratedDepth_ge_two hγ hregime
  have hR : 0 < calibratedRadius η H Δ := by
    unfold calibratedRadius
    have : (0 : ℝ) < calibratedDepth (4 * η) H Δ := by exact_mod_cast (show 0 < calibratedDepth (4 * η) H Δ by omega)
    positivity
  refine ⟨hR, hc.1, hc.2.1, gaussian_sample_jointly_measurable _ _ _ _ _ _,
    fun x => gaussian_sample_value_integrable hn _ _ _ _ _ _ x, hc.2.2.1,
    ?_, ?_, sampleLipschitzModulus_nonneg hγ.le hL, ?_, hc.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.1, ?_⟩
  · intro x y
    simpa only [dist_eq_norm, NNReal.coe_mk] using hc.2.2.2.1.dist_le_mul x y
  · unfold sampleLipschitzModulus
    exact (continuous_const.add (continuous_const.mul
      (maximumNormSq_continuous n (calibratedDepth (4 * η) H Δ)).sqrt)).measurable
  · intro z x y
    simpa only [Real.dist_eq, dist_eq_norm, NNReal.coe_mk] using hc.2.2.2.2.2.1 z |>.dist_le_mul x y
  · let f := calibratedPopulation η H Δ U
    have hf : Continuous f := hc.1.continuous
    have hball := isCompact_closedBall (0 : Space n) (calibratedRadius η H Δ)
    obtain ⟨xmin, hx, hmin⟩ := hball.exists_isMinOn
      (nonempty_closedBall.mpr hR.le) hf.continuousOn
    refine ⟨xmin, hx, hmin, ?_⟩
    have hlow : sInf (f '' closedBall 0 (calibratedRadius η H Δ)) ≤ f xmin :=
      csInf_le (hball.image hf).bddBelow ⟨xmin, hx, rfl⟩
    have hgap := hc.2.2.2.2.1
    change f 0 - sInf (f '' closedBall 0 (calibratedRadius η H Δ)) ≤ Δ at hgap
    linarith

end NCBall
