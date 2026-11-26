import NCBall.UpperFirstOrder

/-! # First-order parameters chosen uniformly before the objective

The configuration is an explicit function of V, Δ, ν and ε. This avoids
an instance-dependent existential choice of algorithm parameters.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped unitInterval
namespace NCBall

structure UpperConfig where
  D : ℝ
  nonneg : 0 ≤ D
  α : ℝ
  alpha_pos : 0 < α
  m : ℕ
  m_pos : 0 < m
  K : ℕ
  K_pos : 0 < K

def trivialUpperConfig : UpperConfig := ⟨0, le_rfl, 1, by norm_num, 1, by norm_num, 1, by norm_num⟩

def localUpperConfig (V Δ ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V) : UpperConfig :=
  if hdeep : ν * ε ≤ Δ then
    ⟨upperClipRadius V ν ε, (upperClipRadius_pos hν hε hV).le,
      upperLearningRate V ν ε, upperLearningRate_pos hν hε hV,
      upperBlockLength V ε, upperBlockLength_pos hε hV,
      upperBlockCount Δ ν ε, upperBlockCount_pos hν hε hdeep⟩
  else trivialUpperConfig

theorem localUpperConfig_radius (V Δ ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V) :
    let c := localUpperConfig V Δ ν ε hν hε hV
    (c.m : ℝ) * c.D ≤ ν := by
  dsimp only [localUpperConfig]
  split_ifs with hdeep
  · exact (upper_block_radius_eq hε hV).le
  · simpa [trivialUpperConfig] using hν.le

theorem localUpperConfig_steps (V Δ ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V)
    (hΔ : 0 ≤ Δ) :
    let c := localUpperConfig V Δ ν ε hν hε hV
    (c.K * c.m : ℕ) ≤ 725 * (1 + V ^ 2 * Δ / (ν * ε ^ 3)) := by
  dsimp only [localUpperConfig]
  split_ifs with hdeep
  · have h := upper_total_steps_bound hν hε hV hdeep
    dsimp
    calc
      _ ≤ 725 * V ^ 2 * Δ / (ν * ε ^ 3) := h
      _ ≤ _ := by ring_nf; linarith
  · have hratio : 0 ≤ V ^ 2 * Δ / (ν * ε ^ 3) := by positivity
    simp only [trivialUpperConfig, Nat.cast_mul, Nat.cast_one, one_mul]
    linarith

theorem localUpperConfig_path (V Δ ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V)
    (hΔ : 0 ≤ Δ) :
    let c := localUpperConfig V Δ ν ε hν hε hV
    (c.K * c.m : ℕ) * c.D ≤ 5 * Δ / ε := by
  dsimp only [localUpperConfig]
  split_ifs with hdeep
  · exact upper_total_path_bound hν hε hV hdeep
  · simp only [trivialUpperConfig, mul_zero]
    positivity

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ]
  {μ : Measure Ξ} [IsProbabilityMeasure μ]

theorem localUpperConfig_success {G : E → Ξ → E} {f : E → ℝ} {V Δ ν ε R : ℝ}
    (hf : ContDiff ℝ 1 f) (ho : OracleMoments μ G (gradient f) V)
    (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V) (hΔ : 0 ≤ Δ) (hRpos : 0 < R)
    (hR : 5 * Δ / ε ≤ R) (x₀ : E) (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    let c := localUpperConfig V Δ ν ε hν hε hV
    Measurable (upperRandomOutput c.D c.nonneg c.α G x₀ c.m (K := c.K)) ∧
      (∀ w : UpperRandomness Ξ, ∀ t < c.K * c.m,
        upperLocation c.D c.nonneg c.α G x₀ w.1 w.2 t ∈ closedBall x₀ R) ∧
      (∀ w : UpperRandomness Ξ × Fin c.K, upperRandomOutput c.D c.nonneg c.α G x₀ c.m w ∈ closedBall x₀ R) ∧
      ∃ S : Set (UpperRandomness Ξ × Fin c.K), MeasurableSet S ∧
        (1 / 2 : ℝ) ≤ (upperOutputLaw μ c.K c.K_pos).real S ∧
        ∀ w ∈ S, clarkeGoldsteinResidual f ν (upperRandomOutput c.D c.nonneg c.α G x₀ c.m w) ≤ ε := by
  let c := localUpperConfig V Δ ν ε hν hε hV
  have hpath : (c.K * c.m : ℕ) * c.D ≤ R := (localUpperConfig_path V Δ ν ε hν hε hV hΔ).trans hR
  refine ⟨upperRandomOutput_measurable c.D c.nonneg c.α G ho.measurable x₀ c.m c.K, ?_, ?_, ?_⟩
  · intro w t ht
    change t < c.K * c.m at ht
    rw [mem_closedBall, dist_eq_norm]
    exact (upper_sample_location_bound c.D c.nonneg c.α G x₀ w.1 w.2 t).trans
      ((mul_le_mul_of_nonneg_right (by exact_mod_cast (show t + 1 ≤ c.K * c.m by omega)) c.nonneg).trans hpath)
  · intro w
    exact (closedBall_subset_closedBall hpath) (upperRandomOutput_in_ball c.D c.nonneg c.α G x₀ c.m_pos w)
  · by_cases hdeep : ν * ε ≤ Δ
    · have hd := upperClipRadius_pos hν hε hV
      have ha := upperLearningRate_pos hν hε hV
      have hm := upperBlockLength_pos hε hV
      have hk := upperBlockCount_pos hν hε hdeep
      have hp : (upperBlockCount Δ ν ε * upperBlockLength V ε : ℕ) * upperClipRadius V ν ε ≤ R :=
        (upper_total_path_bound hν hε hV hdeep).trans hR
      obtain ⟨S, hS, hmass, hsuccess⟩ := upperRandomOutput_success hf ho hd ha hε x₀ hm hk hp hgap
        (upper_parameter_accuracy hν hε hV hdeep)
      rw [localUpperConfig, dif_pos hdeep]
      refine ⟨S, hS, hmass, ?_⟩
      intro w hw
      simpa only [upper_block_radius_eq hε hV] using (hsuccess w hw).2
    · have hstationary : clarkeGoldsteinResidual f ν x₀ ≤ ε := by
        by_cases hd : Δ = 0
        · exact (zero_gap_start_stationary hf x₀ hν hRpos (by simpa only [hd] using hgap)).trans hε.le
        · have hdpos : 0 < Δ := lt_of_le_of_ne hΔ (Ne.symm hd)
          apply large_radius_start_stationary hf x₀ hdpos hε
          · exact (div_le_iff₀ hε).2 (by linarith)
          · have hnonneg : 0 ≤ Δ / ε := div_nonneg hΔ hε.le
            calc
              _ ≤ 5 * Δ / ε := by ring_nf at hnonneg ⊢; linarith
              _ ≤ R := hR
          · exact hgap
      rw [localUpperConfig, dif_neg hdeep]
      refine ⟨univ, MeasurableSet.univ, by norm_num, ?_⟩
      intro w _
      simpa only [trivialUpperConfig, upperRandomOutput_one] using hstationary

end NCBall
