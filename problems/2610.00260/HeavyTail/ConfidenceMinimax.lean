import HeavyTail.ConfidenceCalibration
import HeavyTail.ConfidenceLower
import HeavyTail.MinimaxQuantile
import HeavyTail.RandomizedPolicy

/-! The confidence lower bound for the actual binary oracle family, with the
infimum ranging over all measurable adaptive policies and arbitrary seed laws.
The erasure probability and moment calibration are proved, not assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail

def tunedErasure (δ : ℝ) (T : ℕ) : ℝ := Real.exp (-(erasureLog δ / T))

theorem tunedErasure_pos (δ : ℝ) (T : ℕ) : 0 < tunedErasure δ T := Real.exp_pos _

theorem tunedErasure_lt_one {δ : ℝ} {T : ℕ}
    (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (hT : 0 < T) : tunedErasure δ T < 1 := by
  have hb := erasureLog_pos hδ hδ1
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  apply Real.exp_lt_one_iff.mpr
  exact neg_neg_of_pos (div_pos hb hTr)

def tunedConfidenceAmplitude (G s p δ : ℝ) (T : ℕ) : ℝ :=
  confidenceAmplitude G s p (erasureLog δ / T)

def confidenceRate (μ D G s p δ : ℝ) (T : ℕ) : ℝ :=
  (1 / 64 : ℝ) * envelope μ D (min G (s * (confidenceLog δ / T) ^ (1 - 1 / p)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

def confidenceExperimentLoss (e : E) (a μ D u : ℝ) {T : ℕ}
    (h : Bool) (A : RandomizedPolicy E E E T) (ω : A.Seed × (Fin T → Bool)) : ℝ :=
  confidenceObjective e a μ (envelopeRadius μ D a) h
    (A.policy.execute (confidenceOracle e a (envelopeRadius μ D a) u) h ω) -
  confidenceObjective e a μ (envelopeRadius μ D a) h
    (confidenceCenter e (envelopeRadius μ D a) h)

def confidenceFamilyQuantile (e : E) (a μ D u δ : ℝ) (hu : u ≤ 1) (T : ℕ) : ℝ≥0∞ :=
  minimaxErrorQuantile
    (fun (_h : Bool) (A : RandomizedPolicy E E E T) ↦
      A.seedLaw.prod (erasureSequenceLaw u hu T))
    (confidenceExperimentLoss e a μ D u) δ

theorem confidence_rate_probability_lower
    (e : E) (he : ‖e‖ = 1) {μ D G s p δ : ℝ} {T : ℕ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (hT : 0 < T)
    (A : RandomizedPolicy E E E T) :
    ∃ h : Bool, δ <
      (A.seedLaw.prod (erasureSequenceLaw (tunedErasure δ T)
        (tunedErasure_lt_one hδ hδ1 hT).le T)).real
      {ω | confidenceRate μ D G s p δ T ≤
        confidenceExperimentLoss e (tunedConfidenceAmplitude G s p δ T)
          μ D (tunedErasure δ T) h A ω} := by
  have hb := erasureLog_pos hδ hδ1
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have ha : 0 ≤ tunedConfidenceAmplitude G s p δ T :=
    confidenceAmplitude_nonneg hG hs (by positivity)
  have hu1 := tunedErasure_lt_one hδ hδ1 hT
  obtain ⟨h, _, hprob⟩ := confidence_objective_probability_lower
    A.policy A.seedLaw e he hμ hD ha (tunedErasure_pos δ T).le hu1
  have henv : confidenceRate μ D G s p δ T ≤
      envelope μ D (tunedConfidenceAmplitude G s p δ T) :=
    confidenceAmplitude_envelope hμ hD hG hs hp hδ hδ1 hT
  have hsub :
      {ω | envelope μ D (tunedConfidenceAmplitude G s p δ T) ≤
        confidenceExperimentLoss e (tunedConfidenceAmplitude G s p δ T)
          μ D (tunedErasure δ T) h A ω} ⊆
      {ω | confidenceRate μ D G s p δ T ≤
        confidenceExperimentLoss e (tunedConfidenceAmplitude G s p δ T)
          μ D (tunedErasure δ T) h A ω} := fun _ hω ↦ henv.trans hω
  have hcal : (tunedErasure δ T) ^ T / 2 = 2 * δ := by
    rw [tunedErasure, confidence_erasure_probability hδ hT]
    ring
  change (tunedErasure δ T) ^ T / 2 ≤ _ at hprob
  rw [hcal] at hprob
  refine ⟨h, ?_⟩
  exact (by linarith : δ < 2 * δ).trans_le (hprob.trans (measureReal_mono hsub))

/-- The full confidence-rate quantile bound for the concrete binary family. -/
theorem confidenceFamilyQuantile_lower
    (e : E) (he : ‖e‖ = 1) {μ D G s p δ : ℝ} {T : ℕ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (hT : 0 < T) :
    ENNReal.ofReal (confidenceRate μ D G s p δ T) ≤
      confidenceFamilyQuantile e (tunedConfidenceAmplitude G s p δ T)
        μ D (tunedErasure δ T) δ (tunedErasure_lt_one hδ hδ1 hT).le T := by
  apply minimaxErrorQuantile_lower
  exact confidence_rate_probability_lower e he hμ hD hG hs hp hδ hδ1 hT

omit [MeasurableSpace E] [BorelSpace E] in
/-- The same calibrated oracle satisfies both original centered moment bounds. -/
theorem tunedConfidenceOracle_two_moment_admissible
    (e : E) (he : ‖e‖ = 1) {μ D G s L p δ : ℝ} {T : ℕ}
    (hG : 0 ≤ G) (hs : 0 ≤ s) (hsL : s ≤ L) (hp : 1 < p) (hp2 : p ≤ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (hT : 0 < T) (h : Bool) (x : E) :
    let a := tunedConfidenceAmplitude G s p δ T
    let u := tunedErasure δ T
    (∫ b, ‖confidenceOracle e a (envelopeRadius μ D a) u h x b -
        confidenceMean e a (envelopeRadius μ D a) h x‖ ^ p
      ∂(erasureCoin u (tunedErasure_lt_one hδ hδ1 hT).le).toMeasure) ≤ L ^ p ∧
    ∀ v : E, ‖v‖ = 1 →
      (∫ b, |⟪v, confidenceOracle e a (envelopeRadius μ D a) u h x b -
        confidenceMean e a (envelopeRadius μ D a) h x⟫_ℝ| ^ p
        ∂(erasureCoin u (tunedErasure_lt_one hδ hδ1 hT).le).toMeasure) ≤ s ^ p := by
  have hb := erasureLog_pos hδ hδ1
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hz : 0 < erasureLog δ / T := div_pos hb hTr
  exact confidenceOracle_two_moment_admissible e he
    (confidenceAmplitude_nonneg hG hs hz.le) (tunedErasure_pos δ T)
    (tunedErasure_lt_one hδ hδ1 hT) (by linarith) hs hsL
    (confidenceAmplitude_moment hG hs hp hp2 hz) h x

/-- With zero raw calls, one fixed member of the same hard family gives the
full envelope lower quantile for every confidence level below one half. -/
theorem confidence_zero_query_quantile_lower
    (e : E) (he : ‖e‖ = 1) {μ D G δ : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hδ : δ < 1 / 2) :
    ENNReal.ofReal (envelope μ D G) ≤
      confidenceFamilyQuantile e G μ D 0 δ (by norm_num) 0 := by
  apply minimaxErrorQuantile_lower
  intro A
  obtain ⟨h, _, hprob⟩ := confidence_objective_probability_lower
    A.policy A.seedLaw e he hμ hD hG (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1)
  refine ⟨h, hδ.trans_le ?_⟩
  simpa only [pow_zero, confidenceExperimentLoss] using hprob

end HeavyTail
