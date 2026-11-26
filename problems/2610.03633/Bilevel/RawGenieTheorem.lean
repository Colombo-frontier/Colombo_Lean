import Bilevel.RawGenieProtocol
import Bilevel.GenieTheorem

/-! Adaptive energy control for arbitrary queries with the full projection interface. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.RawGenieProtocol
open EuclideanGaussian ProjectionPosterior ProjectionEnergy GenieProtocol

theorem unsafe_probability (d T M R n : ℕ) (hT : T ≤ d)
    (P : RawGenieProtocol.Protocol d T M R) (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hd : M+R+(n+1) ≤ d) (hcap : (R : ℝ)*((M : ℝ)*b) ≤ 1/2)
    (hP : GenieProtocol.Regular b (normalize P ⊥ 0)) :
    (HaarFrame.frameLaw d T hT) {U | ¬ RawGenieProtocol.Safe (envelope ((M : ℝ)*b) R) P ⊥ ∅ U} ≤
      (M : ℝ≥0∞) * failurePerQuery T n b := by
  have hsub : {U : Frame d T | ¬ RawGenieProtocol.Safe (envelope ((M : ℝ)*b) R) P ⊥ ∅ U} ≤ᵐ[HaarFrame.frameLaw d T hT]
      {U | ¬ GenieProtocol.Safe (envelope ((M : ℝ)*b) R) (normalize P ⊥ 0) ⊥ ∅ U} := by
    filter_upwards [ProjectionConcentration.haar_orthonormal_ae d T hT] with U hU
    intro hsafe hg
    apply hsafe
    have hz : projections d T ⊥ U = 0 := by funext i; simp [projections,ProjectionGeometry.project]
    have h := safe_normalize_iff P (envelope ((M : ℝ)*b) R) ⊥ ∅ U hU
    rw [hz] at h
    exact h.mp hg
  exact (measure_mono_ae hsub).trans
    (GenieProtocol.unsafe_probability d T M R n hT (normalize P ⊥ 0) b hb hb2 hd hcap hP
      (normalized_valid P ⊥ 0))

theorem unsafe_probability_real (d T M R n : ℕ) (hT : T ≤ d)
    (P : RawGenieProtocol.Protocol d T M R) (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hd : M+R+(n+1) ≤ d) (hcap : (R : ℝ)*((M : ℝ)*b) ≤ 1/2)
    (hP : GenieProtocol.Regular b (normalize P ⊥ 0)) :
    (HaarFrame.frameLaw d T hT).real {U | ¬ RawGenieProtocol.Safe (envelope ((M : ℝ)*b) R) P ⊥ ∅ U} ≤
      (M : ℝ) * ((T : ℝ)*(2*Real.exp (-(n : ℝ)*b/8))) := by
  have h := unsafe_probability d T M R n hT P b hb hb2 hd hcap hP
  have hc : 0 ≤ (T : ℝ)*(2*Real.exp (-(n : ℝ)*b/8)) := by positivity
  have hf : (M : ℝ≥0∞) * failurePerQuery T n b ≠ ⊤ := by unfold failurePerQuery; finiteness
  have ht := ENNReal.toReal_mono hf h
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_natCast,failurePerQuery,
    ENNReal.toReal_ofReal hc] using ht

theorem logarithmic_energy_bound (d T M n : ℕ) (hT : T ≤ d) (hMpos : 0 < M)
    (hTpos : 0 < T) (hnpos : 0 < n) (P : RawGenieProtocol.Protocol d T M T)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : M+T+(n+1) ≤ d)
    (hcap : (T : ℝ)*((M : ℝ)*logarithmicIncrement M T n δ) ≤ 1/2)
    (hP : GenieProtocol.Regular (logarithmicIncrement M T n δ) (normalize P ⊥ 0)) :
    (HaarFrame.frameLaw d T hT).real
      {U | ¬ RawGenieProtocol.Safe (envelope ((M : ℝ)*logarithmicIncrement M T n δ) T) P ⊥ ∅ U} ≤ δ/2 := by
  have hb := logarithmic_increment_pos M T n hMpos hTpos hnpos δ hδ hδ1
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  have hp : 1 ≤ (T : ℝ)*M := by nlinarith
  have hb2 : logarithmicIncrement M T n δ ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hp hb.le
    nlinarith
  have h := unsafe_probability_real d T M T n hT P _ hb hb2 hd hcap hP
  rw [logarithmic_failure_identity M T n hMpos hTpos hnpos δ hδ] at h
  exact h

end Bilevel.RawGenieProtocol
