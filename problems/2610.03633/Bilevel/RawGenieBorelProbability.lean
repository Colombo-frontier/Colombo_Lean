import Bilevel.RawGenieBorelMeasurable

/-! An independent context may contain private randomness and all other
frames and edges. The selected Haar frame is the only excluded information.
The actual raw energy event is jointly measurable and is integrated directly. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.RawGenieBorel
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

theorem randomized_unsafe_probability {d T M R n : ℕ} {H : Memory.{u}}
    {C : Type*} [MeasurableSpace C] (hT : T≤d) (P : Policy d T H M R)
    (initial : C → H) (hi : Measurable initial) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (b : ℝ) (hb : 0<b) (hb2 : b≤2) (hd : M+R+(n+1)≤d)
    (hcap : (R:ℝ)*((M:ℝ)*b)≤1/2) :
    (ρ.prod (HaarFrame.frameLaw d T hT)) {p | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*b) R) (compile P (initial p.1)) ⊥ ∅ p.2} ≤
      (M:ℝ≥0∞)*GenieProtocol.failurePerQuery T n b := by
  have he := (hi.prodMap measurable_id) (initial_unsafe_measurable P
    (ProjectionEnergy.envelope ((M:ℝ)*b) R))
  change MeasurableSet {p : C × Frame d T | ¬RawGenieProtocol.Safe
    (ProjectionEnergy.envelope ((M:ℝ)*b) R) (compile P (initial p.1)) ⊥ ∅ p.2} at he
  rw [Measure.prod_apply (μ := ρ) (ν := HaarFrame.frameLaw d T hT) he]
  calc
    _ ≤ ∫⁻ _c, (M:ℝ≥0∞)*GenieProtocol.failurePerQuery T n b ∂ρ := by
      apply lintegral_mono
      intro c
      exact unsafe_probability hT P (initial c) b hb hb2 hd hcap
    _ = _ := by simp

theorem randomized_logarithmic_energy_bound {d T M n : ℕ} {H : Memory.{u}}
    {C : Type*} [MeasurableSpace C] (hT : T≤d) (hMpos : 0<M)
    (hTpos : 0<T) (hnpos : 0<n) (P : Policy d T H M T)
    (initial : C → H) (hi : Measurable initial) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hd : M+T+(n+1)≤d)
    (hcap : (T:ℝ)*((M:ℝ)*GenieProtocol.logarithmicIncrement M T n δ)≤1/2) :
    (ρ.prod (HaarFrame.frameLaw d T hT)) {p | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*GenieProtocol.logarithmicIncrement M T n δ) T)
      (compile P (initial p.1)) ⊥ ∅ p.2} ≤ ENNReal.ofReal (δ/2) := by
  have hb := GenieProtocol.logarithmic_increment_pos M T n hMpos hTpos hnpos δ hδ hδ1
  have hm : (1:ℝ)≤M := by exact_mod_cast hMpos
  have ht : (1:ℝ)≤T := by exact_mod_cast hTpos
  have hp : 1≤(T:ℝ)*M := by nlinarith
  have hb2 : GenieProtocol.logarithmicIncrement M T n δ≤2 := by
    have hh := mul_le_mul_of_nonneg_right hp hb.le
    nlinarith
  have h := randomized_unsafe_probability hT P initial hi ρ _ hb hb2 hd hcap
  have he : (M:ℝ≥0∞)*GenieProtocol.failurePerQuery T n
      (GenieProtocol.logarithmicIncrement M T n δ)=ENNReal.ofReal (δ/2) := by
    rw [GenieProtocol.failurePerQuery,← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg M),
      GenieProtocol.logarithmic_failure_identity M T n hMpos hTpos hnpos δ hδ]
  exact h.trans_eq he

end Bilevel.RawGenieBorel
