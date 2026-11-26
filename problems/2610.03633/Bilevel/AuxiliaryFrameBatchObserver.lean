import Bilevel.AuxiliaryFrameObserver
import Bilevel.RawGenieBorelBatch

/-! General finite-batch auxiliary observation on the original joint prior.
Unlike the ordinary two-insertion specialization, M may include every
transported generator and terminal vector. These are observer insertions,
not extra original-oracle calls. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.IndependentFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine RawGenieBorel

theorem auxiliary_policy_failure {C : Type*} [MeasurableSpace C] (ρ : Measure C) [IsProbabilityMeasure ρ]
    {n D k T M R r : ℕ} {H : Memory.{u}} (hT : T≤D) (i : Fin (k+1))
    (P : Policy D T H M R)
    (initial : Context (C × TransportNetwork.Latent n D) D k → H) (hi : Measurable initial)
    (b : ℝ) (hb : 0<b) (hb2 : b≤2) (hD : M+R+(r+1)≤D)
    (hcap : (R:ℝ)*((M:ℝ)*b)≤1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1))) {s | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*b) R)
      (compile P (initial (auxiliaryExpose hT i s).1)) ⊥ ∅ (auxiliaryExpose hT i s).2}≤
      (M:ℝ≥0∞)*GenieProtocol.failurePerQuery T r b := by
  let ν := (ρ.prod (TransportNetwork.law n D)).prod
    (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))
  letI : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure
    ((ρ.prod (TransportNetwork.law n D)).prod (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))))
  have hp := randomized_unsafe_probability hT P initial hi ν b hb hb2 hD hcap
  have hm := (hi.prodMap measurable_id) (initial_unsafe_measurable P
    (ProjectionEnergy.envelope ((M:ℝ)*b) R))
  have he := (auxiliaryExpose_preserving ρ hT i).measure_preimage hm.nullMeasurableSet
  change (ρ.prod (TransportNetworkAuxiliary.law n D (k+1))) {s | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*b) R)
      (compile P (initial (auxiliaryExpose hT i s).1)) ⊥ ∅ (auxiliaryExpose hT i s).2} = _ at he
  rw [he]
  exact hp

theorem auxiliary_policy_logarithmic {C : Type*} [MeasurableSpace C] (ρ : Measure C) [IsProbabilityMeasure ρ]
    {n D k T M r : ℕ} {H : Memory.{u}} (hT : T≤D) (hMpos : 0<M) (hTpos : 0<T) (hrpos : 0<r)
    (i : Fin (k+1)) (P : Policy D T H M T)
    (initial : Context (C × TransportNetwork.Latent n D) D k → H) (hi : Measurable initial)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hD : M+T+(r+1)≤D)
    (hcap : (T:ℝ)*((M:ℝ)*GenieProtocol.logarithmicIncrement M T r δ)≤1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1))) {s | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*GenieProtocol.logarithmicIncrement M T r δ) T)
      (compile P (initial (auxiliaryExpose hT i s).1)) ⊥ ∅ (auxiliaryExpose hT i s).2}≤
      ENNReal.ofReal (δ/2) := by
  have hb := GenieProtocol.logarithmic_increment_pos M T r hMpos hTpos hrpos δ hδ hδ1
  have hm : (1:ℝ)≤M := by exact_mod_cast hMpos
  have ht : (1:ℝ)≤T := by exact_mod_cast hTpos
  have hp : 1≤(T:ℝ)*M := by nlinarith
  have hb2 : GenieProtocol.logarithmicIncrement M T r δ≤2 := by
    have hh := mul_le_mul_of_nonneg_right hp hb.le
    nlinarith
  have h := auxiliary_policy_failure ρ hT i P initial hi _ hb hb2 hD hcap
  have he : (M:ℝ≥0∞)*GenieProtocol.failurePerQuery T r
      (GenieProtocol.logarithmicIncrement M T r δ)=ENNReal.ofReal (δ/2) := by
    rw [GenieProtocol.failurePerQuery,← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg M),
      GenieProtocol.logarithmic_failure_identity M T r hMpos hTpos hrpos δ hδ]
  exact h.trans_eq he

end Bilevel.IndependentFrame
