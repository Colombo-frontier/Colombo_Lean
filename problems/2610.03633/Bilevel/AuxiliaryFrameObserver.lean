import Bilevel.IndependentFrameContext

/-! Selected-frame observation under the original network-plus-auxiliary
prior. The complete network and all *other* auxiliary orientations may be
used by the Borel policy. The selected orientation is accessed only through
the compiled raw query/revelation interface. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.IndependentFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine OrdinaryFrame

theorem auxiliary_observer {C : Type*} [MeasurableSpace C] (ρ : Measure C) [IsProbabilityMeasure ρ]
    {n D k T Q r : ℕ} {H : Memory.{u}} (hT : T≤D) (hTpos : 0<T) (hrpos : 0<r)
    (i : Fin (k+1)) (L : Rules H D T)
    (initial : Context (C × TransportNetwork.Latent n D) D k → H) (hi : Measurable initial)
    (t : ℕ) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hD : (2*Q+1)+T+(r+1)≤D)
    (hcap : (T:ℝ)*(((2*Q+1:ℕ):ℝ)*GenieProtocol.logarithmicIncrement (2*Q+1) T r δ)≤1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1))) {s | ¬Observed L
      (2*((2*Q+1:ℕ):ℝ)*GenieProtocol.logarithmicIncrement (2*Q+1) T r δ)
      Q T t (initial (auxiliaryExpose hT i s).1,(⊥,∅)) (auxiliaryExpose hT i s).2} ≤
      ENNReal.ofReal (δ/2) := by
  let ν := (ρ.prod (TransportNetwork.law n D)).prod
    (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))
  letI : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure
    ((ρ.prod (TransportNetwork.law n D)).prod (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))))
  have hp := logarithmic_observer hT hTpos hrpos L initial hi ν t δ hδ hδ1 hD hcap
  have hs : BorelState (fun p : Context (C × TransportNetwork.Latent n D) D k × Frame D T =>
      (initial p.1,((⊥ : Submodule ℝ (Space D)),(∅ : Set (Fin T))))) := by
    refine ⟨hi.comp measurable_fst,?_,fun _ => MeasurableSet.empty⟩
    change Measurable (fun _ : Context (C × TransportNetwork.Latent n D) D k × Frame D T =>
      ProjectionStore.ofSubspace D (⊥ : Submodule ℝ (Space D)))
    exact measurable_const
  have hm := (observed_measurable L
    (2*((2*Q+1:ℕ):ℝ)*GenieProtocol.logarithmicIncrement (2*Q+1) T r δ)
    Q T t _ hs _ measurable_snd).compl
  have he := (auxiliaryExpose_preserving ρ hT i).measure_preimage hm.nullMeasurableSet
  change (ρ.prod (TransportNetworkAuxiliary.law n D (k+1))) {s | ¬Observed L
      (2*((2*Q+1:ℕ):ℝ)*GenieProtocol.logarithmicIncrement (2*Q+1) T r δ)
      Q T t (initial (auxiliaryExpose hT i s).1,(⊥,∅)) (auxiliaryExpose hT i s).2} = _ at he
  rw [he]
  exact hp

end Bilevel.IndependentFrame
