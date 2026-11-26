import SecondOrder.SampledKernelComposition
import SecondOrder.FiniteDrawsLaw

open MeasureTheory ProbabilityTheory

namespace SecondOrder
noncomputable section

variable {A T S : Type}

def sampledIterate (initial : A → S) (step : S → T → S) :
    (N : ℕ) → A × Draws T N → S
  | 0, w => initial w.1
  | N+1, w => step (sampledIterate initial step N (w.1,w.2.1)) w.2.2

variable [MeasurableSpace A] [MeasurableSpace T] [MeasurableSpace S]

theorem sampledIterate_measurable (initial : A → S) (hi : Measurable initial)
    (step : S → T → S) (hs : Measurable (fun w : S × T => step w.1 w.2)) (N : ℕ) :
    Measurable (sampledIterate initial step N) := by
  induction N with
  | zero => exact hi.comp measurable_fst
  | succ N ih =>
    exact hs.comp
      ((ih.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)

theorem sampledIterate_map_zero (α : Measure A) (θ : Measure T) [IsProbabilityMeasure θ]
    (initial : A → S) (hi : Measurable initial) (step : S → T → S) :
    Measure.map (sampledIterate initial step 0) (α.prod (drawsLaw θ 0))=Measure.map initial α := by
  have he : Measure.map (Prod.fst : A × Draws T 0 → A) (α.prod (drawsLaw θ 0))=α := by
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  conv_rhs => rw [←he,Measure.map_map hi measurable_fst]
  rfl

theorem sampledIterate_map_succ (α : Measure A) (θ : Measure T)
    [IsProbabilityMeasure α] [IsProbabilityMeasure θ]
    (initial : A → S) (hi : Measurable initial) (step : S → T → S)
    (hs : Measurable (fun w : S × T => step w.1 w.2)) (N : ℕ) :
    Measure.map (sampledIterate initial step (N+1)) (α.prod (drawsLaw θ (N+1)))=
      (Measure.map (sampledIterate initial step N) (α.prod (drawsLaw θ N))).bind
        (sampledResponseKernel θ step hs) := by
  have ha := measurePreserving_prodAssoc α (drawsLaw θ N) θ
  change Measure.map (sampledIterate initial step (N+1)) (α.prod ((drawsLaw θ N).prod θ))=_
  rw [←ha.map_eq,Measure.map_map (sampledIterate_measurable initial hi step hs (N+1)) ha.measurable]
  exact (map_bind_sampledResponse (α.prod (drawsLaw θ N)) θ (sampledIterate initial step N)
    (sampledIterate_measurable initial hi step hs N) step hs).symm

end
end SecondOrder
