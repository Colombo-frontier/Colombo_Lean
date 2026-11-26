import Bilevel.FullGradientKernelBridge

/-! Coordinate conversion from two full Euclidean gradient vectors to the
two-block implementation interface, preserving the joint conditional law. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful
variable {Query History Obs Obs' X Y : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs] [MeasurableSpace Obs']
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

def FullGradientLaw.pushforward {K : Kernel (Query × History) Obs}
    {rx : Obs → X} {ry : Obs → Y} {σ : ℝ} (G : FullGradientLaw K rx ry σ)
    (f : Obs → Obs') (hf : Measurable f) (sx : Obs' → X) (sy : Obs' → Y)
    (hx : Measurable sx) (hy : Measurable sy)
    (hex : ∀ o, sx (f o) = rx o) (hey : ∀ o, sy (f o) = ry o) :
    FullGradientLaw (K.map f) sx sy σ where
  truth_x := G.truth_x
  truth_y := G.truth_y
  truth_x_measurable := G.truth_x_measurable
  truth_y_measurable := G.truth_y_measurable
  rx_measurable := hx
  ry_measurable := hy
  square_integrable q h := by
    rw [Kernel.map_apply _ hf]
    have hm : Measurable (fun o => ‖sx o-G.truth_x q‖^2+‖sy o-G.truth_y q‖^2) := by fun_prop
    apply (integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable).mpr
    change Integrable (fun o => ‖sx (f o)-G.truth_x q‖^2+‖sy (f o)-G.truth_y q‖^2) (K (q,h))
    simpa only [hex,hey] using G.square_integrable q h
  mean_x q h := by
    rw [Kernel.map_apply _ hf]
    have hm : AEStronglyMeasurable (fun o : Obs' => sx o-G.truth_x q)
        (Measure.map f (K (q,h))) := (hx.sub measurable_const).aestronglyMeasurable
    calc
      _ = ∫ o, sx (f o)-G.truth_x q ∂K (q,h) := integral_map hf.aemeasurable hm
      _ = 0 := by simpa only [hex] using G.mean_x q h
  mean_y q h := by
    rw [Kernel.map_apply _ hf]
    have hm : AEStronglyMeasurable (fun o : Obs' => sy o-G.truth_y q)
        (Measure.map f (K (q,h))) := (hy.sub measurable_const).aestronglyMeasurable
    calc
      _ = ∫ o, sy (f o)-G.truth_y q ∂K (q,h) := integral_map hf.aemeasurable hm
      _ = 0 := by simpa only [hey] using G.mean_y q h
  variance q h := by
    rw [Kernel.map_apply _ hf]
    have hm : Measurable (fun o => ‖sx o-G.truth_x q‖^2+‖sy o-G.truth_y q‖^2) := by fun_prop
    rw [integral_map hf.aemeasurable hm.aestronglyMeasurable]
    simpa only [hex,hey] using G.variance q h

end Bilevel.Stateful

namespace Bilevel.Stateful
open PrimitiveGeometry
variable {Query History X Y : Type*} [MeasurableSpace Query] [MeasurableSpace History]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

def splitResponse (z : Joint X Y × Joint X Y) : FullResponse X Y :=
  ((z.1.fst,z.1.snd),(z.2.fst,z.2.snd))

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [SecondCountableTopology Y] [SecondCountableTopology (Joint X Y)] in
theorem splitResponse_measurable : Measurable (splitResponse (X := X) (Y := Y)) :=
  (((fullFst (X := X) (Y := Y)).continuous.measurable.comp measurable_fst).prodMk
    ((fullSnd (X := X) (Y := Y)).continuous.measurable.comp measurable_fst)).prodMk
  (((fullFst (X := X) (Y := Y)).continuous.measurable.comp measurable_snd).prodMk
    ((fullSnd (X := X) (Y := Y)).continuous.measurable.comp measurable_snd))

def packResponse (z : FullResponse X Y) : Joint X Y × Joint X Y :=
  (pack z.1.1 z.1.2,pack z.2.1 z.2.2)

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [SecondCountableTopology (Joint X Y)] in
theorem packResponse_measurable : Measurable (packResponse (X := X) (Y := Y)) :=
  ((packLinear (X := X) (Y := Y)).continuous.measurable.comp measurable_fst).prodMk
    ((packLinear (X := X) (Y := Y)).continuous.measurable.comp measurable_snd)

theorem pack_splitResponse {A B : Type*} (z : Joint A B × Joint A B) :
    packResponse (splitResponse z) = z := rfl

def HistorySFO.ofFullVectorKernel
    (K : Kernel (Query × History) (Joint X Y × Joint X Y)) [IsMarkovKernel K]
    (tf tg : Query → Joint X Y) (htf : Measurable tf) (htg : Measurable tg) (σf σg : ℝ)
    (hgf : ∀ q h, ConditionalKernelRepair.Good K (fun z => z.2.1-tf z.1.1) σf (q,h))
    (hgg : ∀ q h, ConditionalKernelRepair.Good K (fun z => z.2.2-tg z.1.1) σg (q,h))
    (update : (Query × History) × (Joint X Y × Joint X Y) → History) (hu : Measurable update) :
    HistorySFO (Query := Query) (History := History) (X := X) (Y := Y) σf σg where
  law := K.map splitResponse
  markov := Kernel.IsMarkovKernel.map _ splitResponse_measurable
  update z := update (z.1,packResponse z.2)
  update_measurable := hu.comp (measurable_fst.prodMk (packResponse_measurable.comp measurable_snd))
  upper := FullGradientLaw.pushforward (FullGradientLaw.ofFullVector K Prod.fst tf measurable_fst htf σf hgf)
    splitResponse splitResponse_measurable (fun z => z.1.1) (fun z => z.1.2)
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
    (fun _ => rfl) (fun _ => rfl)
  lower := FullGradientLaw.pushforward (FullGradientLaw.ofFullVector K Prod.snd tg measurable_snd htg σg hgg)
    splitResponse splitResponse_measurable (fun z => z.2.1) (fun z => z.2.2)
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
    (fun _ => rfl) (fun _ => rfl)

end Bilevel.Stateful
