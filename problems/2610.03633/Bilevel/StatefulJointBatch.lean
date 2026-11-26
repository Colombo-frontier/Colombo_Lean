import Bilevel.FullGradientKernelBridge
import Bilevel.StatefulBatch

/-! A single shared full-gradient batch. Its x and y estimates use the same
original observations, preserve their correlation, and cost n original calls. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful
open PrimitiveGeometry
variable {Query History Obs X Y : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

def FullGradientLaw.fullOracle {K : Kernel (Query × History) Obs} [IsMarkovKernel K]
    {rx : Obs → X} {ry : Obs → Y} {σ : ℝ} (G : FullGradientLaw K rx ry σ)
    (hx : Measurable rx) (hy : Measurable ry)
    (update : (Query × History) × Obs → History) (hu : Measurable update) :
    HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := Joint X Y) σ where
  law := K
  markov := inferInstance
  read := fun o => pack (rx o) (ry o)
  read_measurable := packLinear.continuous.measurable.comp (hx.prodMk hy)
  truth := fun q => pack (G.truth_x q) (G.truth_y q)
  truth_measurable := packLinear.continuous.measurable.comp
    (G.truth_x_measurable.prodMk G.truth_y_measurable)
  update := update
  update_measurable := hu
  square_integrable q h := by simpa only [norm_sq] using G.square_integrable q h
  mean q h := by
    have hiX : Integrable (fun o => rx o-G.truth_x q) (K (q,h)) :=
      (FullGradientLaw.xOracle G hx update hu).error_integrable q h
    have hiY : Integrable (fun o => ry o-G.truth_y q) (K (q,h)) :=
      (FullGradientLaw.yOracle G hy update hu).error_integrable q h
    have hh := (packLinear (X := X) (Y := Y)).integral_comp_comm (hiX.prodMk hiY)
    change (∫ o, pack (rx o-G.truth_x q) (ry o-G.truth_y q) ∂K (q,h)) =
      packLinear (∫ o, (rx o-G.truth_x q,ry o-G.truth_y q) ∂K (q,h)) at hh
    rw [integral_pair hiX hiY,G.mean_x,G.mean_y] at hh
    exact hh
  variance q h := by simpa only [norm_sq] using G.variance q h

namespace HistorySFO
variable {σf σg : ℝ}
  (O : HistorySFO (Query := Query) (History := History) (X := X) (Y := Y) σf σg)

def fullUpper : HistoryOracle (Query := Query) (History := History)
    (Obs := FullResponse X Y) (E := Joint X Y) σf :=
  O.upper.fullOracle (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) O.update O.update_measurable

def upperBatch (n : ℕ) : Procedure Query History (Joint X Y) := O.fullUpper.batch n

theorem upperBatch_calls (n : ℕ) : (O.upperBatch n).CallsEq (fun _ => n) :=
  O.fullUpper.batch_calls n

theorem upperBatch_error (n : ℕ) (hn : 0 < n) (q : Query) (h : History) :
    Integrable (fun z => ‖z.1.fst-O.upper.truth_x q‖^2+‖z.1.snd-O.upper.truth_y q‖^2)
      ((O.upperBatch n).law (q,h)) ∧
    (∫ z, ‖z.1.fst-O.upper.truth_x q‖^2+‖z.1.snd-O.upper.truth_y q‖^2
      ∂(O.upperBatch n).law (q,h)) ≤ σf^2/(n : ℝ) := by
  simpa only [norm_sq] using O.fullUpper.batch_error n hn q h

end HistorySFO
end Bilevel.Stateful
