import Smoothness2601.AdaptiveModel
import Bilevel.FullGradientKernelBridge
import Bilevel.HistoryOracleTransform

/-! The inner solver reads the lower block of actual full-gradient calls.
No additional oracle is assumed; the supplied oracle's hidden history is
threaded unchanged. These adapters also expose the other blocks for reuse. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel.PrimitiveGeometry Bilevel.Stateful
namespace Smoothness2601.InnerOracle

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)

instance jointSecondCountable : SecondCountableTopology (Joint X Y) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).toHomeomorph.secondCountableTopology

omit [SecondCountableTopology X] in
theorem trueGradient_measurable : Measurable (Adaptive.trueGradient P) := by
  have hfg : Continuous P.grad_f := (LipschitzWith.of_dist_le_mul (K := ⟨b.L₁,b.L₁_pos.le⟩)
    (fun z w => by simpa only [dist_eq_norm, NNReal.coe_mk] using P.smooth_f z w)).continuous
  have hgg : Continuous P.grad_g := (LipschitzWith.of_dist_le_mul (K := ⟨b.L₁,b.L₁_pos.le⟩)
    (fun z w => by simpa only [dist_eq_norm, NNReal.coe_mk] using P.smooth_g z w)).continuous
  have hs : Measurable (fun z : (X × Y) × Bool => Adaptive.trueGradient P (z.2,z.1)) := by
    apply measurable_from_prod_countable
    intro flag
    cases flag
    · exact hfg.measurable.comp (packLinear (X := X) (Y := Y)).continuous.measurable
    · exact hgg.measurable.comp (packLinear (X := X) (Y := Y)).continuous.measurable
  exact hs.comp measurable_swap

variable {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

def fullJoint :
    HistoryOracle (Query := Adaptive.Query X Y) (History := History)
      (Obs := Joint X Y × History) (E := Joint X Y) b.σ where
  law := O.law
  markov := O.markov
  read := Prod.fst
  read_measurable := measurable_fst
  truth := Adaptive.trueGradient P
  truth_measurable := trueGradient_measurable P
  update := fun z => z.2.2
  update_measurable := measurable_snd.comp measurable_snd
  square_integrable := O.square_integrable
  mean := O.centered
  variance := O.variance

def fullLaw : FullGradientLaw O.law
    (fun z => z.1.fst) (fun z => z.1.snd) b.σ :=
  FullGradientLaw.ofFullVector O.law Prod.fst (Adaptive.trueGradient P) measurable_fst
    (trueGradient_measurable P) b.σ
    (fun q h => ⟨O.square_integrable q h, O.centered q h, O.variance q h⟩)

def blockY (lower : Bool) :
    HistoryOracle (Query := X × Y) (History := History) (Obs := Joint X Y × History) (E := Y) b.σ :=
  ((fullLaw P O).yOracle (fullLaw P O).ry_measurable
    (fun z => z.2.2) (measurable_snd.comp measurable_snd)).requery
      (fun q => (lower,q)) (measurable_const.prodMk measurable_id)

def blockX (lower : Bool) :
    HistoryOracle (Query := X × Y) (History := History) (Obs := Joint X Y × History) (E := X) b.σ :=
  ((fullLaw P O).xOracle (fullLaw P O).rx_measurable
    (fun z => z.2.2) (measurable_snd.comp measurable_snd)).requery
      (fun q => (lower,q)) (measurable_const.prodMk measurable_id)

theorem lowerY_truth (q : X × Y) : (blockY P O true).truth q = P.primitive.gy q.1 q.2 := rfl
theorem lowerX_truth (q : X × Y) : (blockX P O true).truth q = P.primitive.gx q.1 q.2 := rfl
theorem upperY_truth (q : X × Y) : (blockY P O false).truth q = P.primitive.fy q.1 q.2 := rfl
theorem upperX_truth (q : X × Y) : (blockX P O false).truth q = P.primitive.fx q.1 q.2 := rfl

/-- Each lower block observation uses precisely the original g-call law. -/
theorem lowerY_law (q : X × Y) (h : History) :
    (blockY P O true).law (q,h) = O.law ((true,q),h) := rfl

theorem blockY_update (flag : Bool) (q : X × Y) (h : History) (z : Joint X Y × History) :
    (blockY P O flag).update ((q,h),z) = z.2 := rfl

end Smoothness2601.InnerOracle
