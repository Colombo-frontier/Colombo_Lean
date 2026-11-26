import Bilevel.HistorySFO
import Bilevel.ConditionalKernelRepair
import Bilevel.PrimitiveGeometry
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual full Euclidean conditional moments imply the block moment fields
used by the history-threaded algorithms, with the same variance budget. -/
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

def fullFst : Joint X Y →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X Y).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).toContinuousLinearMap
def fullSnd : Joint X Y →L[ℝ] Y :=
  (ContinuousLinearMap.snd ℝ X Y).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).toContinuousLinearMap

def FullGradientLaw.ofFullVector (K : Kernel (Query × History) Obs) [IsMarkovKernel K]
    (read : Obs → Joint X Y) (truth : Query → Joint X Y) (hr : Measurable read) (ht : Measurable truth)
    (σ : ℝ) (hgood : ∀ q h, ConditionalKernelRepair.Good K
      (fun z => read z.2-truth z.1.1) σ (q,h)) :
    FullGradientLaw K (fun o => (read o).fst) (fun o => (read o).snd) σ := by
  have hi (q : Query) (h : History) : Integrable (fun o => read o-truth q) (K (q,h)) := by
    have hm : Measurable (fun o => read o-truth q) := hr.sub measurable_const
    have hs : Integrable (fun o => ‖read o-truth q‖^2) (K (q,h)) := (hgood q h).1
    have hlp : MemLp (fun o => read o-truth q) 2 (K (q,h)) :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hs
    exact hlp.integrable (by norm_num)
  refine {
    truth_x := fun q => (truth q).fst
    truth_y := fun q => (truth q).snd
    truth_x_measurable := (fullFst (X := X) (Y := Y)).continuous.measurable.comp ht
    truth_y_measurable := (fullSnd (X := X) (Y := Y)).continuous.measurable.comp ht
    rx_measurable := (fullFst (X := X) (Y := Y)).continuous.measurable.comp hr
    ry_measurable := (fullSnd (X := X) (Y := Y)).continuous.measurable.comp hr
    square_integrable := ?_
    mean_x := ?_
    mean_y := ?_
    variance := ?_ }
  · intro q h
    simpa only [PrimitiveGeometry.norm_sq] using (hgood q h).1
  · intro q h
    have hh := (fullFst (X := X) (Y := Y)).integral_comp_comm (hi q h)
    have hm : (∫ o, read o-truth q ∂K (q,h)) = 0 := (hgood q h).2.1
    rw [hm, map_zero] at hh
    exact hh
  · intro q h
    have hh := (fullSnd (X := X) (Y := Y)).integral_comp_comm (hi q h)
    have hm : (∫ o, read o-truth q ∂K (q,h)) = 0 := (hgood q h).2.1
    rw [hm, map_zero] at hh
    exact hh
  · intro q h
    simpa only [PrimitiveGeometry.norm_sq] using (hgood q h).2.2

end Bilevel.Stateful
