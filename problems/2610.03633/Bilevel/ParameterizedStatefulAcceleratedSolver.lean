import Bilevel.ParameterizedStatefulAcceleratedStages

/-! Jointly measurable finite accelerated solver. Public radius and accuracy
fix the schedule; query location and linear tilt remain adaptive parameters. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Bilevel.ParameterizedStatefulAccelerated
open Stateful AcceleratedInner
variable {Param Query History Obs E : Type*}
  [MeasurableSpace Param] [MeasurableSpace Query] [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)
  (loc : Param × E → Query) (hloc : Measurable loc)
  (shift : Param → E) (hshift : Measurable shift)

def solve (μ M α R r : ℝ) : Procedure (Param × E) History E :=
  if R ≤ r then Procedure.pure Prod.snd measurable_snd else
    ((stages O loc hloc shift hshift μ M α (M * R ^ 2)
      (dyadicStageCount (M * R ^ 2) (μ * r ^ 2 / 4))).reparam
      (fun z => (z.1, (z.2, z.2))) (by fun_prop)).map
      (fun z => z.2.1) (measurable_fst.comp measurable_snd)

omit [CompleteSpace E] in
theorem solve_calls (μ M α R r : ℝ) :
    (solve O loc hloc shift hshift μ M α R r).CallsEq
      (fun _ => StatefulAccelerated.solveCalls μ M α σ R r) := by
  unfold solve StatefulAccelerated.solveCalls
  split_ifs
  · exact Procedure.calls_pure _ _
  · exact Procedure.CallsEq.map _ _
      (Procedure.CallsEq.reparam _ _ (stages_calls O loc hloc shift hshift μ M α _ _) _
        (by fun_prop)) _ _

theorem solve_distance (F : E → ℝ) (g : E → E) {μ M α R r : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hμM : μ ≤ M)
    (hα : 0 < α) (hα1 : α ≤ 1) (hrel : α ^ 2 * M = μ)
    (p : Param) (htruth : ∀ y, O.truth (loc (p, y)) + shift p = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (ys : E) (hmin : ∀ y, F ys ≤ F y) (hstationary : g ys = 0)
    (hR : 0 ≤ R) (hr : 0 < r) (u : E) (hinit : ‖u - ys‖ ^ 2 ≤ R ^ 2) (h : History) :
    Integrable (fun z => ‖z.1 - ys‖ ^ 2)
      ((solve O loc hloc shift hshift μ M α R r).law ((p, u), h)) ∧
      (∫ z, ‖z.1 - ys‖ ^ 2 ∂(solve O loc hloc shift hshift μ M α R r).law ((p, u), h)) ≤ r ^ 2 := by
  have hf : StronglyMeasurable (fun v : E => ‖v - ys‖ ^ 2) :=
    (by fun_prop : Measurable (fun v : E => ‖v - ys‖ ^ 2)).stronglyMeasurable
  unfold solve
  split_ifs with hearly
  · rw [Procedure.pure_law]
    have hm : StronglyMeasurable (fun z : Outcome E History => ‖z.1 - ys‖ ^ 2) :=
      (by fun_prop : Measurable (fun z : Outcome E History => ‖z.1 - ys‖ ^ 2)).stronglyMeasurable
    refine ⟨integrable_dirac' hm, ?_⟩
    rw [integral_dirac' _ _ hm]
    change ‖u - ys‖ ^ 2 ≤ r ^ 2
    nlinarith
  · have hRpos : 0 < R := hr.trans (lt_of_not_ge hearly)
    have hU : 0 < M * R ^ 2 := by positivity
    have hT : 0 < μ * r ^ 2 / 4 := by positivity
    have hTU : μ * r ^ 2 / 4 < M * R ^ 2 := by
      have hrr : r ^ 2 < R ^ 2 := by nlinarith [lt_of_not_ge hearly]
      have h1 := mul_lt_mul_of_pos_left hrr hM
      have h2 := mul_le_mul_of_nonneg_right hμM (sq_nonneg r)
      nlinarith
    have hin := initial_potential_bound F g hM.le hμM hg hlip u ys hstationary hinit
    have hd := stages_distance O loc hloc shift hshift F g hM hμ hα hα1 hU hrel p htruth
      hg hlip hstrong ys hmin hstationary (u, u) hin h (dyadicStageCount (M * R ^ 2) (μ * r ^ 2 / 4))
    have ht := (dyadicStageCount_bounds hT hTU).2.1
    have hfinal : (2 / μ) * stageBudget (M * R ^ 2)
        (dyadicStageCount (M * R ^ 2) (μ * r ^ 2 / 4)) ≤ r ^ 2 := by
      calc
        _ ≤ (2 / μ) * (μ * r ^ 2 / 4) := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = r ^ 2 / 2 := by field_simp; ring
        _ ≤ r ^ 2 := by nlinarith [sq_nonneg r]
    constructor
    · rw [Procedure.map_output_integrable_iff _ _ _ _ _ _ hf]
      exact hd.1
    · rw [Procedure.map_output_integral _ _ _ _ _ _ hf]
      exact hd.2.trans hfinal

end Bilevel.ParameterizedStatefulAccelerated
