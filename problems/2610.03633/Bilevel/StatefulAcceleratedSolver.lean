import Bilevel.StatefulAcceleratedStages

/-! A finite accelerated solver with a fixed public initialization radius.
The executed history-dependent kernel, squared-distance guarantee, and exact
original-call count are certified for the same procedure. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators

namespace Bilevel.StatefulAccelerated
open Stateful AcceleratedInner

variable {History Obs E : Type*} [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := E) (History := History) (Obs := Obs) (E := E) σ)

def solve (μ M α : ℝ) (shift : E) (R r : ℝ) : Procedure E History E :=
  if R ≤ r then Procedure.pure id measurable_id else
    ((stages O μ M α shift (M * R ^ 2) (dyadicStageCount (M * R ^ 2) (μ * r ^ 2 / 4))).reparam
      (fun u => (u, u)) (measurable_id.prodMk measurable_id)).map
      (fun z => z.2.1) (measurable_fst.comp measurable_snd)

def solveCalls (μ M α σ R r : ℝ) : ℕ := if R ≤ r then 0 else
  stageLength α * ∑ s ∈ Finset.range (dyadicStageCount (M * R ^ 2) (μ * r ^ 2 / 4)),
    stageBatch M α σ (stageBudget (M * R ^ 2) (s + 1))

omit [CompleteSpace E] in
theorem solve_calls (μ M α : ℝ) (shift : E) (R r : ℝ) :
    (solve O μ M α shift R r).CallsEq (fun _ => solveCalls μ M α σ R r) := by
  unfold solve solveCalls
  split_ifs
  · exact Procedure.calls_pure _ _
  · exact Procedure.CallsEq.map _ _
      (Procedure.CallsEq.reparam _ _ (stages_calls O μ M α shift _ _) _
        (measurable_id.prodMk measurable_id)) _ _

theorem solve_distance (F : E → ℝ) (g : E → E) {μ M α R r : ℝ} (shift : E)
    (hM : 0 < M) (hμ : 0 < μ) (hμM : μ ≤ M)
    (hα : 0 < α) (hα1 : α ≤ 1) (hrel : α ^ 2 * M = μ)
    (htruth : ∀ y, O.truth y + shift = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (ys : E) (hmin : ∀ y, F ys ≤ F y) (hstationary : g ys = 0)
    (hR : 0 ≤ R) (hr : 0 < r) (u : E) (hinit : ‖u - ys‖ ^ 2 ≤ R ^ 2) (h : History) :
    Integrable (fun z => ‖z.1 - ys‖ ^ 2) ((solve O μ M α shift R r).law (u, h)) ∧
      (∫ z, ‖z.1 - ys‖ ^ 2 ∂(solve O μ M α shift R r).law (u, h)) ≤ r ^ 2 := by
  have hf : StronglyMeasurable (fun v : E => ‖v - ys‖ ^ 2) :=
    (by fun_prop : Measurable (fun v : E => ‖v - ys‖ ^ 2)).stronglyMeasurable
  unfold solve
  split_ifs with hearly
  · rw [Procedure.pure_law]
    have hm : StronglyMeasurable (fun z : Outcome E History => ‖z.1 - ys‖ ^ 2) :=
      (by fun_prop : Measurable (fun z : Outcome E History => ‖z.1 - ys‖ ^ 2)).stronglyMeasurable
    refine ⟨integrable_dirac' hm, ?_⟩
    rw [integral_dirac' _ _ hm]
    dsimp only [id_eq]
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
    have hd := stages_distance O F g shift hM hμ hα hα1 hU hrel htruth hg hlip hstrong
      ys hmin hstationary (u, u) hin h (dyadicStageCount (M * R ^ 2) (μ * r ^ 2 / 4))
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

/-- Explicit finite-schedule cost in the nontrivial initialization branch.
The variance contribution is independent of the initialization stage count. -/
theorem solveCalls_bound {μ M α σ R r : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hμM : μ ≤ M)
    (hα : 0 < α) (hα1 : α ≤ 1) (hrel : α ^ 2 * M = μ)
    (hr : 0 < r) (hRr : r < R) :
    (solveCalls μ M α σ R r : ℝ) ≤
      2 * (Real.log 4 + 1) * (dyadicStageCount (M * R ^ 2) (μ * r ^ 2 / 4) : ℝ) / α +
        32 * (Real.log 4 + 1) * σ ^ 2 / (μ ^ 2 * r ^ 2) := by
  have hR : 0 < R := hr.trans hRr
  have hT : 0 < μ * r ^ 2 / 4 := by positivity
  have hTU : μ * r ^ 2 / 4 < M * R ^ 2 := by
    have hrr : r ^ 2 < R ^ 2 := by nlinarith
    have h1 := mul_lt_mul_of_pos_left hrr hM
    have h2 := mul_le_mul_of_nonneg_right hμM (sq_nonneg r)
    nlinarith
  have hb := scheduled_calls_bound (σ := σ) hM hμ hα hα1 hrel hT hTU
  dsimp only at hb
  unfold solveCalls
  rw [if_neg (not_le_of_gt hRr), Nat.cast_mul, Nat.cast_sum]
  convert hb using 1
  field_simp
  ring

end Bilevel.StatefulAccelerated
