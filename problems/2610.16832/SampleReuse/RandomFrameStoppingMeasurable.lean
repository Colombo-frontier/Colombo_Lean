import SampleReuse.RandomFrameExtendedCost
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
namespace SampleReuse.RandomFrame.StoppingFullJetPolicy

open MeasureTheory
open scoped Classical InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem measurableSet_halts (π : StoppingFullJetPolicy d Ω) {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) : MeasurableSet {ω | π.Halts f ω} := by
  simp only [Halts, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro n
  exact (π.measurable_stop_on_run hf n) (measurableSet_singleton true)

theorem cost_eq_floor_extendedCost (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (ω : Ω) :
    π.cost f ω = ⌊(π.extendedCost f ω).toReal⌋₊ := by
  by_cases hh : π.Halts f ω
  · rw [π.extendedCost_eq_cost f ω hh]
    simp
  · rw [π.extendedCost_eq_top f ω hh]
    simp [cost, hh]

theorem measurable_cost (π : StoppingFullJetPolicy d Ω) {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) : Measurable (π.cost f) := by
  have he : π.cost f = fun ω => ⌊(π.extendedCost f ω).toReal⌋₊ :=
    funext (π.cost_eq_floor_extendedCost f)
  rw [he]
  exact (π.measurable_extendedCost hf).ennreal_toReal.nat_floor

theorem measurable_outputFor (π : StoppingFullJetPolicy d Ω) {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) : Measurable (π.outputFor f) := by
  have hval (n : ℕ) : Measurable (fun ω => π.output n ω
      (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () n)) := by
    have hm := measurable_responseHistory π.query (fun _ (_ : Unit) => fullJet f)
      π.query_measurable (fun _ => (fullJet_measurable hf).comp measurable_snd) n
    exact (π.output_measurable n).comp
      (measurable_id.prodMk (hm.comp (measurable_id.prodMk measurable_const)))
  have hm : Measurable (fun p : Ω × ℕ => π.output p.2 p.1
      (responseHistory π.query (fun _ (_ : Unit) => fullJet f) p.1 () p.2)) :=
    measurable_from_prod_countable hval
  exact hm.comp (measurable_id.prodMk (π.measurable_cost hf))

theorem measurableSet_sosp {f : Point d → ℝ} (hf : ContDiff ℝ 2 f) (ε γ : ℝ) :
    MeasurableSet {x | IsSOSP f ε γ x} := by
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  have hH := hg.continuous_fderiv (by norm_num)
  have hs : IsClosed {x | IsSOSP f ε γ x} := by
    change IsClosed ({x | ‖gradient f x‖ ≤ ε} ∩
      {x | ∀ v : Point d, -γ*‖v‖^2 ≤ ⟪fderiv ℝ (gradient f) x v, v⟫_ℝ})
    apply (isClosed_le hg.continuous.norm continuous_const).inter
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const ((hH.clm_apply continuous_const).inner continuous_const)
  exact hs.measurableSet

theorem measurableSet_success (π : StoppingFullJetPolicy d Ω) {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) (ε γ : ℝ) :
    MeasurableSet {ω | π.Halts f ω ∧ IsSOSP f ε γ (π.outputFor f ω)} :=
  (π.measurableSet_halts hf).inter ((π.measurable_outputFor hf) (measurableSet_sosp hf ε γ))

end SampleReuse.RandomFrame.StoppingFullJetPolicy
