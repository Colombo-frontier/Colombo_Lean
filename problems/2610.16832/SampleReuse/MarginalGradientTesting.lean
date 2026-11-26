import SampleReuse.MarginalGradientAdmissible
import SampleReuse.BinaryTesting

open SecondOrder MeasureTheory
open scoped Classical InnerProductSpace

namespace SampleReuse
noncomputable section

variable {d : ℕ}

theorem marginal_negative_stationary_positive {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) {x : Point d}
    (hs : ‖gradient (marginalLoss ε v (-2*ε)) x‖ ≤ ε) : 0 < ⟪v,x⟫_ℝ := by
  have he : marginalLoss ε (-v) (2*ε) = marginalLoss ε v (-2*ε) := by
    funext x
    simp only [marginalLoss,inner_neg_left]
    ring
  have hn : ‖gradient (marginalLoss ε (-v) (2*ε)) x‖ ≤ ε := by rwa [he]
  have hh := marginal_positive_stationary_negative hε (by simpa using hv) hn
  rw [inner_neg_left] at hh
  linarith

def marginalClassify (v : Point d) (x : Point d) : Bool := if ⟪v,x⟫_ℝ < 0 then true else false

theorem marginalClassify_measurable (v : Point d) : Measurable (marginalClassify v) :=
  Measurable.ite (measurableSet_lt (innerSL ℝ v).continuous.measurable measurable_const)
    measurable_const measurable_const

/-- Optimization success yields an observable correct classification of the
hidden sign; no Hessian observation can reveal that sign directly. -/
theorem marginal_stationary_classifies {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (θ : Bool) {x : Point d}
    (hs : ‖gradient (marginalLoss ε v (2*ε*signValue θ)) x‖ ≤ ε) :
    marginalClassify v x = θ := by
  cases θ with
  | false =>
    have hn : ‖gradient (marginalLoss ε v (-2*ε)) x‖ ≤ ε := by
      simpa [signValue,mul_neg_one,neg_mul] using hs
    have hh := marginal_negative_stationary_positive hε hv hn
    simp only [marginalClassify,if_neg (not_lt_of_ge hh.le)]
  | true =>
    have hn : ‖gradient (marginalLoss ε v (2*ε)) x‖ ≤ ε := by simpa [signValue] using hs
    simp only [marginalClassify,if_pos (marginal_positive_stationary_negative hε hv hn)]

theorem marginal_hessian_no_information (ε : ℝ) (v : Point d) (z z' : ℝ) (x : Point d) :
    hessian (marginalLoss ε v z) x = hessian (marginalLoss ε v z') x := by
  rw [marginalLoss_hessian,marginalLoss_hessian]

theorem marginal_fair_classification_probability (v : Point d) (x : Point d) :
    (PMF.uniformOfFintype Bool).toMeasure.real {θ | marginalClassify v x = θ} = 1/2 := by
  have he : {θ : Bool | marginalClassify v x = θ} = {marginalClassify v x} := by
    ext θ
    simp only [Set.mem_setOf_eq,Set.mem_singleton_iff,eq_comm]
  rw [he,measureReal_def,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply]

end
end SampleReuse
