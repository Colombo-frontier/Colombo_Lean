import Bilevel.ProjectionObservation

/-! Joint Borelness of the explicit full-projection update formulas. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.ProjectionObservation
open EuclideanGaussian ProjectionPosterior
variable {Ω : Type*} [MeasurableSpace Ω]

theorem query_update_measurable (d T : ℕ) (Z : Ω → Frame d T) (hZ : Measurable Z)
    (w : Ω → Space d) (hw : Measurable w) (y : Ω → Fin T → ℝ) (hy : Measurable y) :
    Measurable (fun ω => queryUpdate d T (Z ω) (w ω) (y ω)) := by
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i).comp hZ).add (((measurable_pi_apply i).comp hy).smul hw)

theorem selected_column_measurable (d T : ℕ) (Z : Ω → Frame d T) (hZ : Measurable Z)
    (j : Ω → Fin T) (hj : Measurable j) : Measurable (fun ω => Z ω (j ω)) := by
  have he : Measurable (fun p : Frame d T × Fin T => p.1 p.2) :=
    measurable_from_prod_countable (fun i => measurable_pi_apply i)
  exact he.comp (hZ.prodMk hj)

theorem reveal_update_measurable (d T : ℕ) (Z : Ω → Frame d T) (hZ : Measurable Z)
    (j : Ω → Fin T) (hj : Measurable j) (y : Ω → Space d) (hy : Measurable y) :
    Measurable (fun ω => revealUpdate d T (Z ω) (j ω) (y ω)) := by
  classical
  have hzj := selected_column_measurable d T Z hZ j hj
  have hd := hy.sub hzj
  apply measurable_pi_lambda
  intro i
  have hzi := (measurable_pi_apply i).comp hZ
  have hs : MeasurableSet {ω | i=j ω} := by
    convert hj (measurableSet_singleton i) using 1
    ext ω
    simp [eq_comm]
  have hi : Measurable (fun ω => (if i=j ω then (1:ℝ) else 0)) :=
    measurable_const.ite hs measurable_const
  have hinner : Measurable (fun ω => ⟪Z ω i,Z ω (j ω)⟫) :=
    (continuous_fst.inner continuous_snd).measurable.comp (hzi.prodMk hzj)
  exact hzi.add (((hi.sub hinner).div (hd.norm.pow_const 2)).smul hd)

end Bilevel.ProjectionObservation
