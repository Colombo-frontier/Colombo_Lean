import SecondOrder.OjaProduct
import SecondOrder.OjaRandomInit
import SecondOrder.OjaGrowthScale

open MeasureTheory Filter
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaProduct_adjoint_apply_measurable (h : CommonLoss μ P ν F f)
    (η : ℝ) (x g : Point d) (N : ℕ) :
    Measurable (fun w : Draws Ω N => ContinuousLinearMap.adjoint (ojaProduct P f η x N w) g) := by
  have hi : Measurable (fun w : Draws Ω N => (x,w)) := measurable_const.prodMk measurable_id
  have hL : Measurable (fun w : Draws Ω N => ojaProduct P f η x N w) :=
    Measurable.comp (g := fun w : Point d × Draws Ω N => ojaProduct P f η w.1 N w.2)
      (f := fun w : Draws Ω N => (x,w)) (h.ojaProduct_measurable η N) hi
  exact measurable_point_adjoint_apply (d := d)
    (L := fun w : Draws Ω N => ojaProduct P f η x N w) hL g

/-- Equality of the lower-tail probabilities, obtained from the actual
sample reversal and the almost-sure Hessian symmetry. -/
theorem CommonLoss.ojaProduct_adjoint_tail (h : CommonLoss μ P ν F f)
    (η : ℝ) (x g : Point d) (N : ℕ) (a : ℝ) :
    drawsLaw μ N {w | ‖ContinuousLinearMap.adjoint (ojaProduct P f η x N w) g‖^2 ≤ a} =
      drawsLaw μ N {w | ‖ojaRawRun P f η x g N w‖^2 ≤ a} := by
  have hi : Measurable (fun w : Draws Ω N => ((x,g),w)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun w : Draws Ω N => ojaRawRun P f η x g N w) :=
    (h.ojaRawRun_measurable η N).comp hi
  have hS : MeasurableSet {w : Draws Ω N | ‖ojaRawRun P f η x g N w‖^2 ≤ a} :=
    measurableSet_le (hm.norm.pow_const 2) measurable_const
  calc
    _ = drawsLaw μ N {w | ‖ojaRawRun P f η x g N (reverseDraws N w)‖^2 ≤ a} := by
      apply measure_congr
      filter_upwards [h.ojaProduct_adjoint_reverse η x N] with w hw
      apply propext
      change (_ ≤ a) ↔ (_ ≤ a)
      rw [hw, ojaProduct_apply]
    _ = _ := (reverseDraws_measurePreserving μ N).measure_preimage hS.nullMeasurableSet

/-- This growth guarantee is for the implemented independent-sign seed,
not for an eigenvector supplied to the algorithm. -/
theorem CommonLoss.ojaRandomRawRun_growth (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η p : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Point d) (N : ℕ)
    (hscale : η^2 * topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) *
      (N : ℝ) ≤ p / 100) :
    (1-p)/12 ≤ (ojaRandomLaw μ d N).real
      {w | (1 + η * topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)))^(2*N)/4 ≤
        ‖ojaRandomRawRun P f η x N w‖^2} := by
  obtain ⟨g,hg,hgrowth⟩ := h.ojaRawRun_top_growth hd hη hη1 hp hp1 x N hscale
  let a : ℝ := (1 + η * topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)))^(2*N)
  let B : Set (Draws Ω N) := {w | ‖ContinuousLinearMap.adjoint (ojaProduct P f η x N w) g‖^2 ≤ a/2}
  let S : Set (Draws Ω N × (Fin d → Bool)) := {w | a/4 ≤ ‖ojaRandomRawRun P f η x N w‖^2}
  have hB : MeasurableSet B := measurableSet_le
    ((h.ojaProduct_adjoint_apply_measurable η x g N).norm.pow_const 2) measurable_const
  have hi : Measurable (fun w : Draws Ω N × (Fin d → Bool) => (x,w)) :=
    measurable_const.prodMk measurable_id
  have hraw : Measurable (fun w : Draws Ω N × (Fin d → Bool) => ojaRandomRawRun P f η x N w) :=
    (h.ojaRandomRawRun_measurable η N).comp hi
  have hS : MeasurableSet S := measurableSet_le measurable_const (hraw.norm.pow_const 2)
  have hbad : drawsLaw μ N B ≤ ENNReal.ofReal p := by
    rw [show B = {w | ‖ContinuousLinearMap.adjoint (ojaProduct P f η x N w) g‖^2 ≤ a/2} from rfl,
      h.ojaProduct_adjoint_tail η x g N (a/2)]
    exact hgrowth
  have hgood : 1-p ≤ (drawsLaw μ N).real Bᶜ := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    rw [ENNReal.toReal_ofReal hp] at hb
    rw [measureReal_compl hB, measureReal_univ_eq_one]
    exact sub_le_sub_left hb 1
  have hsections : ∀ z ∈ Bᶜ, (1:ℝ)/12 ≤ (signLaw d).real {w | (z,w) ∈ S} := by
    intro z hz
    have hz' : a/2 < ‖ContinuousLinearMap.adjoint (ojaProduct P f η x N z) g‖^2 :=
      lt_of_not_ge hz
    refine (rademacherVector_operator_probability (ojaProduct P f η x N z) hg).trans ?_
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro w hw
    change a/4 ≤ ‖ojaRandomRawRun P f η x N (z,w)‖^2
    change ‖ContinuousLinearMap.adjoint (ojaProduct P f η x N z) g‖^2/2 ≤
      ‖ojaProduct P f η x N z (rademacherVector w)‖^2 at hw
    rw [ojaProduct_apply] at hw
    change a/4 ≤ ‖ojaRawRun P f η x (rademacherVector w) N z‖^2
    linarith
  have hs := product_success_of_sections (μ := drawsLaw μ N) (ρ := signLaw d) hB.compl hS hsections
  change (1-p)/12 ≤ ((drawsLaw μ N).prod (signLaw d)).real S
  have hm := mul_le_mul_of_nonneg_left hgood (show (0:ℝ) ≤ 1/12 by norm_num)
  linarith

end
end SecondOrder
