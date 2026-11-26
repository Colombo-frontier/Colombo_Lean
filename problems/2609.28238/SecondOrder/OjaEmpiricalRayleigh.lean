import SecondOrder.OjaRandomGrowth

open MeasureTheory Filter
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def ojaRandomRayleighSum {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : Draws Ω N × (Fin d → Bool)) : ℝ :=
  ojaSampledRayleighSum P f η x (rademacherInit w.2) N w.1

theorem log_growth_of_potential {b D s : ℝ} (hb : 0 < b) (hD : 0 < D) (N : ℕ)
    (h : b^(2*N)/4 ≤ D * Real.exp s) :
    2*(N:ℝ)*Real.log b - Real.log (4*D) ≤ s := by
  have hmul : b^(2*N) ≤ (4*D)*Real.exp s := by linarith
  have hl := Real.log_le_log (pow_pos hb _) hmul
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, Real.log_pow] at hl
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hl
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaSampledRayleighSum_measurable (h : CommonLoss μ P ν F f)
    (η : ℝ) (N : ℕ) :
    Measurable (fun w : (Point d × Point d) × Draws Ω N =>
      ojaSampledRayleighSum P f η w.1.1 w.1.2 N w.2) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have hp : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        (w.1,w.2.1)) := measurable_fst.prodMk measurable_snd.fst
    have hx : Measurable (fun w : (Point d × Point d) × Draws Ω N => w.1.1) :=
      measurable_fst.fst
    have hv := h.ojaHvpRun_measurable η N
    have hg : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        ((w.1,w.2.1),w.2.2)) := hp.prodMk measurable_snd.snd
    have ha := (h.shifted_hvp_adaptive_measurable hx hv).comp hg
    exact (ih.comp hp).add
      ((continuous_fst.inner continuous_snd).measurable.comp (ha.prodMk (hv.comp hp)))

theorem CommonLoss.ojaRandomRayleighSum_measurable (h : CommonLoss μ P ν F f)
    (η : ℝ) (N : ℕ) :
    Measurable (fun w : Point d × (Draws Ω N × (Fin d → Bool)) =>
      ojaRandomRayleighSum P f η w.1 N w.2) := by
  exact (h.ojaSampledRayleighSum_measurable η N).comp
    ((measurable_fst.prodMk ((rademacherInit_measurable d).comp measurable_snd.snd)).prodMk
      measurable_snd.fst)

/-- The implemented random trajectory has a cumulative sampled-Rayleigh
lower bound with logarithmic dimension dependence and constant success.
The samples in this sum are the same ones used to update the iterates. -/
theorem CommonLoss.ojaRandomRayleighSum_lower (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η p : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Point d) (N : ℕ)
    (hscale : η^2 * topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) *
      (N : ℝ) ≤ p / 100) :
    (1-p)/12 ≤ (ojaRandomLaw μ d N).real {w |
      2*(N:ℝ)*Real.log (1 + η*topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x))) -
        Real.log (4*(d:ℝ)) ≤ (2*η+η^2)*ojaRandomRayleighSum P f η x N w} := by
  have hgrowth := h.ojaRandomRawRun_growth hd hη hη1 hp hp1 x N hscale
  have hℓ := (h.mean_shifted_top_eigenpair hd x).1
  have hb : 0 < 1 + η*topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) :=
    by positivity
  have hD : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hm : ojaRandomLaw μ d N
      {w | (1 + η*topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)))^(2*N)/4 ≤
        ‖ojaRandomRawRun P f η x N w‖^2} ≤
      ojaRandomLaw μ d N {w |
        2*(N:ℝ)*Real.log (1 + η*topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x))) -
          Real.log (4*(d:ℝ)) ≤ (2*η+η^2)*ojaRandomRayleighSum P f η x N w} := by
    apply measure_mono_ae
    filter_upwards [h.ojaRandomRawRun_potential η N] with w hw
    intro hg
    exact log_growth_of_potential hb hD N (hg.trans (hw x))
  exact hgrowth.trans (ENNReal.toReal_mono (measure_ne_top _ _) hm)

end
end SecondOrder
