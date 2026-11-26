import SecondOrder.OjaNoiseMoments

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

def ojaRandomNoise {Ω : Type*} {d : ℕ} (P : Parameters) (F : Point d → ℝ)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : Draws Ω N × (Fin d → Bool)) : ℝ :=
  ojaRayleighNoise P F f η x (rademacherInit w.2) N w.1

def ojaRandomMeanRayleighSum {Ω : Type*} {d : ℕ} (P : Parameters) (F : Point d → ℝ)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : Draws Ω N × (Fin d → Bool)) : ℝ :=
  ojaMeanRayleighSum P F f η x (rademacherInit w.2) N w.1

theorem ojaRandomRayleigh_decomposition {Ω : Type*} {d : ℕ} (P : Parameters)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : Draws Ω N × (Fin d → Bool)) :
    ojaRandomRayleighSum P f η x N w =
      ojaRandomMeanRayleighSum P F f η x N w + ojaRandomNoise P F f η x N w :=
  ojaRayleighSum_decomposition P F f η x (rademacherInit w.2) N w.1

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaRandomNoise_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : Point d × (Draws Ω N × (Fin d → Bool)) =>
      ojaRandomNoise P F f η w.1 N w.2) := by
  have hi : Measurable (fun w : Point d × (Draws Ω N × (Fin d → Bool)) =>
      ((w.1,rademacherInit w.2.2),w.2.1)) :=
    (measurable_fst.prodMk ((rademacherInit_measurable d).comp measurable_snd.snd)).prodMk
      measurable_snd.fst
  exact Measurable.comp
    (g := fun u : (Point d × Point d) × Draws Ω N => ojaRayleighNoise P F f η u.1.1 u.1.2 N u.2)
    (f := fun w : Point d × (Draws Ω N × (Fin d → Bool)) => ((w.1,rademacherInit w.2.2),w.2.1))
    (h.ojaRayleighNoise_measurable η N) hi

theorem CommonLoss.ojaRandomMeanRayleighSum_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : Point d × (Draws Ω N × (Fin d → Bool)) =>
      ojaRandomMeanRayleighSum P F f η w.1 N w.2) := by
  have he : (fun w : Point d × (Draws Ω N × (Fin d → Bool)) =>
      ojaRandomMeanRayleighSum P F f η w.1 N w.2) =
      (fun w => ojaRandomRayleighSum P f η w.1 N w.2 - ojaRandomNoise P F f η w.1 N w.2) := by
    funext w
    rw [ojaRandomRayleigh_decomposition]
    ring
  rw [he]
  exact (h.ojaRandomRayleighSum_measurable η N).sub (h.ojaRandomNoise_measurable η N)

theorem CommonLoss.ojaRandomNoise_abs_bound (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η) (N : ℕ) :
    ∀ᵐ w ∂ojaRandomLaw μ d N, ∀ x : Point d, |ojaRandomNoise P F f η x N w| ≤ (N:ℝ) := by
  have hh := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := signLaw d)).ae
    (h.ojaRayleighNoise_abs_bound hη N)
  filter_upwards [hh] with w hw
  intro x
  exact hw x (rademacherInit w.2) (rademacherInit_norm hd w.2)

theorem CommonLoss.ojaRandomNoise_pow_integrable (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η) (x : Point d) (N k : ℕ) :
    Integrable (fun w => ojaRandomNoise P F f η x N w ^ k) (ojaRandomLaw μ d N) := by
  have hi : Measurable (fun w : Draws Ω N × (Fin d → Bool) => (x,w)) :=
    measurable_const.prodMk measurable_id
  have hm : Measurable (ojaRandomNoise P F f η x N) := Measurable.comp
    (g := fun w : Point d × (Draws Ω N × (Fin d → Bool)) => ojaRandomNoise P F f η w.1 N w.2)
    (f := fun w : Draws Ω N × (Fin d → Bool) => (x,w)) (h.ojaRandomNoise_measurable η N) hi
  apply (integrable_const ((N:ℝ)^k)).mono' (hm.pow_const k).aestronglyMeasurable
  filter_upwards [h.ojaRandomNoise_abs_bound hd hη N] with w hw
  simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hw x) k

theorem CommonLoss.ojaRandomNoise_mean (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η) (x : Point d) (N : ℕ) :
    (∫ w, ojaRandomNoise P F f η x N w ∂ojaRandomLaw μ d N) = 0 := by
  have hi : Integrable (ojaRandomNoise P F f η x N) (ojaRandomLaw μ d N) := by
    simpa only [pow_one] using h.ojaRandomNoise_pow_integrable hd hη x N 1
  rw [ojaRandomLaw, integral_prod_symm _ hi]
  have hc (b : Fin d → Bool) :
      (∫ w, ojaRandomNoise P F f η x N (w,b) ∂drawsLaw μ N) = 0 :=
    h.ojaRayleighNoise_mean hη x (rademacherInit b) (rademacherInit_norm hd b) N
  simp_rw [hc]
  simp

theorem CommonLoss.ojaRandomNoise_second_moment (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η) (x : Point d) (N : ℕ) :
    (∫ w, ojaRandomNoise P F f η x N w ^ 2 ∂ojaRandomLaw μ d N) ≤ (N:ℝ) := by
  have hi := h.ojaRandomNoise_pow_integrable hd hη x N 2
  rw [ojaRandomLaw, integral_prod_symm _ hi]
  have hb := integral_mono_of_nonneg
    (Eventually.of_forall (fun b => integral_nonneg (fun w => sq_nonneg _)))
    (integrable_const (μ := signLaw d) (N:ℝ))
    (Eventually.of_forall (fun b => h.ojaRayleighNoise_second_moment hη x
      (rademacherInit b) (rademacherInit_norm hd b) N))
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hb

theorem CommonLoss.ojaRandomNoise_tail (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η) (x : Point d) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    ojaRandomLaw μ d N {w | r ≤ |ojaRandomNoise P F f η x N w|} ≤ ENNReal.ofReal ((N:ℝ)/r^2) :=
  abs_tail_of_second_moment (h.ojaRandomNoise_pow_integrable hd hη x N 2) hr
    (h.ojaRandomNoise_second_moment hd hη x N)

theorem CommonLoss.ojaRandomNoise_tail_real (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η) (x : Point d) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (ojaRandomLaw μ d N).real {w | r ≤ |ojaRandomNoise P F f η x N w|} ≤ (N:ℝ)/r^2 := by
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h.ojaRandomNoise_tail hd hη x N hr)
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ (N:ℝ)/r^2 by positivity)] using hb

end
end SecondOrder
