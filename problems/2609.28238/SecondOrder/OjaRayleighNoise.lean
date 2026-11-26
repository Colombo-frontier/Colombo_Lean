import SecondOrder.RayleighNoise
import SecondOrder.OjaEmpiricalRayleigh

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- The cumulative discrepancy uses each direction before the fresh sample
that contributes its next scalar error. -/
def ojaRayleighNoise {Ω : Type*} {d : ℕ} (P : Parameters) (F : Point d → ℝ)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) : (N : ℕ) → Draws Ω N → ℝ
  | 0, _ => 0
  | N+1, w => ojaRayleighNoise P F f η x v N w.1 +
      shiftedRayleighError P F f x (ojaHvpRun P f η x v N w.1) w.2

def ojaMeanRayleighSum {Ω : Type*} {d : ℕ} (P : Parameters) (F : Point d → ℝ)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) : (N : ℕ) → Draws Ω N → ℝ
  | 0, _ => 0
  | N+1, w => ojaMeanRayleighSum P F f η x v N w.1 +
      ⟪shiftedHessian (eigenHessianBound P) (hessian F x) (ojaHvpRun P f η x v N w.1),
        ojaHvpRun P f η x v N w.1⟫_ℝ

theorem ojaRayleighSum_decomposition {Ω : Type*} {d : ℕ} (P : Parameters)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d)
    (N : ℕ) (w : Draws Ω N) :
    ojaSampledRayleighSum P f η x v N w =
      ojaMeanRayleighSum P F f η x v N w + ojaRayleighNoise P F f η x v N w := by
  induction N with
  | zero => simp [ojaSampledRayleighSum, ojaMeanRayleighSum, ojaRayleighNoise]
  | succ N ih =>
    simp only [ojaSampledRayleighSum, ojaMeanRayleighSum, ojaRayleighNoise,
      shiftedRayleighError, ih]
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaRayleighNoise_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : (Point d × Point d) × Draws Ω N =>
      ojaRayleighNoise P F f η w.1.1 w.1.2 N w.2) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have hp : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        (w.1,w.2.1)) := measurable_fst.prodMk measurable_snd.fst
    have hv := (h.ojaHvpRun_measurable η N).comp hp
    have hm : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        ((w.1.1,ojaHvpRun P f η w.1.1 w.1.2 N w.2.1),w.2.2)) :=
      (measurable_fst.fst.prodMk hv).prodMk measurable_snd.snd
    have he : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        shiftedRayleighError P F f w.1.1 (ojaHvpRun P f η w.1.1 w.1.2 N w.2.1) w.2.2) :=
      Measurable.comp
        (g := fun u : (Point d × Point d) × Ω => shiftedRayleighError P F f u.1.1 u.1.2 u.2)
        (f := fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
          ((w.1.1,ojaHvpRun P f η w.1.1 w.1.2 N w.2.1),w.2.2))
        h.shiftedRayleighError_measurable hm
    exact (ih.comp hp).add he

theorem CommonLoss.ojaMeanRayleighSum_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : (Point d × Point d) × Draws Ω N =>
      ojaMeanRayleighSum P F f η w.1.1 w.1.2 N w.2) := by
  have he : (fun w : (Point d × Point d) × Draws Ω N =>
      ojaMeanRayleighSum P F f η w.1.1 w.1.2 N w.2) =
      (fun w => ojaSampledRayleighSum P f η w.1.1 w.1.2 N w.2 -
        ojaRayleighNoise P F f η w.1.1 w.1.2 N w.2) := by
    funext w
    rw [ojaRayleighSum_decomposition]
    ring
  rw [he]
  exact (h.ojaSampledRayleighSum_measurable η N).sub (h.ojaRayleighNoise_measurable η N)

theorem CommonLoss.ojaRayleighNoise_abs_bound (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (N : ℕ) :
    ∀ᵐ w ∂drawsLaw μ N, ∀ (x v : Point d), ‖v‖ = 1 →
      |ojaRayleighNoise P F f η x v N w| ≤ (N : ℝ) := by
  induction N with
  | zero => filter_upwards with w x v hv; simp [ojaRayleighNoise]
  | succ N ih =>
    have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae ih
    have hu := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae
      (h.ojaHvpRun_ae_norm hη N)
    have hz := (Measure.quasiMeasurePreserving_snd (μ := drawsLaw μ N) (ν := μ)).ae
      h.shiftedRayleighError_abs_bound
    filter_upwards [hp,hu,hz] with w hw hu hz
    intro x v hv
    have he := hz x (ojaHvpRun P f η x v N w.1)
    rw [hu x v hv, one_pow] at he
    calc
      _ ≤ |ojaRayleighNoise P F f η x v N w.1| +
          |shiftedRayleighError P F f x (ojaHvpRun P f η x v N w.1) w.2| := abs_add _ _
      _ ≤ (N:ℝ)+1 := add_le_add (hw x v hv) he
      _ = _ := by simp

theorem CommonLoss.ojaRayleighNoise_integrable (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) (hv : ‖v‖ = 1) (N : ℕ) :
    Integrable (ojaRayleighNoise P F f η x v N) (drawsLaw μ N) := by
  have hg : Measurable (fun w : Draws Ω N => ((x,v),w)) := measurable_const.prodMk measurable_id
  have hm := (h.ojaRayleighNoise_measurable η N).comp hg
  apply (integrable_const (N:ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [h.ojaRayleighNoise_abs_bound hη N] with w hw
  exact hw x v hv

theorem CommonLoss.ojaRayleighNoise_sq_integrable (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) (hv : ‖v‖ = 1) (N : ℕ) :
    Integrable (fun w => ojaRayleighNoise P F f η x v N w ^ 2) (drawsLaw μ N) := by
  have hg : Measurable (fun w : Draws Ω N => ((x,v),w)) := measurable_const.prodMk measurable_id
  have hm := (h.ojaRayleighNoise_measurable η N).comp hg
  apply (integrable_const ((N:ℝ)^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [h.ojaRayleighNoise_abs_bound hη N] with w hw
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw x v hv) 2

end
end SecondOrder
