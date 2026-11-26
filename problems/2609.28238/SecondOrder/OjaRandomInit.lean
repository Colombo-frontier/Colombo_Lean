import SecondOrder.RademacherProjection
import SecondOrder.OjaRawRun

open MeasureTheory Filter
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

/-- The sign seed is independent of every loss sample. -/
def ojaRandomLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (d N : ℕ) :
    Measure (Draws Ω N × (Fin d → Bool)) := (drawsLaw μ N).prod (signLaw d)

instance ojaRandomLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d N : ℕ) :
    IsProbabilityMeasure (ojaRandomLaw μ d N) := by
  unfold ojaRandomLaw
  infer_instance

def ojaRandomRun {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x : Point d) (N : ℕ) (w : Draws Ω N × (Fin d → Bool)) : Point d :=
  ojaHvpRun P f η x (rademacherInit w.2) N w.1

def ojaRandomRawRun {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x : Point d) (N : ℕ) (w : Draws Ω N × (Fin d → Bool)) : Point d :=
  ojaRawRun P f η x (rademacherVector w.2) N w.1

def ojaRandomTrace {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x : Point d) (N : ℕ) (w : Draws Ω N × (Fin d → Bool)) :
    List (Ω × HvpQuery d) := ojaHvpTrace P f η x (rademacherInit w.2) N w.1

theorem ojaRandomTrace_length {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : Draws Ω N × (Fin d → Bool)) : (ojaRandomTrace P f η x N w).length = N :=
  ojaHvpTrace_length P f η x (rademacherInit w.2) N w.1

theorem ojaRandomRun_eq_reply_fold {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : Draws Ω N × (Fin d → Bool)) :
    (ojaRandomTrace P f η x N w).foldl
      (fun u q => ojaStepFromHvp P η u (hvpReply f q.1 q.2)) (rademacherInit w.2) =
        ojaRandomRun P f η x N w :=
  ojaHvpRun_eq_reply_fold P f η x (rademacherInit w.2) N w.1

theorem normalize_ojaRandomRawRun {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : Draws Ω N × (Fin d → Bool)) :
    normalizeProbe (ojaRandomRawRun P f η x N w) = ojaRandomRun P f η x N w :=
  normalize_ojaRawRun P f η x (rademacherVector w.2) N w.1

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaRandomRun_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : Point d × (Draws Ω N × (Fin d → Bool)) =>
      ojaRandomRun P f η w.1 N w.2) := by
  exact (h.ojaHvpRun_measurable η N).comp
    ((measurable_fst.prodMk ((rademacherInit_measurable d).comp measurable_snd.snd)).prodMk
      measurable_snd.fst)

theorem CommonLoss.ojaRandomRawRun_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : Point d × (Draws Ω N × (Fin d → Bool)) =>
      ojaRandomRawRun P f η w.1 N w.2) := by
  have hs : Measurable (@rademacherVector d) := measurable_of_finite _
  exact (h.ojaRawRun_measurable η N).comp
    ((measurable_fst.prodMk (hs.comp measurable_snd.snd)).prodMk measurable_snd.fst)

/-- The event holds for every query point simultaneously. -/
theorem CommonLoss.ojaRandomRun_ae_norm (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η) (N : ℕ) :
    ∀ᵐ w ∂ojaRandomLaw μ d N, ∀ x : Point d, ‖ojaRandomRun P f η x N w‖ = 1 := by
  have hg := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N)
    (ν := signLaw d)).ae (h.ojaHvpRun_ae_norm hη N)
  filter_upwards [hg] with w hw
  intro x
  exact hw x (rademacherInit w.2) (rademacherInit_norm hd w.2)

theorem CommonLoss.ojaRandomRawRun_potential (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    ∀ᵐ w ∂ojaRandomLaw μ d N, ∀ x : Point d,
      ‖ojaRandomRawRun P f η x N w‖^2 ≤ (d : ℝ) * Real.exp
        ((2*η+η^2) * ojaSampledRayleighSum P f η x (rademacherInit w.2) N w.1) := by
  have hg := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N)
    (ν := signLaw d)).ae (h.ojaRawRun_potential η N)
  filter_upwards [hg] with w hw
  intro x
  simpa only [rademacherVector_norm_sq] using hw x (rademacherVector w.2)

end
end SecondOrder
