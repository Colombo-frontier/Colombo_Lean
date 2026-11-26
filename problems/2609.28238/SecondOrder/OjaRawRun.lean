import SecondOrder.OjaHvpRun
import SecondOrder.OjaEnergy

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

theorem normalizeProbe_smul_pos {d : ℕ} {c : ℝ} (hc : 0 < c) (v : Point d) :
    normalizeProbe (c • v) = normalizeProbe v := by
  simp only [normalizeProbe, norm_smul, Real.norm_of_nonneg hc.le, mul_inv, smul_smul]
  congr 1
  calc
    c⁻¹ * ‖v‖⁻¹ * c = (c⁻¹ * c) * ‖v‖⁻¹ := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc.ne', one_mul]

theorem ojaUpdate_smul {d : ℕ} (η c : ℝ) (A : Point d →L[ℝ] Point d) (v : Point d) :
    ojaUpdate η A (c • v) = c • ojaUpdate η A v := by
  simp [ojaUpdate, smul_add, smul_comm η c]

theorem ojaStep_normalize {d : ℕ} (η : ℝ) (A : Point d →L[ℝ] Point d) (v : Point d) :
    ojaStep η A (normalizeProbe v) = ojaStep η A v := by
  by_cases hv : v = 0
  · simp [hv, normalizeProbe, ojaStep, ojaUpdate]
  · change normalizeProbe (ojaUpdate η A (‖v‖⁻¹ • v)) = _
    rw [ojaUpdate_smul, normalizeProbe_smul_pos (inv_pos.mpr (norm_pos_iff.mpr hv))]
    rfl

/-- The same stochastic matrix product before normalization. -/
def ojaRawRun {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x v : Point d) : (N : ℕ) → Draws Ω N → Point d
  | 0, _ => v
  | N+1, w => ojaUpdate η (sampledShiftedHessian P f x w.2)
      (ojaRawRun P f η x v N w.1)

/-- Normalizing only at the end gives exactly the implemented HVP iterates,
including the total definition at a zero input. -/
theorem normalize_ojaRawRun {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) :
    normalizeProbe (ojaRawRun P f η x v N w) =
      ojaHvpRun P f η x (normalizeProbe v) N w := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change ojaStep η (sampledShiftedHessian P f x w.2) (ojaRawRun P f η x v N w.1) =
      ojaStep η (sampledShiftedHessian P f x w.2)
        (ojaHvpRun P f η x (normalizeProbe v) N w.1)
    rw [← ih, ojaStep_normalize]

/-- The sum uses the actual normalized direction queried before each draw. -/
def ojaSampledRayleighSum {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) : (N : ℕ) → Draws Ω N → ℝ
  | 0, _ => 0
  | N+1, w => ojaSampledRayleighSum P f η x v N w.1 +
      ⟪sampledShiftedHessian P f x w.2 (ojaHvpRun P f η x v N w.1),
        ojaHvpRun P f η x v N w.1⟫_ℝ

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaRawRun_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : (Point d × Point d) × Draws Ω N =>
      ojaRawRun P f η w.1.1 w.1.2 N w.2) := by
  induction N with
  | zero => exact measurable_fst.snd
  | succ N ih =>
    have hp : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        (w.1, w.2.1)) := measurable_fst.prodMk measurable_snd.fst
    have hx : Measurable (fun w : (Point d × Point d) × Draws Ω N => w.1.1) :=
      measurable_fst.fst
    have hg : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        ((w.1, w.2.1), w.2.2)) := hp.prodMk measurable_snd.snd
    have hd := (h.shifted_hvp_adaptive_measurable hx ih).comp hg
    have hu := ih.comp hp
    exact hu.add (hd.const_smul η)

/-- A pathwise exponential potential for the concrete fresh-HVP iteration. -/
theorem CommonLoss.ojaRawRun_potential (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    ∀ᵐ w ∂drawsLaw μ N, ∀ (x v : Point d),
      ‖ojaRawRun P f η x v N w‖^2 ≤ ‖v‖^2 * Real.exp
        ((2 * η + η^2) * ojaSampledRayleighSum P f η x (normalizeProbe v) N w) := by
  induction N with
  | zero => filter_upwards with w x v; simp [ojaRawRun, ojaSampledRayleighSum]
  | succ N ih =>
    have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae ih
    have hz := (Measure.quasiMeasurePreserving_snd (μ := drawsLaw μ N) (ν := μ)).ae
      h.sample_hessian_symmetric_bounded
    filter_upwards [hp, hz] with w hw hz
    intro x v
    have hf := shiftedHessian_firm (eigenHessianBound_pos P) (hz x).2
      (ojaRawRun P f η x v N w.1)
    have hstep := ojaUpdate_norm_sq_exp η hf
    rw [normalize_ojaRawRun] at hstep
    change ‖ojaUpdate η (sampledShiftedHessian P f x w.2) (ojaRawRun P f η x v N w.1)‖^2 ≤ _
    refine hstep.trans ?_
    calc
      _ ≤ (‖v‖^2 * Real.exp ((2 * η + η^2) *
          ojaSampledRayleighSum P f η x (normalizeProbe v) N w.1)) *
          Real.exp ((2 * η + η^2) *
            ⟪sampledShiftedHessian P f x w.2 (ojaHvpRun P f η x (normalizeProbe v) N w.1),
              ojaHvpRun P f η x (normalizeProbe v) N w.1⟫_ℝ) :=
        mul_le_mul_of_nonneg_right (hw x v) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; simp [ojaSampledRayleighSum]; ring

end
end SecondOrder
