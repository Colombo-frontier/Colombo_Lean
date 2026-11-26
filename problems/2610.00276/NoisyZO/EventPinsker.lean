import NoisyZO.BinaryPinsker
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Event form of Pinsker's inequality

The scalar binary inequality is lifted to probability measures by mapping a measurable event to
`Bool` and applying the data-processing inequality for Kullback--Leibler divergence.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace NoisyZO

noncomputable section

private lemma mul_log_div_eq {x y : ℝ} (hy : y ≠ 0) :
    x * Real.log (x / y) = -x * Real.log x⁻¹ - x * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_div hx hy, Real.log_inv]
    ring

/-- On the two-point space, mathlib's measure-theoretic KL divergence is the usual binary
relative entropy. -/
theorem toReal_klDiv_bool_eq_binaryRelativeEntropy
    (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq0 : 0 < ν.real {true}) (hq1 : ν.real {true} < 1) :
    (InformationTheory.klDiv μ ν).toReal =
      binaryRelativeEntropy (μ.real {true}) (ν.real {true}) := by
  let p : ℝ := μ.real {true}
  let q : ℝ := ν.real {true}
  have hμcomp := probReal_add_probReal_compl (μ := μ) (measurableSet_singleton true)
  have hνcomp := probReal_add_probReal_compl (μ := ν) (measurableSet_singleton true)
  have hμfalse : μ.real {false} = 1 - p := by
    change μ.real {false} = 1 - μ.real {true}
    have hc : ({true} : Set Bool)ᶜ = {false} := by ext b <;> cases b <;> simp
    rw [hc] at hμcomp
    linarith
  have hνfalse : ν.real {false} = 1 - q := by
    change ν.real {false} = 1 - ν.real {true}
    have hc : ({true} : Set Bool)ᶜ = {false} := by ext b <;> cases b <;> simp
    rw [hc] at hνcomp
    linarith
  have hνtrue0 : ν {true} ≠ 0 := by
    intro h
    have : ν.real {true} = 0 := by simp [measureReal_def, h]
    linarith
  have hνfalse0 : ν {false} ≠ 0 := by
    intro h
    have hz : ν.real {false} = 0 := by simp [measureReal_def, h]
    rw [hνfalse] at hz
    dsimp only [q] at hz
    linarith
  let density : Bool → ℝ≥0∞ := fun b ↦ μ {b} / ν {b}
  have hdensity_meas : Measurable density := measurable_of_finite _
  have hwith : ν.withDensity density = μ := by
    apply Measure.ext_of_singleton
    intro b
    rw [withDensity_apply density (measurableSet_singleton b), lintegral_singleton]
    dsimp only [density]
    apply ENNReal.div_mul_cancel
    · cases b
      · exact hνfalse0
      · exact hνtrue0
    · exact measure_ne_top ν {b}
  have hμν : μ ≪ ν := by
    rw [← hwith]
    exact withDensity_absolutelyContinuous ν density
  have hrn : μ.rnDeriv ν =ᵐ[ν] density := by
    rw [← hwith]
    exact Measure.rnDeriv_withDensity ν hdensity_meas
  calc
    (InformationTheory.klDiv μ ν).toReal =
        ∫ b, InformationTheory.klFun (μ.rnDeriv ν b).toReal ∂ν :=
      InformationTheory.toReal_klDiv_eq_integral_klFun hμν
    _ = ∫ b, InformationTheory.klFun (density b).toReal ∂ν := by
      apply integral_congr_ae
      filter_upwards [hrn] with b hb
      rw [hb]
    _ = ∑ b : Bool, ν.real {b} • InformationTheory.klFun (density b).toReal :=
      integral_fintype Integrable.of_finite
    _ = binaryRelativeEntropy p q := by
      have hq0' : q ≠ 0 := by dsimp only [q]; exact hq0.ne'
      have hq1' : 1 - q ≠ 0 := by dsimp only [q]; linarith
      have htrue : (density true).toReal = p / q := by
        simp only [density, ENNReal.toReal_div, p, q, measureReal_def]
      have hfalse : (density false).toReal = (1 - p) / (1 - q) := by
        rw [show (density false).toReal = μ.real {false} / ν.real {false} by
          simp only [density, ENNReal.toReal_div, measureReal_def]]
        rw [hμfalse, hνfalse]
      have htrueTerm :
          q * InformationTheory.klFun (p / q) =
            -p * Real.log p⁻¹ - p * Real.log q + q - p := by
        have hlog := mul_log_div_eq (x := p) hq0'
        calc
          q * InformationTheory.klFun (p / q) =
              p * Real.log (p / q) + q - p := by
            rw [InformationTheory.klFun_apply]
            field_simp [hq0']
            <;> ring
          _ = -p * Real.log p⁻¹ - p * Real.log q + q - p := by rw [hlog]
      have hfalseTerm :
          (1 - q) * InformationTheory.klFun ((1 - p) / (1 - q)) =
            -(1 - p) * Real.log (1 - p)⁻¹ -
              (1 - p) * Real.log (1 - q) + (1 - q) - (1 - p) := by
        have hlog := mul_log_div_eq (x := 1 - p) hq1'
        calc
          (1 - q) * InformationTheory.klFun ((1 - p) / (1 - q)) =
              (1 - p) * Real.log ((1 - p) / (1 - q)) +
                (1 - q) - (1 - p) := by
            rw [InformationTheory.klFun_apply]
            field_simp [hq1']
            <;> ring
          _ = -(1 - p) * Real.log (1 - p)⁻¹ -
              (1 - p) * Real.log (1 - q) + (1 - q) - (1 - p) := by rw [hlog]
      rw [show (∑ b : Bool, ν.real {b} •
          InformationTheory.klFun (density b).toReal) =
          ν.real {false} * InformationTheory.klFun (density false).toReal +
            ν.real {true} * InformationTheory.klFun (density true).toReal by
        simp [add_comm]]
      change ν.real {false} * InformationTheory.klFun (density false).toReal +
          q * InformationTheory.klFun (density true).toReal = _
      rw [hνfalse, htrue, hfalse, hfalseTerm, htrueTerm]
      simp only [binaryRelativeEntropy, Real.binEntropy]
      ring

/-- Indicator of a measurable event, with codomain the discrete two-point space. -/
noncomputable def eventBit {α : Type*} (E : Set α) (x : α) : Bool := by
  classical
  exact if x ∈ E then true else false

theorem measurable_eventBit {α : Type*} [MeasurableSpace α]
    {E : Set α} (hE : MeasurableSet E) : Measurable (eventBit E) := by
  classical
  unfold eventBit
  exact Measurable.ite hE measurable_const measurable_const

private theorem map_eventBit_true_real
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {E : Set α} (hE : MeasurableSet E) :
    (μ.map (eventBit E)).real {true} = μ.real E := by
  classical
  rw [map_measureReal_apply (measurable_eventBit hE) (measurableSet_singleton true)]
  congr 1
  ext x
  simp [eventBit]

/-- Event-level Pinsker inequality for probability measures with finite KL divergence. -/
theorem abs_probReal_sub_probReal_le_sqrt_klDiv
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set α} (hE : MeasurableSet E)
    (hKL : InformationTheory.klDiv μ ν ≠ ∞) :
    |μ.real E - ν.real E| ≤
      Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2) := by
  have hμν : μ ≪ ν := (InformationTheory.klDiv_ne_top_iff.mp hKL).1
  by_cases hq0eq : ν.real E = 0
  · have hνE : ν E = 0 := (measureReal_eq_zero_iff (measure_ne_top ν E)).mp hq0eq
    have hμE : μ E = 0 := hμν hνE
    have hp0 : μ.real E = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top μ E)).mpr hμE
    rw [hp0, hq0eq, sub_self, abs_zero]
    exact Real.sqrt_nonneg _
  by_cases hq1eq : ν.real E = 1
  · have hνcompReal : ν.real Eᶜ = 0 := by
      have h := probReal_add_probReal_compl (μ := ν) hE
      linarith
    have hνcomp : ν Eᶜ = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top ν Eᶜ)).mp hνcompReal
    have hμcomp : μ Eᶜ = 0 := hμν hνcomp
    have hμcompReal : μ.real Eᶜ = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top μ Eᶜ)).mpr hμcomp
    have hp1 : μ.real E = 1 := by
      have h := probReal_add_probReal_compl (μ := μ) hE
      linarith
    rw [hp1, hq1eq, sub_self, abs_zero]
    exact Real.sqrt_nonneg _
  have hq0 : 0 < ν.real E :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hq0eq)
  have hq1 : ν.real E < 1 :=
    lt_of_le_of_ne measureReal_le_one hq1eq
  let μb : Measure Bool := μ.map (eventBit E)
  let νb : Measure Bool := ν.map (eventBit E)
  let _ : IsProbabilityMeasure μb := by dsimp only [μb]; infer_instance
  let _ : IsProbabilityMeasure νb := by dsimp only [νb]; infer_instance
  have hμb : μb.real {true} = μ.real E := by
    exact map_eventBit_true_real μ hE
  have hνb : νb.real {true} = ν.real E := by
    exact map_eventBit_true_real ν hE
  have hmapKL : InformationTheory.klDiv μb νb ≤ InformationTheory.klDiv μ ν := by
    exact InformationTheory.klDiv_map_le μ ν (measurable_eventBit hE)
  have hmapFinite : InformationTheory.klDiv μb νb ≠ ∞ :=
    ne_top_of_le_ne_top hKL hmapKL
  have hmapReal :
      (InformationTheory.klDiv μb νb).toReal ≤
        (InformationTheory.klDiv μ ν).toReal :=
    (ENNReal.toReal_le_toReal hmapFinite hKL).mpr hmapKL
  have hp : μ.real E ∈ Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hbinary := two_sq_sub_le_binaryRelativeEntropy hp hq0 hq1
  have hbool := toReal_klDiv_bool_eq_binaryRelativeEntropy μb νb
    (by rwa [hνb]) (by rwa [hνb])
  have hquad :
      2 * (μ.real E - ν.real E) ^ 2 ≤
        (InformationTheory.klDiv μ ν).toReal := by
    calc
      2 * (μ.real E - ν.real E) ^ 2 ≤
          binaryRelativeEntropy (μ.real E) (ν.real E) := hbinary
      _ = (InformationTheory.klDiv μb νb).toReal := by
        rw [hbool, hμb, hνb]
      _ ≤ (InformationTheory.klDiv μ ν).toReal := hmapReal
  have hsq :
      (μ.real E - ν.real E) ^ 2 ≤
        (Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2)) ^ 2 := by
    rw [Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg (by norm_num))]
    nlinarith
  exact abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _)

end

end NoisyZO
