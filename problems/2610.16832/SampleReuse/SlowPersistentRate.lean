import SampleReuse.SlowPersistentLower

/-! The integer cap is chosen from the concrete slow threshold; the
resulting expected budget has the displayed epsilon^{-3} D^{-1/4} rate. -/

open SecondOrder MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section

def slowRateCap (M : Parameters) (ε : ℝ) : ℕ := ⌊slowQueryThreshold M ε⌋₊

def slowExpectedConstant : ℝ := (5/12)*slowQueryConstant

theorem slowExpectedConstant_pos : 0 < slowExpectedConstant :=
  mul_pos (by norm_num) slowQueryConstant_pos

theorem slowRateCap_le (M : Parameters) {ε : ℝ} (hε : 0 < ε) :
    (slowRateCap M ε : ℝ) ≤ slowQueryThreshold M ε :=
  Nat.floor_le (slowQueryThreshold_pos M hε).le

theorem slowRateCap_rate (M : Parameters) (ε : ℝ) :
    ENNReal.ofReal (slowExpectedConstant*M.gap*(slowModelScale M)^2/
      (ε^3*(slowBlockSize M ε:ℝ)^(1/4:ℝ))) ≤
        (slowRateCap M ε+1:ℕ)*ENNReal.ofReal (5/12) := by
  have hf := Nat.lt_floor_add_one (slowQueryThreshold M ε)
  have hr : slowExpectedConstant*M.gap*(slowModelScale M)^2/
      (ε^3*(slowBlockSize M ε:ℝ)^(1/4:ℝ)) = (5/12)*slowQueryThreshold M ε := by
    unfold slowExpectedConstant slowQueryThreshold
    rw [slowAlpha_rpow]
    ring
  rw [hr]
  have hh : (5/12)*slowQueryThreshold M ε ≤ ((slowRateCap M ε+1:ℕ):ℝ)*(5/12) := by
    dsimp only [slowRateCap]
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [hf]
  apply (ENNReal.ofReal_le_ofReal hh).trans_eq
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]

theorem slow_persistent_expected_rate {H S Ξ : Type} [MeasurableSpace Ξ]
    (M : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions M ε)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → FirstOrderStoppingAlgorithm (slowBlockSize M ε) (slowLinks M ε) H S)
    (hE : ∀ Θ (table : Fin (slowRateCap M ε+1) → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)), MeasurableSet {ξ |
        ‖gradient (slowPopulation M ε Θ) (persistentOriginalOutput
          (firstOrderStoppingCapPolicy (P ξ) (slowRateCap M ε))
          Θ (slowAmplitude (slowBlockSize M ε) ε) (slowDilation (slowBlockSize M ε)) table
          (slowRateCap M ε))‖ ≤ ε})
    (hs : ∀ Θ n, Measurable (fun w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)) => (P w.1).stopOnRun (slowReply M ε Θ) w.2 n))
    (hsolve : ∀ Θ, (2/3:ℝ) ≤ (μ.prod (iidSampleTapeLaw (slowLaw M hc Θ))).real
      {w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)) |
        (P w.1).Halts (slowReply M ε Θ) w.2 ∧
        ‖gradient (slowPopulation M ε Θ) ((P w.1).outputFor (slowReply M ε Θ) w.2)‖ ≤ ε}) :
    ∃ Θ, Admissible (slowLaw M hc Θ).toMeasure M (slowPopulation M ε Θ) (slowSample M ε Θ) 0 ∧
      ENNReal.ofReal (slowExpectedConstant*M.gap*(slowModelScale M)^2/
        (ε^3*(slowBlockSize M ε:ℝ)^(1/4:ℝ))) ≤
        ∫⁻ w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)),
          (P w.1).extendedCost (slowReply M ε Θ) w.2 ∂μ.prod (iidSampleTapeLaw (slowLaw M hc Θ)) := by
  obtain ⟨Θ,ha,hb⟩ := slow_calibrated_expected_lower M hc μ P (slowRateCap M ε)
    (slowRateCap_le M hc.tolerance_pos) hE hs hsolve
  exact ⟨Θ,ha,(slowRateCap_rate M ε).trans hb⟩

end
end SampleReuse
