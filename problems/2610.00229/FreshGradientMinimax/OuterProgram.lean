import FreshGradientMinimax.OuterStep

/-! The finite sequence of coarse solves is a single original-query
program. Only its first solve uses the cold initialization envelope. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def outerStageEnvelope (Ec Ew : ℝ) (j : ℕ) : ℝ := if j = 0 then Ec else Ew

def outerColdEnvelope (L μ Δ G η : ℝ) : ℝ := (3 + 2 * (L / μ)) * Δ + 2 * G ^ 2 / μ + η

def outerWarmEnvelope (Δ η : ℝ) (T : ℕ) : ℝ := 12 * η + 24 * (Δ + T * η)

def outerRunProgram (dx dy : ℕ) (L σ μ η Ec Ew : ℝ) : ℕ →
    OracleProgram dx dy (Euclid dx × Joint dx dy) (Euclid dx × Joint dx dy)
  | 0 => OracleProgram.pure id measurable_id
  | n + 1 => (outerRunProgram dx dy L σ μ η Ec Ew n).chain
      (outerStepProgram dx dy L σ μ η (outerStageEnvelope Ec Ew n))

def outerRunLaw {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) : Measure (Euclid dx × Joint dx dy) :=
  (outerRunProgram dx dy L σ μ η Ec Ew n).resultKernel K ∘ₘ Measure.dirac 0

instance outerRunLaw_probability {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsProbabilityMeasure (outerRunLaw L σ μ η Ec Ew K n) := by
  unfold outerRunLaw
  infer_instance

theorem outerRunLaw_zero {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    outerRunLaw L σ μ η Ec Ew K 0 = Measure.dirac 0 := by
  rw [outerRunLaw, outerRunProgram, OracleProgram.pure_result,
    Measure.deterministic_comp_eq_map measurable_id, Measure.map_id]

theorem outerRunLaw_succ {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    outerRunLaw L σ μ η Ec Ew K (n + 1) =
      (outerStepProgram dx dy L σ μ η (outerStageEnvelope Ec Ew n)).resultKernel K ∘ₘ
        outerRunLaw L σ μ η Ec Ew K n := by
  rw [outerRunLaw, outerRunProgram, OracleProgram.chain_result, ← Measure.comp_assoc]
  rfl

theorem outerRunLaw_original {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    ((outerRunProgram dx dy L σ μ η Ec Ew n).originalKernel K ∘ₘ Measure.dirac 0).map Prod.fst =
      outerRunLaw L σ μ η Ec Ew K n := OracleProgram.original_result_law _ _ _

theorem outerStageEnvelope_pos {Ec Ew : ℝ} (hc : 0 < Ec) (hw : 0 < Ew) (j : ℕ) :
    0 < outerStageEnvelope Ec Ew j := by unfold outerStageEnvelope; split <;> assumption

namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (F : NCObjective dx dy L μ)

theorem primalGap_parameter_nonneg {Δ : ℝ} (hΔ : F.PrimalGapAtMost Δ) : 0 ≤ Δ := by
  have h := hΔ 0
  simpa only [sub_self] using h

include F in
theorem outerColdEnvelope_pos {Δ G η : ℝ} (hΔ : 0 ≤ Δ) (hη : 0 < η) :
    0 < outerColdEnvelope L μ Δ G η := by
  have hL := F.L_pos
  have hμ := F.μ_pos
  unfold outerColdEnvelope
  positivity

theorem outerWarmEnvelope_pos {Δ η : ℝ} (hΔ : 0 ≤ Δ) (hη : 0 < η) (T : ℕ) :
    0 < outerWarmEnvelope Δ η T := by unfold outerWarmEnvelope; positivity

theorem outer_initial_energy {Δ G η : ℝ} (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 ≤ η) :
    F.proximalStartEnergy (recenterProximal (0 : Euclid dx × Joint dx dy)) ≤ outerColdEnvelope L μ Δ G η := by
  have h := F.initial_proximal_energy hΔ hG
  simp only [proximalStartEnergy, recenterProximal, Prod.fst_zero, Prod.snd_zero,
    SCObjective.saddleStartEnergy, F.proximalObjective_saddleU, F.proximalObjective_saddleV,
    zero_sub, norm_neg, outerColdEnvelope]
  linarith

end NCObjective
end FreshGradientMinimax
