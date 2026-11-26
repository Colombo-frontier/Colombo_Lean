import FreshGradientMinimax.OuterProgram

/-! Every coarse solve in the actual outer program satisfies its expected
energy precondition. The warm envelope is independent of the cold energy. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem outerRunLaw_invariant (O : FreshOracle F σ) {Δ η Ec Ew : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hc : 0 < Ec) (hw : 0 < Ew)
    (hinit : F.proximalStartEnergy (recenterProximal (0 : Euclid dx × Joint dx dy)) ≤ Ec)
    (T : ℕ) (hW : outerWarmEnvelope Δ η T ≤ Ew) (n : ℕ) : n ≤ T →
    Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1) (outerRunLaw L σ μ η Ec Ew O.kernel n) ∧
    Integrable (fun p => F.proximalStartEnergy (recenterProximal p)) (outerRunLaw L σ μ η Ec Ew O.kernel n) ∧
    (∫ p, F.primalHeight Δ p.2.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel n) ≤ Δ + n * η ∧
    (∫ p, F.proximalStartEnergy (recenterProximal p) ∂outerRunLaw L σ μ η Ec Ew O.kernel n) ≤ outerStageEnvelope Ec Ew n := by
  induction n with
  | zero =>
    intro _
    rw [outerRunLaw_zero]
    refine ⟨integrable_dirac, integrable_dirac, ?_, ?_⟩
    · simp only [integral_dirac, Prod.fst_zero, Prod.snd_zero, F.primalHeight_zero, Nat.cast_zero, zero_mul, add_zero, le_refl]
    · simpa only [integral_dirac, outerStageEnvelope, ite_true] using hinit
  | succ n ih =>
    intro hn
    obtain ⟨hhi, hei, hhb, heb⟩ := ih (by omega)
    have he := outerStageEnvelope_pos hc hw n
    have hi := F.outerStepProgram_integrability O hΔ hη he _ hei heb hhi
    have hd := F.outerStepProgram_descent O hΔ hη he _ hei heb hhi
    have hb := F.outerStepProgram_energy_bound O hΔ hη he _ hei heb hhi
    have hhp := integral_nonneg (f := fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1)
      (fun p => F.primalHeight_nonneg hΔ p.2.1)
      (μ := (outerStepProgram dx dy L σ μ η (outerStageEnvelope Ec Ew n)).resultKernel O.kernel ∘ₘ outerRunLaw L σ μ η Ec Ew O.kernel n)
    have hmp := integral_nonneg (f := proximalMoveEnergy (dx := dx) (dy := dy) L) (fun p =>
      mul_nonneg F.L_pos.le (sq_nonneg ‖p.2.1 - p.1‖))
      (μ := (outerStepProgram dx dy L σ μ η (outerStageEnvelope Ec Ew n)).resultKernel O.kernel ∘ₘ outerRunLaw L σ μ η Ec Ew O.kernel n)
    have hrp := integral_nonneg (f := fun p : Euclid dx × Joint dx dy => F.proximalResidualEnergy p.1)
      (fun p => F.proximalResidualEnergy_nonneg p.1)
      (μ := (outerStepProgram dx dy L σ μ η (outerStageEnvelope Ec Ew n)).resultKernel O.kernel ∘ₘ outerRunLaw L σ μ η Ec Ew O.kernel n)
    change 0 ≤ ∫ p, proximalMoveEnergy L p ∂_ at hmp
    rw [outerRunLaw_succ]
    refine ⟨hi.1, hi.2.2.2, ?_, ?_⟩
    · push_cast
      linarith
    · rw [show outerStageEnvelope Ec Ew (n + 1) = Ew by simp [outerStageEnvelope]]
      have hn' : (n : ℝ) + 1 ≤ T := by exact_mod_cast hn
      have ht := mul_le_mul_of_nonneg_right hn' hη.le
      unfold outerWarmEnvelope at hW
      nlinarith only [hb, hd, hhp, hrp, hhb, ht, hW]

theorem outerRunLaw_gap (O : FreshOracle F σ) {Δ η Ec Ew : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hc : 0 < Ec) (hw : 0 < Ew)
    (hinit : F.proximalStartEnergy (recenterProximal (0 : Euclid dx × Joint dx dy)) ≤ Ec)
    (T : ℕ) (hW : outerWarmEnvelope Δ η T ≤ Ew) {n : ℕ} (hn : n < T) :
    Integrable F.proximalGap (outerRunLaw L σ μ η Ec Ew O.kernel (n + 1)) ∧
    (∫ p, F.proximalGap p ∂outerRunLaw L σ μ η Ec Ew O.kernel (n + 1)) ≤ η := by
  have hi := F.outerRunLaw_invariant O hΔ hη hc hw hinit T hW n hn.le
  rw [outerRunLaw_succ]
  exact F.outerStepProgram_gap O hη (outerStageEnvelope_pos hc hw n) _ hi.2.1 hi.2.2.2

theorem outerRunLaw_step_moments (O : FreshOracle F σ) {Δ η Ec Ew : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hc : 0 < Ec) (hw : 0 < Ew)
    (hinit : F.proximalStartEnergy (recenterProximal (0 : Euclid dx × Joint dx dy)) ≤ Ec)
    (T : ℕ) (hW : outerWarmEnvelope Δ η T ≤ Ew) {n : ℕ} (hn : n < T) :
    Integrable (proximalMoveEnergy L) (outerRunLaw L σ μ η Ec Ew O.kernel (n + 1)) ∧
    Integrable (fun p : Euclid dx × Joint dx dy => F.proximalResidualEnergy p.1)
      (outerRunLaw L σ μ η Ec Ew O.kernel (n + 1)) := by
  have hi := F.outerRunLaw_invariant O hΔ hη hc hw hinit T hW n hn.le
  have hs := F.outerStepProgram_integrability O hΔ hη (outerStageEnvelope_pos hc hw n) _ hi.2.1 hi.2.2.2 hi.1
  rw [outerRunLaw_succ]
  exact ⟨hs.2.1, hs.2.2.1⟩

theorem outerRunLaw_descent (O : FreshOracle F σ) {Δ η Ec Ew : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hc : 0 < Ec) (hw : 0 < Ew)
    (hinit : F.proximalStartEnergy (recenterProximal (0 : Euclid dx × Joint dx dy)) ≤ Ec)
    (T : ℕ) (hW : outerWarmEnvelope Δ η T ≤ Ew) {n : ℕ} (hn : n < T) :
    (∫ p, F.primalHeight Δ p.2.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel (n + 1)) +
      (∫ p, proximalMoveEnergy L p ∂outerRunLaw L σ μ η Ec Ew O.kernel (n + 1)) +
      (∫ p, F.proximalResidualEnergy p.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel (n + 1)) ≤
      (∫ p, F.primalHeight Δ p.2.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel n) + η := by
  have hi := F.outerRunLaw_invariant O hΔ hη hc hw hinit T hW n hn.le
  rw [outerRunLaw_succ]
  exact F.outerStepProgram_descent O hΔ hη (outerStageEnvelope_pos hc hw n) _ hi.2.1 hi.2.2.2 hi.1

end NCObjective
end FreshGradientMinimax
