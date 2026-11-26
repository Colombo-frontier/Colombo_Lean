import FreshGradientMinimax.ProximalResult

/-! Integrability in the outer algorithm follows from nonnegative descent
quantities and the actual proximal gap. It is not an additional assumption
on the sequence of solver outputs. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def recenterProximal {dx dy : ℕ} (p : Euclid dx × Joint dx dy) : Euclid dx × Joint dx dy :=
  (p.2.1, p.2)

theorem recenterProximal_continuous {dx dy : ℕ} :
    Continuous (recenterProximal (dx := dx) (dy := dy)) :=
  continuous_snd.fst.prodMk continuous_snd

def proximalMoveEnergy {dx dy : ℕ} (L : ℝ) (p : Euclid dx × Joint dx dy) : ℝ := L * ‖p.2.1 - p.1‖ ^ 2

theorem proximalMoveEnergy_continuous {dx dy : ℕ} (L : ℝ) :
    Continuous (proximalMoveEnergy (dx := dx) (dy := dy) L) :=
  continuous_const.mul ((continuous_snd.fst.sub continuous_fst).norm.pow 2)

theorem integrable_nonneg_envelope {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    {f g : X → ℝ} (hf : Measurable f) (hfpos : ∀ x, 0 ≤ f x)
    (hg : Integrable g ρ) (hb : ∀ x, f x ≤ g x) : Integrable f ρ := by
  apply hg.mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfpos x)] using hb x)

namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (F : NCObjective dx dy L μ)

def primalHeight (Δ : ℝ) (u : Euclid dx) : ℝ := F.value u - F.value 0 + Δ

theorem primalHeight_continuous (Δ : ℝ) : Continuous (F.primalHeight Δ) :=
  ((continuous_iff_continuousAt.mpr (fun u => (F.value_hasFDerivAt u).continuousAt)).sub continuous_const).add continuous_const

theorem primalHeight_nonneg {Δ : ℝ} (hΔ : F.PrimalGapAtMost Δ) (u : Euclid dx) :
    0 ≤ F.primalHeight Δ u := by
  have h := hΔ u
  unfold primalHeight
  linarith

theorem primalHeight_zero (Δ : ℝ) : F.primalHeight Δ 0 = Δ := by simp [primalHeight]

def proximalResidualEnergy (c : Euclid dx) : ℝ := ‖proximalResidual L c (F.proxPoint c)‖ ^ 2 / (8 * L)

theorem proximalResidualEnergy_continuous : Continuous F.proximalResidualEnergy := by
  exact ((continuous_const.smul (continuous_id.sub F.proxPoint_continuous)).norm.pow 2).div_const (8 * L)

theorem proximalResidualEnergy_nonneg (c : Euclid dx) : 0 ≤ F.proximalResidualEnergy c := by
  unfold proximalResidualEnergy
  exact div_nonneg (sq_nonneg _) (by have := F.L_pos; positivity)

theorem proximal_height_descent (Δ : ℝ) (p : Euclid dx × Joint dx dy) :
    F.primalHeight Δ p.2.1 + proximalMoveEnergy L p + F.proximalResidualEnergy p.1 ≤
      F.primalHeight Δ p.1 + F.proximalGap p := by
  have h := F.proximal_gap_descent p.1 p.2.1 p.2.2
  unfold primalHeight proximalMoveEnergy proximalResidualEnergy proximalGap
  linarith

theorem proximal_warm_energy_recenter (p : Euclid dx × Joint dx dy) :
    F.proximalStartEnergy (recenterProximal p) ≤ 12 * F.proximalGap p + 24 * proximalMoveEnergy L p := by
  have h := F.proximal_warm_energy p.1 p.2.1 p.2.1 p.2.2
  simp only [proximalStartEnergy, SCObjective.saddleStartEnergy, recenterProximal,
    F.proximalObjective_saddleU, F.proximalObjective_saddleV, proximalGap, proximalMoveEnergy]
  rw [norm_sub_rev p.2.1 p.1]
  nlinarith only [h]

theorem proximal_output_integrability {Δ : ℝ} (hΔ : F.PrimalGapAtMost Δ)
    (ρ : Measure (Euclid dx × Joint dx dy))
    (hc : Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.1) ρ)
    (hg : Integrable F.proximalGap ρ) :
    Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1) ρ ∧
    Integrable (proximalMoveEnergy L) ρ ∧
    Integrable (fun p : Euclid dx × Joint dx dy => F.proximalResidualEnergy p.1) ρ ∧
    Integrable (fun p : Euclid dx × Joint dx dy => F.proximalStartEnergy (recenterProximal p)) ρ := by
  have hmpos (p : Euclid dx × Joint dx dy) : 0 ≤ proximalMoveEnergy L p :=
    mul_nonneg F.L_pos.le (sq_nonneg _)
  have hu := integrable_nonneg_envelope ((F.primalHeight_continuous Δ).measurable.comp measurable_snd.fst)
    (fun p => F.primalHeight_nonneg hΔ p.2.1) (hc.add hg) (fun p => by
      have h := F.proximal_height_descent Δ p
      have h1 := hmpos p
      have h2 := F.proximalResidualEnergy_nonneg p.1
      dsimp only [Pi.add_apply, Function.comp_apply]
      linarith)
  have hm := integrable_nonneg_envelope (proximalMoveEnergy_continuous L).measurable hmpos (hc.add hg) (fun p => by
      have h := F.proximal_height_descent Δ p
      have h1 := F.primalHeight_nonneg hΔ p.2.1
      have h2 := F.proximalResidualEnergy_nonneg p.1
      dsimp only [Pi.add_apply, Function.comp_apply]
      linarith)
  have hr := integrable_nonneg_envelope (F.proximalResidualEnergy_continuous.measurable.comp measurable_fst)
    (fun p => F.proximalResidualEnergy_nonneg p.1) (hc.add hg) (fun p => by
      have h := F.proximal_height_descent Δ p
      have h1 := F.primalHeight_nonneg hΔ p.2.1
      have h2 := hmpos p
      dsimp only [Pi.add_apply, Function.comp_apply]
      linarith)
  refine ⟨hu, hm, hr, ?_⟩
  exact integrable_nonneg_envelope
    (F.proximalStartEnergy_continuous.measurable.comp recenterProximal_continuous.measurable)
    (fun p => F.proximalStartEnergy_nonneg _) ((hg.const_mul 12).add (hm.const_mul 24)) F.proximal_warm_energy_recenter

theorem proximal_output_descent {Δ : ℝ} (hΔ : F.PrimalGapAtMost Δ)
    (ρ : Measure (Euclid dx × Joint dx dy))
    (hc : Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.1) ρ)
    (hg : Integrable F.proximalGap ρ) :
    (∫ p, F.primalHeight Δ p.2.1 ∂ρ) + (∫ p, proximalMoveEnergy L p ∂ρ) +
        (∫ p, F.proximalResidualEnergy p.1 ∂ρ) ≤
      (∫ p, F.primalHeight Δ p.1 ∂ρ) + ∫ p, F.proximalGap p ∂ρ := by
  have hi := F.proximal_output_integrability hΔ ρ hc hg
  have h := integral_mono ((hi.1.add hi.2.1).add hi.2.2.1) (hc.add hg) (F.proximal_height_descent Δ)
  simp only [Pi.add_apply] at h
  rw [integral_add (f := fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1 + proximalMoveEnergy L p)
    (g := fun p => F.proximalResidualEnergy p.1) (hi.1.add hi.2.1) hi.2.2.1,
    integral_add hi.1 hi.2.1, integral_add hc hg] at h
  exact h

theorem proximal_output_warm_energy {Δ : ℝ} (hΔ : F.PrimalGapAtMost Δ)
    (ρ : Measure (Euclid dx × Joint dx dy))
    (hc : Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.1) ρ)
    (hg : Integrable F.proximalGap ρ) :
    (∫ p, F.proximalStartEnergy (recenterProximal p) ∂ρ) ≤
      12 * (∫ p, F.proximalGap p ∂ρ) + 24 * (∫ p, proximalMoveEnergy L p ∂ρ) := by
  have hi := F.proximal_output_integrability hΔ ρ hc hg
  have h := integral_mono hi.2.2.2 ((hg.const_mul 12).add (hi.2.1.const_mul 24)) F.proximal_warm_energy_recenter
  simpa only [Pi.add_apply, integral_add (hg.const_mul 12) (hi.2.1.const_mul 24), integral_const_mul] using h

end NCObjective
end FreshGradientMinimax
