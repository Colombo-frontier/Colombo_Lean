import FreshGradientMinimax.ParameterAccuracy
import FreshGradientMinimax.QuadraticFamily
import FreshGradientMinimax.Calculus

/-! F.3 instantiated for the actual random dual quadratics used in F.4.
The objective's derivative, smooth/strong constants, minimizer and its
measurability are all derived. The program uses only the known quadratic
coefficient and original fresh-gradient calls. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {dx dy : ℕ}

def dualQuadraticCorrection (a : ℝ) (z : Euclid dy × Euclid dy) : Euclid dy := a • z.2 - z.1

theorem dualQuadraticCorrection_continuous (a : ℝ) : Continuous (dualQuadraticCorrection (dy := dy) a) :=
  (continuous_const.smul continuous_snd).sub continuous_fst

def quadraticValueProgram (dx dy : ℕ) (ℓ α σ μ a e E₀ : ℝ) :
    OracleProgram dx dy (Euclid dy × Joint dx dy) (Euclid dy × Joint dx dy) :=
  parameterValueSolverProgram dx dy ℓ α σ (μ + a) (5 * ℓ + a) e E₀
    (dualQuadraticCorrection a) (dualQuadraticCorrection_continuous a).measurable

namespace SCObjective
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem effective_model (hfast : ℓ / 4 ≤ α) :
    SmoothStrongModel S.effectiveValue (gradient S.effectiveValue) μ (5 * ℓ) := by
  constructor
  · intro x
    rw [S.true_effective_gradient]
    exact S.effectiveValue_hasFDerivAt x
  · intro x y
    rw [S.true_effective_gradient]
    exact S.effective_strong x y
  · intro x y
    rw [S.true_effective_gradient]
    have h := (abs_le.mp (smooth_taylor_remainder S.effectiveValue_hasFDerivAt
      (S.effectiveGradient_lip_five hfast) x (y - x))).2
    rw [add_sub_cancel] at h
    linarith

def dualQuadraticMin (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a) : Euclid dy → Euclid dy :=
  (S.effective_model hfast).quadraticMin a (add_pos_of_pos_of_nonneg S.μ_pos ha)

theorem dualQuadraticMin_continuous (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a) :
    Continuous (S.dualQuadraticMin hfast a ha) :=
  (S.effective_model hfast).quadraticMin_continuous _ _

theorem dualQuadraticMin_minimizes (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a) (b y : Euclid dy) :
    quadraticFamily S.effectiveValue a b (S.dualQuadraticMin hfast a ha b) ≤ quadraticFamily S.effectiveValue a b y :=
  (S.effective_model hfast).quadraticMin_minimizes _ _ _ _

theorem dualQuadratic_model (hfast : ℓ / 4 ≤ α) (a : ℝ) (b : Euclid dy) :
    SmoothStrongModel (quadraticFamily S.effectiveValue a b)
      (fun y => gradient S.effectiveValue y + dualQuadraticCorrection a (b, y)) (μ + a) (5 * ℓ + a) := by
  have hfun : quadraticGradient (gradient S.effectiveValue) a b =
      fun y => gradient S.effectiveValue y + dualQuadraticCorrection a (b, y) := by
    funext y
    dsimp [quadraticGradient, dualQuadraticCorrection]
    module
  rw [← hfun]
  exact (S.effective_model hfast).quadratic_model a b

theorem quadraticValueProgram_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {a e E₀ : ℝ} (ha : 0 ≤ a) (he : 0 < e)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.parameterEnergy (fun z => quadraticFamily S.effectiveValue a z.1 z.2)
      (μ + a) (S.dualQuadraticMin hfast a ha)) ν)
    (hEnergy : (∫ z, S.parameterEnergy (fun z => quadraticFamily S.effectiveValue a z.1 z.2)
      (μ + a) (S.dualQuadraticMin hfast a ha) z ∂ν) ≤ E₀) :
    Integrable (fun t : (Euclid dy × Joint dx dy) × ℕ =>
      quadraticFamily S.effectiveValue a t.1.1 t.1.2.2 -
        quadraticFamily S.effectiveValue a t.1.1 (S.dualQuadraticMin hfast a ha t.1.1))
      ((quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν) ∧
    Integrable (fun t : (Euclid dy × Joint dx dy) × ℕ => S.fastError (μ + a) t.1.2)
      ((quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, quadraticFamily S.effectiveValue a t.1.1 t.1.2.2 -
      quadraticFamily S.effectiveValue a t.1.1 (S.dualQuadraticMin hfast a ha t.1.1)
      ∂(quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν) ≤ e ∧
    (∫ t, S.fastError (μ + a) t.1.2
      ∂(quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν) ≤ e := by
  have hmH : μ + a ≤ 5 * ℓ + a := by have := S.μ_le_L; have := S.L_pos; linarith
  exact S.parameterValueSolverProgram_accuracy O hαℓ hfast (add_pos_of_pos_of_nonneg S.μ_pos ha) hmH he
    (dualQuadraticCorrection a) (dualQuadraticCorrection_continuous a).measurable
    (fun z => quadraticFamily S.effectiveValue a z.1 z.2)
    ((S.effective_model hfast).quadraticFamily_joint_continuous a).measurable
    (S.dualQuadratic_model hfast a) (S.dualQuadraticMin hfast a ha)
    (S.dualQuadraticMin_continuous hfast a ha).measurable (S.dualQuadraticMin_minimizes hfast a ha)
    ν hInit hEnergy

theorem quadraticValueProgram_calls_rate (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {a e E₀ : ℝ} (ha : 0 ≤ a) (haL : a ≤ 15 * ℓ)
    (he : 0 < e) (hE₀ : 0 ≤ E₀) (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂(quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν) ≤
      10 ^ 70 * valueLogFactor ℓ σ (μ + a) e ^ 3 *
        (Real.sqrt ((5 * ℓ + a) / (μ + a)) * Real.log (2 + E₀ / e) + σ ^ 2 / ((μ + a) * e)) := by
  have hmH : μ + a ≤ 5 * ℓ + a := by have := S.μ_le_L; have := S.L_pos; linarith
  exact S.parameterValueSolverProgram_calls_rate O hfast (add_pos_of_pos_of_nonneg S.μ_pos ha) hmH
    (by linarith) he hE₀ _ _ ν

end SCObjective
end FreshGradientMinimax
