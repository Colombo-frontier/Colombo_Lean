import Nonsmooth.Minimax
import Nonsmooth.HistoryPolicy
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def maximumValue {E : Type} [NormedAddCommGroup E] (R : ℝ) (f : E → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x : E, ‖x‖ ≤ R ∧ f x = v}

theorem maximumValue_eq {E : Type} [NormedAddCommGroup E] {R : ℝ} {f : E → ℝ}
    {x : E} (hx : ‖x‖ ≤ R) (hm : ∀ y, ‖y‖ ≤ R → f y ≤ f x) :
    maximumValue R f = f x := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro v ⟨y, hy, rfl⟩
  exact hm y hy

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The ball instance of the external Protasov theorem, including the manuscript's uniformity
and Borel-policy legality requirements. The algorithm and cap precede the unknown objective.
This predicate is discharged in PlaneRetraction by protasovBallInput_all_dimensions. -/
def ProtasovBallInput (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (C : ℝ) : Prop :=
  ∀ (ρ η : ℝ), 0 < ρ → 0 < η → η < 1 / 2 →
    ∃ (T : ℕ) (S : Type) (mS : MeasurableSpace S),
      letI := mS
      StandardBorelSpace S ∧ ∃ p : Policy Unit S (Feasible E ρ), p.IsMeasurable ∧
        (T : ℝ) ≤ C * (Module.finrank ℝ E : ℝ) ^ 2 *
          Real.log ((Module.finrank ℝ E : ℝ) + 1) * Real.log (1 / η) ∧
        ∀ f : E → ℝ, ContinuousOn f (Metric.closedBall 0 ρ) →
          ConvexOn ℝ (Metric.closedBall 0 ρ) f →
          (∃ x y : E, ‖x‖ ≤ ρ ∧ ‖y‖ ≤ ρ ∧ f x ≠ f y) →
          f (p.result (fun x => f x.val) () T).val - minimumValue ρ f ≤
            η * (maximumValue ρ f - minimumValue ρ f)

theorem log_four_mul_le {x : ℝ} (hx : 0 < x) :
    Real.log (4 * x) ≤ 2 * Real.log (Real.exp 1 + x) := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hsq : 4 * x ≤ (Real.exp 1 + x) ^ 2 := by
    nlinarith [sq_nonneg (x - 1), mul_nonneg (sub_nonneg.mpr he) hx.le]
  have h := Real.log_le_log (by positivity : 0 < 4 * x) hsq
  simpa only [Real.log_pow, Nat.cast_ofNat] using h


end
end Nonsmooth
