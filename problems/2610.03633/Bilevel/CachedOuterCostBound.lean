import Bilevel.CachedOuterTotalCalls

/-! Deterministic (almost-sure) and expected query bounds for the same actual
cached outer run, on all oracle histories, including accuracy failures. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOuterProcedure
open Stateful CachedBudgetCalibration

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

def publicRun (μ Lg Cf t D r rA δ η Λ La Δ ε : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) : Procedure Unit History (State X Y) :=
  run O μ Lg Cf t D r rA δ η Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε)
    q x₀ yinit (outerCount Λ Δ ε)

def publicCost (μ Lg σf σg D r rA δ η Λ La Δ ε : ℝ) (q : ℕ) : ℝ :=
  outerCount Λ Δ ε * estimatorCalls μ Lg σg D r δ q +
    2560*(1+La*Δ/ε^2)*anchorCalls μ Lg σf σg D rA η q

theorem publicRun_calls_bound (μ Lg Cf t D r rA δ η Λ La Δ ε : ℝ) (q : ℕ) [NeZero q]
    (hΛ : 0 < Λ) (hLa : 0 ≤ La) (hLaΛ : La ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (x₀ : X) (yinit : Y) (h : History) :
    ∀ᵐ z ∂(publicRun O μ Lg Cf t D r rA δ η Λ La Δ ε q x₀ yinit).law ((),h),
      (z.2.2:ℝ) ≤ publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q := by
  have hN := outerCount_pos Λ Δ ε
  filter_upwards [run_calls_actual O μ Lg Cf t D r rA δ η Λ (energyCap Λ Δ ε)
    (refreshRadius Λ La Δ ε) q x₀ yinit (outerCount Λ Δ ε) h] with z hz
  have hc := capped_anchor_budget hΛ hLa hLaΛ hΔ hε x₀ z.1.1 (outerCount Λ Δ ε-1) (Nat.sub_le _ _)
  have hr : (refreshCount Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε)
      x₀ (outerCount Λ Δ ε) z.1.1 : ℝ) ≤ 2560*(1+La*Δ/ε^2) := by
    simp only [refreshCount,if_neg (Nat.ne_of_gt hN),Nat.cast_add,Nat.cast_one]
    simpa only [add_comm] using hc
  rw [hz]
  push_cast
  exact add_le_add_left (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) _

theorem publicRun_costBound (μ Lg Cf t D r rA δ η Λ La Δ ε : ℝ) (q : ℕ) [NeZero q]
    (hΛ : 0 < Λ) (hLa : 0 ≤ La) (hLaΛ : La ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (x₀ : X) (yinit : Y) :
    (publicRun O μ Lg Cf t D r rA δ η Λ La Δ ε q x₀ yinit).CostBound
      (fun _ => publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q) := by
  intro p h
  cases p
  let B := publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q
  have hb := publicRun_calls_bound O μ Lg Cf t D r rA δ η Λ La Δ ε q
    hΛ hLa hLaΛ hΔ hε x₀ yinit h
  have hi : Integrable (fun z : Outcome (State X Y) History => (z.2.2:ℝ))
      ((publicRun O μ Lg Cf t D r rA δ η Λ La Δ ε q x₀ yinit).law ((),h)) := by
    have hm : Measurable (fun z : Outcome (State X Y) History => (z.2.2:ℝ)) :=
      (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_snd.comp measurable_snd)
    apply (integrable_const B).mono' hm.aestronglyMeasurable
    filter_upwards [hb] with z hz
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using hz
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae hi (integrable_const B) hb
  simpa only [integral_const,measureReal_univ_eq_one,one_smul] using hh

end Bilevel.CachedOuterProcedure
