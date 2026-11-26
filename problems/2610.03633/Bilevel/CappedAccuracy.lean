import Bilevel.CappedGoodEvent
import Bilevel.CappedMeasurability
import Bilevel.CachedUniformOutput

/-! Actual capped, independently uniform output under a simultaneous
estimator-accuracy probability certificate. The supplied vectors can be fully
adaptive and biased. Producing the certificate by SFO calls is separate.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Bilevel.CappedAccuracy
open CappedExecution

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν]

def bad (Λ cap ε : ℝ) (g : E → E) (x₀ : E) (G : ℕ → Ω → E) (N : ℕ) : Set Ω :=
  {ω | ∃ i < N, (run Λ cap x₀ (fun j => G j ω) i).stopped = false ∧
    ε/8 < ‖G i ω-g (run Λ cap x₀ (fun j => G j ω) i).point‖}

omit [CompleteSpace E] [IsProbabilityMeasure ν] in
theorem bad_measurable (Λ cap ε : ℝ) (g : E → E) (hg : Measurable g)
    (x₀ : E) (G : ℕ → Ω → E) (hG : ∀ i, Measurable (G i)) (N : ℕ) :
    MeasurableSet (bad Λ cap ε g x₀ G N) := by
  classical
  unfold bad
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i < N
  · simp only [hi, true_and]
    have hs := (run_measurable Λ cap x₀ G hG i).2.2
    have hx := (run_measurable Λ cap x₀ G hG i).1
    exact (hs (measurableSet_singleton false)).inter
      (measurableSet_lt measurable_const ((hG i).sub (hg.comp hx)).norm)
  · simp [hi]

theorem expected_gradient_norm (F : E → ℝ) (g : E → E) {Λ Δ lower ε δ : ℝ}
    (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hg : ∀ z, HasGradientAt F (g z) z)
    (hlip : ∀ z w, ‖g z-g w‖ ≤ Λ * ‖z-w‖)
    (hlower : ∀ z, lower ≤ F z) (x₀ : E) (hgap : F x₀-lower ≤ Δ)
    (G : ℕ → Ω → E) (hG : ∀ i, Measurable (G i))
    (N : ℕ) [NeZero N] (horizon : 32*Λ*Δ ≤ N*ε^2)
    (hprob : ν.real (bad Λ (16*Λ*Δ+N*ε^2) ε g x₀ G N) ≤ δ)
    (hbudget : δ * (Real.sqrt (2*Λ*Δ)+Real.sqrt (N*(16*Λ*Δ+N*ε^2))) ≤ ε/2) :
    Integrable (fun p : Fin N × Ω =>
      ‖g (output Λ (16*Λ*Δ+N*ε^2) x₀ (fun i => G i p.2) N p.1)‖)
        (StochasticOuter.outputLaw N ν) ∧
    (∫ p : Fin N × Ω,
      ‖g (output Λ (16*Λ*Δ+N*ε^2) x₀ (fun i => G i p.2) N p.1)‖
        ∂StochasticOuter.outputLaw N ν) ≤ ε := by
  have hN : 0 < N := Nat.pos_of_neZero N
  let cap := 16*Λ*Δ+N*ε^2
  have hc : 0 ≤ cap := by dsimp [cap]; positivity
  have hgLip : LipschitzWith ⟨Λ, hΛ.le⟩ g := (lipschitzWith_iff_norm_sub_le).mpr hlip
  have hgm := hgLip.continuous.measurable
  let loss : ℕ → Ω → ℝ := fun i ω => ‖g (output Λ cap x₀ (fun j => G j ω) N i)‖
  have hmeas : ∀ i < N, AEStronglyMeasurable (loss i) ν := by
    intro i _
    exact (hgm.comp (output_measurable Λ cap x₀ G hG N i)).norm.aestronglyMeasurable
  have hcap : ∀ i < N, ∀ ω, loss i ω ≤ Real.sqrt (2*Λ*Δ)+Real.sqrt (N*cap) := by
    intro i hi ω
    exact all_history_output_gradient F g hΛ hc hg hlip hlower x₀ hgap (fun j => G j ω) N i hi.le
  have hgood : ∀ ω ∉ bad Λ cap ε g x₀ G N,
      (∑ i ∈ Finset.range N, loss i ω)/N ≤ ε/2 := by
    intro ω hω
    apply CappedGoodEvent.good_output_average F g hΛ hΔ hε hg hlip hlower
      x₀ hgap (fun i => G i ω) N hN horizon
    intro i hi hstop
    exact le_of_not_gt (fun he => hω ⟨i, hi, hstop, he⟩)
  exact CachedUniformOutput.expected_selected_loss N loss (bad Λ cap ε g x₀ G N)
    (bad_measurable Λ cap ε g hgm x₀ G hG N) hmeas hε.le (by positivity)
    (fun _ _ _ => norm_nonneg _) hcap hgood hprob hbudget

end Bilevel.CappedAccuracy
