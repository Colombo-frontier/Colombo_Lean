import Smoothness2601.RandomizedTail

/-! The no-hit event of the deferred simulator couples every real reply and
leaves an unrevealed small coordinate at the algorithm's actual output. -/
noncomputable section
namespace Smoothness2601.PrefixSimulator
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry IndependentDraws
open scoped RealInnerProductSpace ENNReal

variable {d T : ℕ} (A : Adaptive.Algorithm (Space d) ℝ)
variable (reply : Frame d T → Adaptive.Query (Space d) ℝ → Bool → Joint (Space d) ℝ)
variable (point : Adaptive.Query (Space d) ℝ → Space d) (outPoint : Space d → Space d) (δ : ℝ)

theorem real_output_hidden
    (hlocal : ∀ U k q c,
      (∀ i : Fin T, k ≤ i.val → |⟪point q,U i⟫| ≤ δ) →
      reply U q c = reply (truncate U (min T (k+if c then 1 else 0))) q c)
    (coins : ℕ → Bool) (initial : A.Memory) (U : Frame d T) (N : ℕ)
    (hbad : ¬ (queryBad A reply coins point δ initial N U ∨
      outputBad A reply coins outPoint δ initial N U))
    (hsat : ¬ T ≤ prefixCount T coins N) :
    ∃ i : Fin T, |⟪outPoint (A.output (realState A reply coins initial U N)),U i⟫| < δ := by
  have hsafe : ∀ t < N, ∀ i : Fin T, prefixCount T coins t ≤ i.val →
      |⟪point (A.query t (simulatedState A reply coins initial U t)),U i⟫| ≤ δ := by
    intro t ht i hi
    apply le_of_lt
    apply lt_of_not_ge
    intro hh
    exact hbad (Or.inl ⟨⟨t,ht⟩,i,hi,hh⟩)
  have he := outputs_coupled A reply coins
    (fun U k q => ∀ i : Fin T, k ≤ i.val → |⟪point q,U i⟫| ≤ δ)
    hlocal initial U N hsafe
  rw [he]
  let i : Fin T := ⟨prefixCount T coins N,lt_of_not_ge hsat⟩
  refine ⟨i,lt_of_not_ge ?_⟩
  intro hh
  exact hbad (Or.inr ⟨i,le_rfl,hh⟩)

theorem experiment_output_measurable
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (N : ℕ) : Measurable (fun p : Draws Bool N × (A.Memory × Frame d T) =>
      A.output (realState A reply (coinSequence N p.1) p.2.1 p.2.2 N)) := by
  have hh : Measurable (fun p : (A.Memory × Frame d T) × Draws Bool N =>
      A.output (realState A reply (coinSequence N p.2) p.1.1 p.1.2 N)) :=
    measurable_from_prod_countable fun c =>
      A.output_measurable.comp (realState_measurable A reply (coinSequence N c) hr N)
  exact hh.comp measurable_swap

end Smoothness2601.PrefixSimulator

namespace Smoothness2601.LowerRisk
open MeasureTheory
open scoped ENNReal

/-- Fixed-frame extraction with private initialization and fresh oracle coins
kept as separate independent probability spaces. -/
theorem fixed_frame_three {C M F : Type*} [MeasurableSpace C] [MeasurableSpace M] [MeasurableSpace F]
    (κ : Measure C) (ν : Measure M) (μ : Measure F)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (valid : F → Prop) (hvalid : ∀ᵐ U ∂μ, valid U)
    (risk : C × (M × F) → ℝ≥0∞) (hrisk : Measurable risk) (target : ℝ≥0∞)
    (hmean : target < ∫⁻ p, risk p ∂κ.prod (ν.prod μ)) :
    ∃ U, valid U ∧ target < ∫⁻ m, ∫⁻ c, risk (c,(m,U)) ∂κ ∂ν := by
  have hm : Measurable (fun p : M × F => ∫⁻ c, risk (c,p) ∂κ) := hrisk.lintegral_prod_left'
  have he : (∫⁻ p, risk p ∂κ.prod (ν.prod μ)) =
      ∫⁻ U, ∫⁻ m, ∫⁻ c, risk (c,(m,U)) ∂κ ∂ν ∂μ := by
    rw [lintegral_prod_symm _ hrisk.aemeasurable]
    exact lintegral_prod_symm _ hm.aemeasurable
  rw [he] at hmean
  by_contra hn
  push_neg at hn
  have hi : (∫⁻ U, ∫⁻ m, ∫⁻ c, risk (c,(m,U)) ∂κ ∂ν ∂μ) ≤ target := by
    calc
      _ ≤ ∫⁻ _U, target ∂μ := lintegral_mono_ae (hvalid.mono fun U hU => hn U hU)
      _ = _ := by simp
  exact (not_lt_of_ge hi) hmean

end Smoothness2601.LowerRisk
