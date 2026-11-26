import HeavyTail.RejectionSampler
import HeavyTail.Rejection

/-! The accepted-law moment bounds transferred to the actual iid rejection
sampler output. The pushforward identity and almost-sure termination are proved
from the raw law; the accepted moments are not hypotheses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace
namespace HeavyTail

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem sampled_rejection_lemma {ξ : Ω → E} {b : E} {p G L s τ : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hG : 0 ≤ G) (hL : 0 < L) (hs : 0 ≤ s)
    (hτ : 64 * (4 * G + L) ≤ τ) (hb : ‖b‖ ≤ 4 * G)
    (hξm : Measurable ξ) (hξp : MemLp ξ (ENNReal.ofReal p) P)
    (hzero : ∫ ω, ξ ω ∂P = 0)
    (hstrong : ∫ ω, ‖ξ ω‖ ^ p ∂P ≤ L ^ p)
    (hweak : ∀ v : E, ‖v‖ = 1 → ∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P ≤ s ^ p) :
    let S := {ω | ‖b + ξ ω‖ ≤ τ}
    let Q := (iidRawLaw P).map (rejectionSample S)
    let b' := ∫ ω, b + ξ ω ∂Q
    (∀ᵐ ω ∂iidRawLaw P, ∃ n, ω n ∈ S) ∧
    P.real Sᶜ ≤ (2 * L / τ) ^ p ∧ P.real Sᶜ ≤ 1 / 16 ∧
    ‖b' - b‖ ≤ rejectionConstant p * s * (L / τ) ^ (p - 1) ∧
    (∫ ω, ‖b + ξ ω - b'‖ ^ 2 ∂Q) ≤ rejectionConstant p * L ^ p * τ ^ (2 - p) ∧
    ∀ v : E, ‖v‖ = 1 →
      (∫ ω, |⟪v, b + ξ ω - b'⟫_ℝ| ^ p ∂Q) ≤ rejectionConstant p * s ^ p := by
  let S := {ω | ‖b + ξ ω‖ ≤ τ}
  have hmeas : Measurable (fun ω => ‖b + ξ ω‖) :=
    (continuous_const.add continuous_id).norm.measurable.comp hξm
  have hS : MeasurableSet S := measurableSet_le hmeas measurable_const
  have hr := rejection_lemma (E := E) (P := P) (ξ := ξ) (b := b)
    hp hp2 hG hL hs hτ hb hξm hξp hzero hstrong hweak
  change P.real Sᶜ ≤ _ ∧ P.real Sᶜ ≤ 1 / 16 ∧ _ at hr
  have hmass : P.real S + P.real Sᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := P) hS
  have hpos : P S ≠ 0 := by
    intro hz
    have hz' : P.real S = 0 := by simp [Measure.real, hz]
    linarith [hr.2.1]
  let result (Q : Measure Ω) : Prop :=
    let b' := ∫ ω, b + ξ ω ∂Q
    P.real Sᶜ ≤ (2 * L / τ) ^ p ∧ P.real Sᶜ ≤ 1 / 16 ∧
    ‖b' - b‖ ≤ rejectionConstant p * s * (L / τ) ^ (p - 1) ∧
    (∫ ω, ‖b + ξ ω - b'‖ ^ 2 ∂Q) ≤ rejectionConstant p * L ^ p * τ ^ (2 - p) ∧
    ∀ v : E, ‖v‖ = 1 →
      (∫ ω, |⟪v, b + ξ ω - b'⟫_ℝ| ^ p ∂Q) ≤ rejectionConstant p * s ^ p
  have hr' : result (ProbabilityTheory.cond P S) := hr
  have he : result ((iidRawLaw P).map (rejectionSample S)) =
      result (ProbabilityTheory.cond P S) := congrArg result (rejectionSample_map P hS hpos)
  exact ⟨iid_eventually_accepts P hS hpos, he.mpr hr'⟩

end HeavyTail
