import HeavyTail.CappedRawPolicy
import HeavyTail.RejectionSamplerKernel
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.Prod

/-! The ideal accepted process is built from the actual first-acceptance
sampler kernel. Its remaining-output kernel is harmonic under each raw trial:
rejected replies preserve the frozen state, while accepted replies consume
exactly one remaining update. This supplies the marginal identity for the
ideal/capped distribution coupling, without conditioning on completion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
namespace HeavyTail

theorem rejection_conditional_harmonic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    (hpos : P A ≠ 0) (f : Ω → ℝ≥0∞) :
    (∫⁻ ω, if ω ∈ A then f ω else (∫⁻ z, f z ∂ProbabilityTheory.cond P A) ∂P) =
      ∫⁻ z, f z ∂ProbabilityTheory.cond P A := by
  let c := ∫⁻ z, f z ∂ProbabilityTheory.cond P A
  have hpart : (∫⁻ z in A, f z ∂P) = P A * c := by
    dsimp [c]
    rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hpos (measure_ne_top P A), one_mul]
  have hmass : P A + P Aᶜ = 1 := by
    rw [measure_add_measure_compl hA, measure_univ]
  change (∫⁻ ω, A.piecewise f (fun _ => c) ω ∂P) = c
  rw [lintegral_piecewise hA, hpart, setLIntegral_const]
  calc
    P A * c + c * P Aᶜ = (P A + P Aᶜ) * c := by rw [mul_comm c, add_mul]
    _ = c := by rw [hmass, one_mul]

namespace CappedRaw.Rule
universe u v w
variable {State : Type v} {Reply : Type u} {Query Output : Type w}
  [MeasurableSpace State] [MeasurableSpace Query] [MeasurableSpace Reply]
  [MeasurableSpace Output]
  (M : CappedRaw.Rule State Query Reply Output)
  (K : Kernel Query Reply) [IsMarkovKernel K]
  (hpos : ∀ s, K (M.query s) (Prod.mk s ⁻¹' M.acceptance) ≠ 0)

def idealAcceptedReply : Kernel State Reply :=
  rejectionSamplerKernel (K.comap M.query M.query_measurable) M.acceptance_measurable hpos

instance idealAcceptedReply_markov : IsMarkovKernel (M.idealAcceptedReply K hpos) := by
  unfold idealAcceptedReply
  infer_instance

theorem idealAcceptedReply_eq_cond (s : State) :
    M.idealAcceptedReply K hpos s =
      ProbabilityTheory.cond (K (M.query s)) (Prod.mk s ⁻¹' M.acceptance) :=
  rejectionSamplerKernel_eq_cond _ _ _ _

def idealAcceptedTransition : Kernel State State :=
  (Kernel.id ×ₖ M.idealAcceptedReply K hpos).map M.update

instance idealAcceptedTransition_markov : IsMarkovKernel (M.idealAcceptedTransition K hpos) := by
  unfold idealAcceptedTransition
  exact Kernel.IsMarkovKernel.map _ M.update_measurable

theorem idealAcceptedTransition_lintegral (s : State) {f : State → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t, f t ∂M.idealAcceptedTransition K hpos s) =
      ∫⁻ r, f (M.update (s, r))
        ∂ProbabilityTheory.cond (K (M.query s)) (Prod.mk s ⁻¹' M.acceptance) := by
  rw [idealAcceptedTransition, Kernel.lintegral_map _ M.update_measurable _ hf,
    Kernel.lintegral_id_prod
      (show Measurable (fun p => f (M.update p)) from hf.comp M.update_measurable),
    M.idealAcceptedReply_eq_cond]

def idealOutputKernel : ℕ → Kernel State Output
  | 0 => Kernel.deterministic M.readout M.readout_measurable
  | n + 1 => idealOutputKernel n ∘ₖ M.idealAcceptedTransition K hpos

instance idealOutputKernel_markov (n : ℕ) : IsMarkovKernel (M.idealOutputKernel K hpos n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.deterministic M.readout M.readout_measurable))
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (M.idealOutputKernel K hpos n ∘ₖ M.idealAcceptedTransition K hpos)
    infer_instance

theorem idealOutputKernel_succ_apply (n : ℕ) (s : State) {S : Set Output} (hS : MeasurableSet S) :
    M.idealOutputKernel K hpos (n + 1) s S =
      ∫⁻ r, M.idealOutputKernel K hpos n (M.update (s, r)) S
        ∂ProbabilityTheory.cond (K (M.query s)) (Prod.mk s ⁻¹' M.acceptance) := by
  rw [idealOutputKernel, Kernel.comp_apply' _ _ _ hS]
  exact M.idealAcceptedTransition_lintegral K hpos s
    ((M.idealOutputKernel K hpos n).measurable_coe hS)

def idealCompletionKernel (n : ℕ) : Kernel (ℕ × State) Output where
  toFun s := M.idealOutputKernel K hpos (n - s.1) s.2
  measurable' := by
    have hm : Measurable (fun s : State × ℕ => M.idealOutputKernel K hpos (n - s.2) s.1) :=
      measurable_from_prod_countable (fun k : ℕ => (M.idealOutputKernel K hpos (n - k)).measurable)
    exact hm.comp measurable_swap

instance idealCompletionKernel_markov (n : ℕ) :
    IsMarkovKernel (M.idealCompletionKernel K hpos n) := ⟨fun s => by
  change IsProbabilityMeasure (M.idealOutputKernel K hpos (n - s.1) s.2)
  infer_instance⟩

theorem idealCompletionKernel_done {n : ℕ} (s : ℕ × State) (hs : n ≤ s.1) :
    M.idealCompletionKernel K hpos n s = Measure.dirac (M.readout s.2) := by
  simp [idealCompletionKernel, Nat.sub_eq_zero_of_le hs, idealOutputKernel,
    Kernel.deterministic_apply]

theorem idealCompletionKernel_harmonic (n : ℕ) (s : ℕ × State)
    {S : Set Output} (hS : MeasurableSet S) :
    (∫⁻ r, M.idealCompletionKernel K hpos n (M.step n (s, r)) S ∂K (M.query s.2)) =
      M.idealCompletionKernel K hpos n s S := by
  by_cases hs : s.1 < n
  · let k := n - (s.1 + 1)
    have hk : n - s.1 = k + 1 := by dsimp [k]; omega
    have he : ∀ r, M.idealCompletionKernel K hpos n (M.step n (s, r)) S =
        if r ∈ Prod.mk s.2 ⁻¹' M.acceptance then
          M.idealOutputKernel K hpos k (M.update (s.2, r)) S
        else M.idealOutputKernel K hpos (k + 1) s.2 S := by
      intro r
      by_cases ha : (s.2, r) ∈ M.acceptance
      · simp [step, activeAcceptance, hs, ha, idealCompletionKernel, k]
      · simp [step, activeAcceptance, hs, ha, idealCompletionKernel, hk]
    simp_rw [he]
    rw [M.idealOutputKernel_succ_apply K hpos k s.2 hS,
      rejection_conditional_harmonic _ (M.acceptance_measurable.preimage measurable_prodMk_left) (hpos s.2)]
    change _ = M.idealOutputKernel K hpos (n - s.1) s.2 S
    rw [hk, M.idealOutputKernel_succ_apply K hpos k s.2 hS]
  · simp_rw [M.step_frozen_done n s _ (Nat.le_of_not_gt hs)]
    simp

end CappedRaw.Rule
end HeavyTail
