import Nonsmooth.RecursiveSupportResponse
import Nonsmooth.SupportPosteriorIndependence

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

def supportResponseErase {n : ℕ} (h : SupportHistory E k n) : ResponseHistory k n :=
  fun i => (h i).2

theorem supportResponseErase_measurable (n : ℕ) :
    Measurable (supportResponseErase (E := E) (k := k) (n := n)) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).snd

theorem supportResponseErase_snoc {n : ℕ} (h : SupportHistory E k n) (v : E × (Fin k × ℝ)) :
    supportResponseErase (Fin.snoc h v) = Fin.snoc (supportResponseErase h) v.2 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [supportResponseErase]

def policyResponseState (p : Policy Ω S E) (ω : Ω) :
    (n : ℕ) → ResponseHistory k n → S
  | 0, _ => p.initial ω
  | n + 1, h => p.update n ω (policyResponseState p ω n (Fin.init h)) (h (Fin.last n)).2

def policyResponseQuery (p : Policy Ω S E) (ω : Ω) (n : ℕ) (h : ResponseHistory k n) : E :=
  p.query n ω (policyResponseState p ω n h)

theorem policyResponseState_erases (p : Policy Ω S E) (ω : Ω) (n : ℕ)
    (h : SupportHistory E k n) :
    policyResponseState p ω n (supportResponseErase h) = p.stateOnHistory ω n (supportEraseHistory h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change p.update n ω (policyResponseState p ω n (supportResponseErase (Fin.init h)))
      (h (Fin.last n)).2.2 =
      p.update n ω (p.stateOnHistory ω n (supportEraseHistory (Fin.init h))) (h (Fin.last n)).2.2
    rw [ih]

theorem policyResponseState_measurable (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    Measurable (policyResponseState (k := k) p ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hi : Measurable (fun h : ResponseHistory k (n + 1) => Fin.init h) :=
      responseHistorySplit_measurable.fst
    exact (hp.update n).comp (measurable_const.prodMk
      ((ih.comp hi).prodMk (measurable_pi_apply (Fin.last n)).snd))

theorem policyResponseQuery_measurable (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    Measurable (policyResponseQuery (k := k) p ω n) :=
  (hp.query n).comp (measurable_const.prodMk (policyResponseState_measurable p hp ω n))

theorem recursiveSupportResponse_policy (p : Policy Ω S E) (ω : Ω) (n : ℕ) (a : Fin k → E) :
    recursiveSupportResponse (policyResponseQuery p ω) n a =
      supportResponseErase (supportAugmentedTranscript p a ω n) := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [recursiveSupportResponse, responseHistoryJoin, supportAugmentedTranscript,
      supportResponseErase_snoc, ih, policyResponseQuery, policyResponseState_erases,
      supportSingleObservation]

end
end Nonsmooth
