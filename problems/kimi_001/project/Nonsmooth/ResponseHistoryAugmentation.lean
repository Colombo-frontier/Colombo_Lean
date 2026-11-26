import Nonsmooth.PolicyResponseEncoding

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

def responseHistoryAugment (u : ∀ n, ResponseHistory k n → E) :
    (n : ℕ) → ResponseHistory k n → SupportHistory E k n
  | 0, _ => Fin.elim0
  | n + 1, h => Fin.snoc (responseHistoryAugment u n (Fin.init h))
      (u n (Fin.init h), h (Fin.last n))

theorem responseHistoryAugment_measurable (u : ∀ n, ResponseHistory k n → E)
    (hu : ∀ n, Measurable (u n)) (n : ℕ) : Measurable (responseHistoryAugment u n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hi : Measurable (fun h : ResponseHistory k (n + 1) => Fin.init h) :=
      responseHistorySplit_measurable.fst
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [responseHistoryAugment, Fin.snoc_last, Function.comp_def] using
        ((hu n).comp hi).prodMk (measurable_pi_apply (Fin.last n))
    · simpa only [responseHistoryAugment, Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp (ih.comp hi)

theorem responseHistoryAugment_join (u : ∀ n, ResponseHistory k n → E)
    (n : ℕ) (h : ResponseHistory k n) (y : Fin k × ℝ) :
    responseHistoryAugment u (n + 1) (responseHistoryJoin (h, y)) =
      Fin.snoc (responseHistoryAugment u n h) (u n h, y) := by
  simp only [responseHistoryAugment, responseHistoryJoin, Fin.init_snoc, Fin.snoc_last]

theorem supportResponseErase_augment (u : ∀ n, ResponseHistory k n → E)
    (n : ℕ) (h : ResponseHistory k n) :
    supportResponseErase (responseHistoryAugment u n h) = h := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change supportResponseErase (Fin.snoc (responseHistoryAugment u n (Fin.init h))
      (u n (Fin.init h), h (Fin.last n))) = h
    rw [supportResponseErase_snoc, ih]
    exact Fin.snoc_init_self h

variable {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem responseHistoryAugment_policy (p : Policy Ω S E) (ω : Ω) (n : ℕ) (a : Fin k → E) :
    responseHistoryAugment (policyResponseQuery p ω) n
      (recursiveSupportResponse (policyResponseQuery p ω) n a) =
        supportAugmentedTranscript p a ω n := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [recursiveSupportResponse, responseHistoryAugment_join, ih, recursiveSupportResponse_policy]
    simp only [policyResponseQuery, policyResponseState_erases, supportAugmentedTranscript,
      supportSingleObservation]

end
end Nonsmooth
