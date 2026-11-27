import Nonsmooth.ResponseHistoryEncoding

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

def recursiveSupportResponse (u : ∀ n, ResponseHistory k n → E) :
    (n : ℕ) → (Fin k → E) → ResponseHistory k n
  | 0 => fun _ => Fin.elim0
  | n + 1 => fun a => responseHistoryJoin (recursiveSupportResponse u n a,
      supportSingleObservation (u n (recursiveSupportResponse u n a)) a)

theorem recursiveSupportResponse_measurable (u : ∀ n, ResponseHistory k n → E)
    (hu : ∀ n, Measurable (u n)) (n : ℕ) : Measurable (recursiveSupportResponse u n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hp : Measurable (fun a : Fin k → E => (recursiveSupportResponse u n a, a)) :=
      ih.prodMk measurable_id
    have hF := supportParametricObservation_measurable (k := k) (u n) (hu n)
    have hO : Measurable (fun a : Fin k → E =>
        supportSingleObservation (u n (recursiveSupportResponse u n a)) a) := by
      simpa only [Function.comp_def] using hF.comp hp
    exact responseHistoryJoin_measurable.comp (ih.prodMk hO)

theorem recursiveSupportResponse_split (u : ∀ n, ResponseHistory k n → E)
    (n : ℕ) (a : Fin k → E) :
    responseHistorySplit (recursiveSupportResponse u (n + 1) a) =
      (recursiveSupportResponse u n a, supportSingleObservation (u n (recursiveSupportResponse u n a)) a) :=
  responseHistorySplit_join _

end
end Nonsmooth
