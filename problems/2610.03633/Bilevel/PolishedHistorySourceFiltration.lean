import Bilevel.PolishedHistorySourceExperiment

/-! A growing actual pre-query filtration also observes the original-call
clock. This is derived from adapted program states, not an extra oracle
condition. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {S Q O Y Ω : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]

theorem experimentClock_information (A : BorelAdaptive.Program S Q O Y)
    (state : ℕ → Ω → S) (info : ℕ → MeasurableSpace Ω)
    (hmono : Monotone info) (hs : ∀ n,Measurable[info n] (state n)) (n : ℕ) :
    Measurable[info n] (experimentClock A state n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.mono (hmono (Nat.le_succ n)) le_rfl).add
      (measurable_const.ite
        (((A.halt_measurable.comp (hs n)).mono (hmono (Nat.le_succ n)) le_rfl)
          (measurableSet_singleton true)) measurable_const)

theorem clockedState_information (A : BorelAdaptive.Program S Q O Y)
    (state : ℕ → Ω → S) (info : ℕ → MeasurableSpace Ω)
    (hmono : Monotone info) (hs : ∀ n,Measurable[info n] (state n)) (n : ℕ) :
    Measurable[info n] (clockedState A state n) :=
  (hs n).prodMk (experimentClock_information A state info hmono hs n)

end Bilevel.PolishedHistory
