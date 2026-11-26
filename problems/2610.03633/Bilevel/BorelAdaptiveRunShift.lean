import Bilevel.BorelAdaptiveExecution

/-! Forward decomposition of the actual chronological halted execution. -/
noncomputable section
namespace Bilevel.BorelAdaptive

variable {S Q O Y I C : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]

theorem run_succ_first (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (draws : ℕ → C) (s : S) (n : ℕ) :
    run A response i draws s (n+1) =
      run A response i (fun k => draws (k+1)) (step A response i (draws 0) s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step A response i (draws (n+1)) (run A response i draws s (n+1)) =
      step A response i (draws (n+1)) (run A response i (fun k => draws (k+1)) (step A response i (draws 0) s) n)
    rw [ih]

end Bilevel.BorelAdaptive
