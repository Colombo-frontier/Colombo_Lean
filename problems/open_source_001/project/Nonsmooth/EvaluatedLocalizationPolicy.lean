import Nonsmooth.SelectedBlockPolicy
import Nonsmooth.QueryOutputValue
import Nonsmooth.BestValueRecord

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def evaluatedLocalizationFamily {C S X : Type} (p : C → Policy Unit S X) (T : ℕ)
    (cb : C × BestValueRecord X) : Policy Unit (S × ℝ) X := queryOutputValue (p cb.1) T

def evaluatedLocalizationStep {C S X : Type} (p : C → Policy Unit S X) (next : C → S → C)
    (cb : C × BestValueRecord X) (st : S × ℝ) : C × BestValueRecord X :=
  (next cb.1 st.1, updateBestValue cb.2 ((p cb.1).output () st.1) st.2)

def evaluatedLocalizationPolicy {C S X : Type} (p : C → Policy Unit S X) (T : ℕ)
    (next : C → S → C) (c0 : C) (x0 : X) :
    Policy Unit ((C × BestValueRecord X) × (S × ℝ)) X :=
  selectedBlockPolicy (evaluatedLocalizationFamily p T) (T + 1)
    (evaluatedLocalizationStep p next) (fun cb => cb.2.2.1) (c0, false, x0, 0)

def localizationStagePoint {C S X : Type} (p : C → Policy Unit S X) (T : ℕ)
    (next : C → S → C) (f : X → ℝ) (c0 : C) (m : ℕ) : X :=
  (p (selectedBlockController p T next f c0 m)).result f () T

def localizationBestRecord {C S X : Type} (p : C → Policy Unit S X) (T : ℕ)
    (next : C → S → C) (f : X → ℝ) (c0 : C) (x0 : X) : ℕ → BestValueRecord X
  | 0 => (false, x0, 0)
  | m + 1 => let x := localizationStagePoint p T next f c0 m
      updateBestValue (localizationBestRecord p T next f c0 x0 m) x (f x)

theorem evaluatedLocalizationController_exact {C S X : Type} (p : C → Policy Unit S X)
    (T : ℕ) (next : C → S → C) (f : X → ℝ) (c0 : C) (x0 : X) (m : ℕ) :
    selectedBlockController (evaluatedLocalizationFamily p T) (T + 1)
      (evaluatedLocalizationStep p next) f (c0, false, x0, 0) m =
      (selectedBlockController p T next f c0 m, localizationBestRecord p T next f c0 x0 m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [selectedBlockController, ih]
    simp only [evaluatedLocalizationFamily, queryOutputValue_run_exact,
      evaluatedLocalizationStep, selectedBlockController, localizationBestRecord,
      localizationStagePoint, Policy.result]

theorem evaluatedLocalizationPolicy_run_exact {C S X : Type} (p : C → Policy Unit S X)
    (T : ℕ) (next : C → S → C) (f : X → ℝ) (c0 : C) (x0 : X) (m : ℕ) :
    (evaluatedLocalizationPolicy p T next c0 x0).run f () (m * (T + 1)) =
      ((selectedBlockController p T next f c0 m, localizationBestRecord p T next f c0 x0 m),
        (p (selectedBlockController p T next f c0 m)).initial (), 0) := by
  unfold evaluatedLocalizationPolicy
  rw [selectedBlockPolicy_run_exact _ (by omega), evaluatedLocalizationController_exact]
  rfl

theorem evaluatedLocalizationPolicy_result_exact {C S X : Type} (p : C → Policy Unit S X)
    (T : ℕ) (next : C → S → C) (f : X → ℝ) (c0 : C) (x0 : X) (m : ℕ) :
    (evaluatedLocalizationPolicy p T next c0 x0).result f () (m * (T + 1)) =
      (localizationBestRecord p T next f c0 x0 m).2.1 := by
  unfold Policy.result
  rw [evaluatedLocalizationPolicy_run_exact]
  rfl

end
end Nonsmooth
