import Nonsmooth.EvaluatedLocalizationPolicy

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem localizationBestRecord_initialized {C S X : Type} (p : C → Policy Unit S X)
    (T : ℕ) (next : C → S → C) (f : X → ℝ) (c0 : C) (x0 : X) {m : ℕ} (hm : 0 < m) :
    (localizationBestRecord p T next f c0 x0 m).1 = true := by
  cases m with
  | zero => omega
  | succ m => exact updateBestValue_initialized _ _ _

theorem localizationBestRecord_value_exact {C S X : Type} (p : C → Policy Unit S X)
    (T : ℕ) (next : C → S → C) (f : X → ℝ) (c0 : C) (x0 : X) (m : ℕ)
    (hm : (localizationBestRecord p T next f c0 x0 m).1 = true) :
    (localizationBestRecord p T next f c0 x0 m).2.2 =
      f (localizationBestRecord p T next f c0 x0 m).2.1 := by
  induction m with
  | zero => simp only [localizationBestRecord, Bool.false_eq_true] at hm
  | succ m ih => exact updateBestValue_value_exact f _ ih _

theorem localizationBestRecord_le_stage {C S X : Type} (p : C → Policy Unit S X)
    (T : ℕ) (next : C → S → C) (f : X → ℝ) (c0 : C) (x0 : X) (m i : ℕ) (hi : i < m) :
    (localizationBestRecord p T next f c0 x0 m).2.2 ≤
      f (localizationStagePoint p T next f c0 i) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases him : i = m
    · subst i
      exact updateBestValue_le_new _ _ _
    · have him' : i < m := by omega
      exact (updateBestValue_le_old _
        (localizationBestRecord_initialized p T next f c0 x0 (by omega : 0 < m)) _ _).trans (ih him')

theorem evaluatedLocalizationPolicy_le_every_stage {C S X : Type} (p : C → Policy Unit S X)
    (T : ℕ) (next : C → S → C) (f : X → ℝ) (c0 : C) (x0 : X) (m i : ℕ) (hi : i < m) :
    f ((evaluatedLocalizationPolicy p T next c0 x0).result f () (m * (T + 1))) ≤
      f (localizationStagePoint p T next f c0 i) := by
  rw [evaluatedLocalizationPolicy_result_exact]
  rw [← localizationBestRecord_value_exact p T next f c0 x0 m
    (localizationBestRecord_initialized p T next f c0 x0 (by omega : 0 < m))]
  exact localizationBestRecord_le_stage p T next f c0 x0 m i hi

end
end Nonsmooth
