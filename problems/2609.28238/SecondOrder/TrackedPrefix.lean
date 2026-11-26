import SecondOrder.SampledStepConfidence

open scoped Classical

namespace SecondOrder
noncomputable section

/-- Agreement of all observable local providers before a finite horizon. -/
def TrackingSource.AgreesBefore {d L : ℕ} (a b : TrackingSource d L) (N : ℕ) : Prop :=
  a.initialAnchor = b.initialAnchor ∧ ∀ t < N,
    a.curvature t = b.curvature t ∧ a.chords t = b.chords t ∧ a.refresh t = b.refresh t

theorem trackedRun_prefix_congr {d L N : ℕ} (q : ℕ) (Lip s τ : ℝ)
    {a b : TrackingSource d L} (h : a.AgreesBefore b N) (t : ℕ) (ht : t ≤ N) (w : Fin t → Bool) :
    trackedRun q Lip s τ a t w = trackedRun q Lip s τ b t w := by
  induction t with
  | zero => simp only [trackedRun,h.1]
  | succ t ih =>
    have hp := h.2 t (by omega)
    simp only [trackedRun,ih (by omega) (Fin.init w),hp.1,hp.2.1,hp.2.2]

theorem trackedRequestTrace_prefix_congr {d L N : ℕ} (q : ℕ) (Lip s τ : ℝ)
    {a b : TrackingSource d L} (h : a.AgreesBefore b N) (t : ℕ) (ht : t ≤ N) (w : Fin t → Bool) :
    trackedRequestTrace q Lip s τ a t w = trackedRequestTrace q Lip s τ b t w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := h.2 t (by omega)
    simp only [trackedRequestTrace,ih (by omega) (Fin.init w),
      trackedRun_prefix_congr q Lip s τ h t (by omega) (Fin.init w),hp.1]

theorem trackedHistoryGood_prefix_congr {d L N : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s τ γ ρ : ℝ)
    {a b : TrackingSource d L} (h : a.AgreesBefore b N) (t : ℕ) (ht : t ≤ N) (w : Fin t → Bool) :
    trackedHistoryGood F q Lip s τ γ ρ a t w ↔ trackedHistoryGood F q Lip s τ γ ρ b t w := by
  induction t with
  | zero => simp only [trackedHistoryGood,h.1]
  | succ t ih =>
    have hp := h.2 t (by omega)
    simp only [trackedHistoryGood,ih (by omega) (Fin.init w),
      trackedRun_prefix_congr q Lip s τ h t (by omega) (Fin.init w),hp.1,hp.2.1,hp.2.2]

end
end SecondOrder
