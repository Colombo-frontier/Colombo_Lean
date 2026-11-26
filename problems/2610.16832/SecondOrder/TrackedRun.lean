import SecondOrder.TrackedStep

open scoped Classical

namespace SecondOrder
noncomputable section

/-- Local reply providers. The curvature direction is fixed using the old
sign prefix. Chord and refresh replies are queried only after the new sign
has determined the move endpoint, so they may use the longer prefix. -/
structure TrackingSource (d L : ℕ) where
  initialAnchor : Point d
  curvature : (t : ℕ) → (Fin t → Bool) → TrackedState d L → CurvatureReply d
  chords : (t : ℕ) → (Fin (t+1) → Bool) → TrackedState d L → CurvatureReply d → BinaryNode L → Point d
  refresh : (t : ℕ) → (Fin (t+1) → Bool) → TrackedState d L → CurvatureReply d → Point d

def trackedRun {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L) :
    (t : ℕ) → (Fin t → Bool) → TrackedState d L
  | 0, _ => trackedInitial source.initialAnchor
  | t+1, w =>
      let z := trackedRun q Lip s τ source t (Fin.init w)
      let r := source.curvature t (Fin.init w) z
      trackedStep q Lip s τ z r (w (Fin.last t)) (source.chords t w z r) (source.refresh t w z r)

def trackedPolicy {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L) : IdealPolicy d :=
  fun t w _ =>
    let z := trackedRun q Lip s τ source t w
    trackedMove τ z (source.curvature t w z)

/-- The projected physical execution is exactly the previously analyzed
idealRun of a causal policy. This is a state equality, not just an output
or count comparison. Providers are allowed to fail arbitrarily here. -/
theorem trackedRun_physical {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (t : ℕ) (w : Fin t → Bool) :
    (trackedRun q Lip s τ source t w).physical =
      idealRun Lip s (trackedPolicy q Lip s τ source) t w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trackedRun,trackedStep_physical,idealRun,← ih (Fin.init w)]
    rfl

theorem trackedRun_memory_le {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (t : ℕ) (w : Fin t → Bool) : (trackedRun q Lip s τ source t w).memory.length ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trackedRun]
    exact (trackedStep_memory_length q Lip s τ _ _ _ _ _).trans (Nat.add_le_add_right (ih (Fin.init w)) 1)

def trackedHistoryGood {d L : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s τ γ ρ : ℝ)
    (source : TrackingSource d L) : (t : ℕ) → (Fin t → Bool) → Prop
  | 0, _ => ‖source.initialAnchor-gradient F 0‖ ≤ τ/4
  | t+1, w =>
      trackedHistoryGood F q Lip s τ γ ρ source t (Fin.init w) ∧
      let z := trackedRun q Lip s τ source t (Fin.init w)
      let r := source.curvature t (Fin.init w) z
      TrackedLocalGood F q Lip s τ γ ρ z r (w (Fin.last t))
        (source.chords t w z r) (source.refresh t w z r)

theorem trackedHistoryGood_consistent {d L : ℕ} {F : Point d → ℝ} {τ γ ρ : ℝ}
    (q : ℕ) (Lip s : ℝ) (source : TrackingSource d L) (t : ℕ) (w : Fin t → Bool)
    (hg : trackedHistoryGood F q Lip s τ γ ρ source t w) :
    TrackedConsistent F τ ρ (trackedRun q Lip s τ source t w) := by
  induction t with
  | zero => exact trackedInitial_consistent source.initialAnchor hg
  | succ t ih =>
    exact trackedStep_consistent q Lip s _ (ih (Fin.init w) hg.1) _ _ _ _ hg.2

/-- Successful local calls imply the valid physical history used by the
coupling and cap proofs. The binary depth bound is verified from the actual
memory length; it is not added as a per-state correctness assumption. -/
theorem trackedHistoryGood_validHistory {d L : ℕ} {F : Point d → ℝ} {τ γ ρ : ℝ}
    (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hL : (L : ℝ)*ρ ≤ τ/4)
    (q : ℕ) (Lip s : ℝ) (source : TrackingSource d L)
    (t : ℕ) (w : Fin t → Bool) (ht : t ≤ 2^L)
    (hg : trackedHistoryGood F q Lip s τ γ ρ source t w) :
    validHistory F Lip s τ γ (trackedPolicy q Lip s τ source) t w := by
  induction t with
  | zero => trivial
  | succ t ih =>
    refine ⟨ih (Fin.init w) (by omega) hg.1,?_⟩
    intro hr
    rw [← trackedRun_physical q Lip s τ source t (Fin.init w)] at hr ⊢
    have hc := trackedHistoryGood_consistent q Lip s source t (Fin.init w) hg.1
    have hn := trackedRun_memory_le q Lip s τ source t (Fin.init w)
    exact trackedMove_valid hτ hρ hL _ hc (by omega) _ (hg.2.1 hr)

theorem trackedRun_good_stopped_sosp {d L : ℕ} {F : Point d → ℝ} {τ γ ρ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hL : (L : ℝ)*ρ ≤ τ/4)
    (q : ℕ) (Lip s : ℝ) (source : TrackingSource d L)
    (t : ℕ) (w : Fin t → Bool) (ht : t ≤ 2^L)
    (hg : trackedHistoryGood F q Lip s τ γ ρ source t w)
    (hr : (trackedRun q Lip s τ source t w).physical.running = false) :
    IsSOSP F (10*τ) γ (trackedRun q Lip s τ source t w).physical.point := by
  rw [trackedRun_physical] at hr ⊢
  exact idealRun_good_stopped_sosp F hτ hγ Lip s _ t w
    (trackedHistoryGood_validHistory hτ hρ hL q Lip s source t w ht hg) hr

end
end SecondOrder
