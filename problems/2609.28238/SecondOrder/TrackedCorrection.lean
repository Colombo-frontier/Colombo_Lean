import SecondOrder.TrackedRun

open scoped Classical

namespace SecondOrder
noncomputable section

theorem validCurvatureReply_iff_rayleigh {d : ℕ} (F : Point d → ℝ) (γ : ℝ)
    (x : Point d) (r : CurvatureReply d) :
    ValidCurvatureReply F γ x r ↔ RayleighReplyValid γ (hessian F x) r := by
  cases r <;> rfl

def correctTrackedCurvature {d L : ℕ} (F : Point d → ℝ) (τ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (z : TrackedState d L) (r : CurvatureReply d) : CurvatureReply d :=
  if z.physical.running = true ∧ ‖trackerRead z.memory‖ ≤ 4*τ then
    measurableCorrectCurvature hγ (hessian F z.physical.point) r else r

theorem correctTrackedCurvature_valid {d L : ℕ} (F : Point d → ℝ) (τ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (z : TrackedState d L) (r : CurvatureReply d) (hr : z.physical.running = true)
    (hn : ‖trackerRead z.memory‖ ≤ 4*τ) :
    ValidCurvatureReply F γ z.physical.point (correctTrackedCurvature F τ hγ z r) := by
  rw [correctTrackedCurvature,if_pos ⟨hr,hn⟩,validCurvatureReply_iff_rayleigh]
  exact measurableCorrectCurvature_valid hγ _ r

theorem correctTrackedCurvature_unchanged {d L : ℕ} (F : Point d → ℝ) (τ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (z : TrackedState d L) (r : CurvatureReply d)
    (hr : z.physical.running = true → ‖trackerRead z.memory‖ ≤ 4*τ → ValidCurvatureReply F γ z.physical.point r) :
    correctTrackedCurvature F τ hγ z r = r := by
  unfold correctTrackedCurvature
  split_ifs with hh
  · exact measurableCorrectCurvature_unchanged hγ _ r ((validCurvatureReply_iff_rayleigh F γ _ r).mp (hr hh.1 hh.2))
  · rfl

/-- Correct local routine outputs at the actual corrected trajectory's own
query points. This differs from correcting only a final physical move:
accurate stored estimates remain untouched and continue driving the tracker. -/
def correctTrackingSource {d L : ℕ} (F : Point d → ℝ) (Lip s τ ρ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (source : TrackingSource d L) : TrackingSource d L where
  initialAnchor := correctVector (τ/4) (gradient F 0) source.initialAnchor
  curvature := fun t w z => correctTrackedCurvature F τ hγ z (source.curvature t w z)
  chords := fun t w z r i =>
    let p := trackedNext Lip s τ z r (w (Fin.last t))
    correctVector ρ (gradient F (trackerPushPoints z.memory p.point (nodeRight i))-
      gradient F (trackerPushPoints z.memory p.point (nodeLeft i))) (source.chords t w z r i)
  refresh := fun t w z r =>
    correctVector (τ/4) (gradient F (trackedNext Lip s τ z r (w (Fin.last t))).point) (source.refresh t w z r)

theorem correctedTrackingSource_good {d L : ℕ} (F : Point d → ℝ) (Lip s : ℝ) {τ ρ γ : ℝ}
    (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hγ : 0 < γ) (q : ℕ) (source : TrackingSource d L)
    (t : ℕ) (w : Fin t → Bool) :
    trackedHistoryGood F q Lip s τ γ ρ (correctTrackingSource F Lip s τ ρ hγ source) t w := by
  induction t with
  | zero => exact correctVector_accurate (by positivity) _ _
  | succ t ih =>
    refine ⟨ih (Fin.init w),?_⟩
    constructor
    · intro hr hn
      exact correctTrackedCurvature_valid F τ hγ _ _ hr hn
    · intro hr
      constructor
      · intro i hi
        exact correctVector_accurate hρ _ _
      · intro he
        exact correctVector_accurate (by positivity) _ _

theorem trackerPush_congr_packets {d L : ℕ} (z : TrackerMemory d L) (x : Point d)
    (a b : BinaryNode L → Point d) (hab : ∀ i ∈ createdNodes L z.length, a i=b i) :
    trackerPush z x a = trackerPush z x b := by
  unfold trackerPush
  congr 1
  funext i
  by_cases hi : i ∈ createdNodes L z.length
  · simp [hi,hab i hi]
  · simp [hi]

theorem trackedStep_congr_packets {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (a c : BinaryNode L → Point d) (u v : Point d)
    (hc : (trackedNext Lip s τ z r b).running = true → ∀ i ∈ createdNodes L z.memory.length, a i=c i)
    (ha : (trackedNext Lip s τ z r b).running = true → trackedRestart q τ z r → u=v) :
    trackedStep q Lip s τ z r b a u = trackedStep q Lip s τ z r b c v := by
  by_cases hr : (trackedNext Lip s τ z r b).running = true
  · by_cases he : trackedRestart q τ z r
    · simp only [trackedStep,hr,↓reduceIte,he,ha hr he]
    · simp only [trackedStep,hr,↓reduceIte,he,trackerPush_congr_packets _ _ _ _ (hc hr)]
  · simp [trackedStep,hr]

/-- On local success, the complete actual and locally corrected tracker
states coincide, including old tables, epoch clock and physical state. -/
theorem trackedRun_corrected_agrees {d L : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s : ℝ)
    {τ ρ γ : ℝ} (hγ : 0 < γ) (source : TrackingSource d L) (t : ℕ) (w : Fin t → Bool)
    (hg : trackedHistoryGood F q Lip s τ γ ρ source t w) :
    trackedRun q Lip s τ (correctTrackingSource F Lip s τ ρ hγ source) t w =
      trackedRun q Lip s τ source t w := by
  induction t with
  | zero =>
    change trackedInitial (correctVector (τ/4) (gradient F 0) source.initialAnchor) = _
    rw [correctVector_unchanged _ _ hg]
    rfl
  | succ t ih =>
    rw [trackedRun,trackedRun,ih (Fin.init w) hg.1]
    let z := trackedRun q Lip s τ source t (Fin.init w)
    let r := source.curvature t (Fin.init w) z
    have hr : correctTrackedCurvature F τ hγ z r = r :=
      correctTrackedCurvature_unchanged F τ hγ z r hg.2.1
    dsimp only [correctTrackingSource]
    change trackedStep q Lip s τ z (correctTrackedCurvature F τ hγ z r) _ _ _ = _
    rw [hr]
    apply trackedStep_congr_packets
    · intro hrun i hi
      exact correctVector_unchanged _ _ ((hg.2.2 hrun).1 i hi)
    · intro hrun he
      exact correctVector_unchanged _ _ ((hg.2.2 hrun).2 he)

end
end SecondOrder
