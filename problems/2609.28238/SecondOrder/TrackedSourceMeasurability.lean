import SecondOrder.TrackedMeasurability
import SecondOrder.TrackedCorrection

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- Reply providers are jointly measurable in the external tape, available
signs, current tracker state and, after a move, the curvature reply. This
condition alone does not assert freshness or a success probability. -/
structure MeasurableTrackingSource {Ξ : Type*} [MeasurableSpace Ξ] {d L : ℕ}
    (source : Ξ → TrackingSource d L) : Prop where
  initialAnchor : Measurable (fun ξ => (source ξ).initialAnchor)
  curvature : ∀ t, Measurable (fun w : (Ξ × (Fin t → Bool)) × TrackedState d L =>
    (source w.1.1).curvature t w.1.2 w.2)
  chords : ∀ t, Measurable (fun w : ((Ξ × (Fin (t+1) → Bool)) × TrackedState d L) × CurvatureReply d =>
    (source w.1.1.1).chords t w.1.1.2 w.1.2 w.2)
  refresh : ∀ t, Measurable (fun w : ((Ξ × (Fin (t+1) → Bool)) × TrackedState d L) × CurvatureReply d =>
    (source w.1.1.1).refresh t w.1.1.2 w.1.2 w.2)

theorem trackedRun_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d L : ℕ}
    (q : ℕ) (Lip s τ : ℝ) {source : Ξ → TrackingSource d L}
    (hm : MeasurableTrackingSource source) (t : ℕ) :
    Measurable (fun w : Ξ × (Fin t → Bool) => trackedRun q Lip s τ (source w.1) t w.2) := by
  induction t with
  | zero => exact trackedInitial_measurable (hm.initialAnchor.comp measurable_fst)
  | succ t ih =>
    have hp : Measurable (fun w : Ξ × (Fin (t+1) → Bool) => (w.1,Fin.init w.2)) :=
      measurable_fst.prodMk ((measurable_of_countable (fun w : Fin (t+1) → Bool => Fin.init w)).comp measurable_snd)
    have hz := ih.comp hp
    have hr := (hm.curvature t).comp (hp.prodMk hz)
    have hafter := (measurable_id.prodMk hz).prodMk hr
    exact trackedStep_measurable q Lip s τ hz hr
      ((measurable_of_countable (fun w : Fin (t+1) → Bool => w (Fin.last t))).comp measurable_snd)
      ((hm.chords t).comp hafter) ((hm.refresh t).comp hafter)

theorem trackedPolicy_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d L : ℕ}
    (q : ℕ) (Lip s τ : ℝ) {source : Ξ → TrackingSource d L}
    (hm : MeasurableTrackingSource source) :
    MeasurableIdealPolicy (fun ξ => trackedPolicy q Lip s τ (source ξ)) := by
  intro t
  have hz := (trackedRun_measurable q Lip s τ hm t).comp
    (measurable_fst : Measurable (fun w : (Ξ × (Fin t → Bool)) × IdealState d => w.1))
  exact trackedMove_measurable τ hz ((hm.curvature t).comp (measurable_fst.prodMk hz))

theorem correctTrackedCurvature_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (τ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} (hz : Measurable z) (hr : Measurable r) :
    Measurable (fun a => correctTrackedCurvature F τ hγ (z a) (r a)) := by
  have hf := tracked_measurable_fields.mp hz
  have hp := state_measurable_fields.mp hf.1
  exact Measurable.ite ((hp.2.1 (measurableSet_singleton true)).inter
    (measurableSet_le (trackerRead_measurable hf.2.2).norm measurable_const))
    (measurableCorrectCurvature_measurable hγ ((continuous_hessian hF).measurable.comp hp.1) hr) hr

theorem correctTrackingSource_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d L : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (Lip s τ ρ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source) :
    MeasurableTrackingSource (fun ξ => correctTrackingSource F Lip s τ ρ hγ (source ξ)) := by
  refine ⟨correctVector_measurable measurable_const measurable_const hm.initialAnchor,?_,?_,?_⟩
  · intro t
    exact correctTrackedCurvature_measurable hF τ hγ measurable_snd (hm.curvature t)
  · intro t
    have hz : Measurable (fun w : ((Ξ × (Fin (t+1) → Bool)) × TrackedState d L) × CurvatureReply d => w.1.2) :=
      measurable_fst.snd
    have hb : Measurable (fun w : ((Ξ × (Fin (t+1) → Bool)) × TrackedState d L) × CurvatureReply d => w.1.1.2 (Fin.last t)) :=
      (measurable_fst.fst.snd).eval
    have hp := (state_measurable_fields.mp (trackedNext_measurable Lip s τ hz measurable_snd hb)).1
    have hpoints := trackerPushPoints_measurable (tracked_measurable_fields.mp hz).2.2 hp
    apply measurable_pi_lambda
    intro i
    exact correctVector_measurable measurable_const
      (((contDiff_gradient_one hF).continuous.measurable.comp (hpoints.eval (a := nodeRight i))).sub
        ((contDiff_gradient_one hF).continuous.measurable.comp (hpoints.eval (a := nodeLeft i))))
      ((hm.chords t).eval (a := i))
  · intro t
    have hz : Measurable (fun w : ((Ξ × (Fin (t+1) → Bool)) × TrackedState d L) × CurvatureReply d => w.1.2) :=
      measurable_fst.snd
    have hb : Measurable (fun w : ((Ξ × (Fin (t+1) → Bool)) × TrackedState d L) × CurvatureReply d => w.1.1.2 (Fin.last t)) :=
      (measurable_fst.fst.snd).eval
    have hp := (state_measurable_fields.mp (trackedNext_measurable Lip s τ hz measurable_snd hb)).1
    exact correctVector_measurable measurable_const ((contDiff_gradient_one hF).continuous.measurable.comp hp)
      (hm.refresh t)

end
end SecondOrder
