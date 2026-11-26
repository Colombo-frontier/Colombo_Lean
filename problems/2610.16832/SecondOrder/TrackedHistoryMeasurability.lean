import SecondOrder.TrackedSourceMeasurability

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

theorem trackedLocalGood_measurableSet {A : Type*} [MeasurableSpace A] {d L : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (q : ℕ) (Lip s τ γ ρ : ℝ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    {packet : A → BinaryNode L → Point d} {anchor : A → Point d}
    (hz : Measurable z) (hr : Measurable r) (hb : Measurable b)
    (hp : Measurable packet) (ha : Measurable anchor) :
    MeasurableSet {a | TrackedLocalGood F q Lip s τ γ ρ (z a) (r a) (b a) (packet a) (anchor a)} := by
  have hf := tracked_measurable_fields.mp hz
  have hphys := state_measurable_fields.mp hf.1
  have hmem := trackerMemory_measurable_fields.mp hf.2.2
  have hnext := state_measurable_fields.mp (trackedNext_measurable Lip s τ hz hr hb)
  have hpoints := trackerPushPoints_measurable hf.2.2 hnext.1
  have hcurv : MeasurableSet {a | ValidCurvatureReply F γ (z a).physical.point (r a)} := by
    simp only [validCurvatureReply_iff_rayleigh]
    exact rayleighReplyValid_measurableSet γ ((continuous_hessian hF).measurable.comp hphys.1) hr
  have hchord : MeasurableSet {a | ∀ i ∈ createdNodes L (z a).memory.length,
      ‖packet a i-(gradient F (trackerPushPoints (z a).memory (trackedNext Lip s τ (z a) (r a) (b a)).point (nodeRight i))-
        gradient F (trackerPushPoints (z a).memory (trackedNext Lip s τ (z a) (r a) (b a)).point (nodeLeft i)))‖ ≤ ρ} := by
    simp only [imp_iff_not_or,Set.setOf_forall,Set.setOf_or,← Set.compl_setOf]
    apply MeasurableSet.iInter
    intro i
    have hi : MeasurableSet {a | i ∈ createdNodes L (z a).memory.length} := by
      simp only [mem_createdNodes]
      exact measurableSet_eq_fun_of_countable measurable_const (hmem.1.add_const 1)
    apply hi.compl.union
    exact measurableSet_le (((hp.eval (a := i)).sub
      (((contDiff_gradient_one hF).continuous.measurable.comp (hpoints.eval (a := nodeRight i))).sub
        ((contDiff_gradient_one hF).continuous.measurable.comp (hpoints.eval (a := nodeLeft i))))).norm) measurable_const
  have hanchor : MeasurableSet {a | ‖anchor a-gradient F (trackedNext Lip s τ (z a) (r a) (b a)).point‖ ≤ τ/4} :=
    measurableSet_le (ha.sub ((contDiff_gradient_one hF).continuous.measurable.comp hnext.1)).norm measurable_const
  simp only [imp_iff_not_or] at hchord
  simp only [TrackedLocalGood,imp_iff_not_or,Set.setOf_and,Set.setOf_or,← Set.compl_setOf]
  exact ((hphys.2.1 (measurableSet_singleton true)).compl.union
    ((measurableSet_le (trackerRead_measurable hf.2.2).norm measurable_const).compl.union hcurv)).inter
    ((hnext.2.1 (measurableSet_singleton true)).compl.union
      (hchord.inter ((trackedRestart_measurableSet q τ hz hr).compl.union hanchor)))

theorem trackedHistoryGood_measurableSet {Ξ : Type*} [MeasurableSpace Ξ] {d L : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (q : ℕ) (Lip s τ γ ρ : ℝ)
    {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source) (t : ℕ) :
    MeasurableSet {w : Ξ × (Fin t → Bool) | trackedHistoryGood F q Lip s τ γ ρ (source w.1) t w.2} := by
  induction t with
  | zero => exact measurableSet_le ((hm.initialAnchor.comp measurable_fst).sub measurable_const).norm measurable_const
  | succ t ih =>
    have hp : Measurable (fun w : Ξ × (Fin (t+1) → Bool) => (w.1,Fin.init w.2)) :=
      measurable_fst.prodMk ((measurable_of_countable (fun w : Fin (t+1) → Bool => Fin.init w)).comp measurable_snd)
    have hz := (trackedRun_measurable q Lip s τ hm t).comp hp
    have hr := (hm.curvature t).comp (hp.prodMk hz)
    have hafter := (measurable_id.prodMk hz).prodMk hr
    exact (ih.preimage hp).inter (trackedLocalGood_measurableSet hF q Lip s τ γ ρ hz hr
      ((measurable_of_countable (fun w : Fin (t+1) → Bool => w (Fin.last t))).comp measurable_snd)
      ((hm.chords t).comp hafter) ((hm.refresh t).comp hafter))

end
end SecondOrder
