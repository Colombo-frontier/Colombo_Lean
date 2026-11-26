import SecondOrder.TrackerMemoryMeasurability

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def trackedEncode {d L : ℕ} (z : TrackedState d L) : IdealState d × EpochClock × TrackerMemory d L :=
  (z.physical,z.clock,z.memory)

instance trackedStateMeasurableSpace (d L : ℕ) : MeasurableSpace (TrackedState d L) :=
  MeasurableSpace.comap trackedEncode inferInstance

theorem trackedEncode_injective {d L : ℕ} : Function.Injective (@trackedEncode d L) := by
  intro x y he
  cases x
  cases y
  simpa [trackedEncode,TrackedState.mk.injEq] using he

theorem trackedEncode_measurable {d L : ℕ} : Measurable (@trackedEncode d L) := comap_measurable _

theorem tracked_measurable_iff {A : Type*} [MeasurableSpace A] {d L : ℕ} {z : A → TrackedState d L} :
    Measurable z ↔ Measurable (fun a => trackedEncode (z a)) := by
  constructor
  · exact fun hz => trackedEncode_measurable.comp hz
  · intro hz s hs
    obtain ⟨t,ht,rfl⟩ := hs
    exact hz ht

theorem tracked_measurable_fields {A : Type*} [MeasurableSpace A] {d L : ℕ} {z : A → TrackedState d L} :
    Measurable z ↔ Measurable (fun a => (z a).physical) ∧ Measurable (fun a => (z a).clock) ∧
      Measurable (fun a => (z a).memory) := by
  rw [tracked_measurable_iff]
  constructor
  · intro hz
    exact ⟨hz.fst,hz.snd.fst,hz.snd.snd⟩
  · rintro ⟨hp,hc,hm⟩
    exact hp.prodMk (hc.prodMk hm)

theorem epochClockStep_variable_measurable {A : Type*} [MeasurableSpace A] (q : ℕ)
    {t : A → ℕ} {g : A → Bool} {z : A → EpochClock} (ht : Measurable t)
    (hg : Measurable g) (hz : Measurable z) :
    Measurable (fun a => epochClockStep q (t a) (g a) (z a)) := by
  have hh : Measurable (fun w : A × ℕ => epochClockStep q w.2 (g w.1) (z w.1)) := by
    apply measurable_from_prod_countable
    intro n
    exact epochClockStep_measurable q n hg hz
  exact hh.comp (measurable_id.prodMk ht)

theorem trackedMove_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ} (τ : ℝ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} (hz : Measurable z) (hr : Measurable r) :
    Measurable (fun a => trackedMove τ (z a) (r a)) :=
  decideMove_measurable τ (trackerRead_measurable (tracked_measurable_fields.mp hz).2.2) hr

theorem trackedNext_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ} (Lip s τ : ℝ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    (hz : Measurable z) (hr : Measurable r) (hb : Measurable b) :
    Measurable (fun a => trackedNext Lip s τ (z a) (r a) (b a)) :=
  idealStep_measurable Lip s (tracked_measurable_fields.mp hz).1 (trackedMove_measurable τ hz hr) hb

theorem trackedClock_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ} (q : ℕ) (τ : ℝ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} (hz : Measurable z) (hr : Measurable r) :
    Measurable (fun a => trackedClock q τ (z a) (r a)) := by
  have hf := tracked_measurable_fields.mp hz
  have hp := state_measurable_fields.mp hf.1
  exact epochClockStep_variable_measurable q (hp.2.2.1.add hp.2.2.2.1)
    (isGradientMove_measurable hf.1 (trackedMove_measurable τ hz hr)) hf.2.1

theorem trackedRestart_measurableSet {A : Type*} [MeasurableSpace A] {d L : ℕ} (q : ℕ) (τ : ℝ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} (hz : Measurable z) (hr : Measurable r) :
    MeasurableSet {a | trackedRestart q τ (z a) (r a)} := by
  have hnew := (epochClockEncode_measurable.comp (trackedClock_measurable q τ hz hr)).fst
  have hold := (epochClockEncode_measurable.comp (tracked_measurable_fields.mp hz).2.1).fst
  exact (measurableSet_eq_fun_of_countable hnew hold).compl

theorem trackedStep_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ} (q : ℕ) (Lip s τ : ℝ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    {packet : A → BinaryNode L → Point d} {anchor : A → Point d}
    (hz : Measurable z) (hr : Measurable r) (hb : Measurable b)
    (hp : Measurable packet) (ha : Measurable anchor) :
    Measurable (fun a => trackedStep q Lip s τ (z a) (r a) (b a) (packet a) (anchor a)) := by
  have hf := tracked_measurable_fields.mp hz
  have hn := trackedNext_measurable Lip s τ hz hr hb
  have hnfields := state_measurable_fields.mp hn
  dsimp only [trackedStep]
  apply Measurable.ite (hnfields.2.1 (measurableSet_singleton true))
  · apply tracked_measurable_fields.mpr
    refine ⟨hn,trackedClock_measurable q τ hz hr,?_⟩
    exact Measurable.ite (trackedRestart_measurableSet q τ hz hr)
      (trackerReset_measurable hnfields.1 ha) (trackerPush_measurable hf.2.2 hnfields.1 hp)
  · exact tracked_measurable_fields.mpr ⟨hn,hf.2.1,hf.2.2⟩

theorem trackedInitial_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    {anchor : A → Point d} (ha : Measurable anchor) : Measurable (fun a => trackedInitial (L := L) (anchor a)) :=
  tracked_measurable_fields.mpr ⟨measurable_const,measurable_const,trackerReset_measurable measurable_const ha⟩

end
end SecondOrder
