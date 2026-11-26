import NCConcave16991.BranchOracleInterpreter
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # Measurable public accounting and full-history reference states -/

namespace NCConcave16991.BranchOracle
noncomputable section
open MeasureTheory

instance wordProfileMeasurableSpace {ι : Type*} : MeasurableSpace (WordProfile ι) := ⊤

theorem wordProfile_measurable_any {ι X : Type*} [MeasurableSpace X] (f : WordProfile ι → X) : Measurable f :=
  measurable_iff_comap_le.mpr le_top

theorem publicUpdate_measurable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {M : ℕ} (ρ : ℝ) (site : Fin M → ℕ) :
    Measurable (fun q : (WordProfile ι × ℕ) × ι ↦ WordProfile.close ρ site q.1.2 (q.1.1.matrixScheduleStep (fun _ ↦ q.2))) := by
  apply measurable_from_prod_countable_left
  intro i
  apply measurable_from_prod_countable_left
  intro r
  exact wordProfile_measurable_any _

namespace Reference

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable {D : ℝ} (K : KnownDualDomain (GlobalHardEuclidean.dualDimension V) D)

def stateData (s : State (n := n) V K) :
    (WordProfile (Fin n) × ℕ) × OraclePolicy.History K (n := n) (dx := GlobalHardEuclidean.primalDimension V) :=
  ((s.profile, s.released), s.history)

instance stateMeasurableSpace : MeasurableSpace (State (n := n) V K) :=
  MeasurableSpace.comap (stateData V K) inferInstance

theorem stateData_measurable : Measurable (stateData (n := n) V K) := measurable_iff_comap_le.mpr le_rfl

theorem profile_measurable : Measurable (fun s : State (n := n) V K ↦ s.profile) :=
  measurable_fst.comp (measurable_fst.comp (stateData_measurable V K))

theorem released_measurable : Measurable (fun s : State (n := n) V K ↦ s.released) :=
  measurable_snd.comp (measurable_fst.comp (stateData_measurable V K))

theorem history_measurable : Measurable (fun s : State (n := n) V K ↦ s.history) :=
  measurable_snd.comp (stateData_measurable V K)

theorem state_mk_measurable {X : Type*} [MeasurableSpace X]
    (p : X → WordProfile (Fin n)) (r : X → ℕ)
    (h : X → OraclePolicy.History K (n := n) (dx := GlobalHardEuclidean.primalDimension V))
    (hp : Measurable p) (hr : Measurable r) (hh : Measurable h) :
    Measurable (fun x ↦ (⟨p x, r x, h x⟩ : State (n := n) V K)) := by
  apply measurable_iff_comap_le.mpr
  dsimp only [stateMeasurableSpace]
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun x : X ↦ ((p x, r x), h x))
    (inferInstance : MeasurableSpace ((WordProfile (Fin n) × ℕ) ×
      OraclePolicy.History K (n := n) (dx := GlobalHardEuclidean.primalDimension V))) ≤
    (inferInstance : MeasurableSpace X)
  exact ((hp.prodMk hr).prodMk hh).comap_le

end Reference
end
end NCConcave16991.BranchOracle
