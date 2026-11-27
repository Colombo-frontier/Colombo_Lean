import AdaptiveSphereGlobalMean
import AdaptiveSphereOriginalHandleEvent

/-! Distinct informative handles can be read measurably from the stopped
scalar history, its exogenous tape and seed. Countability is used only for the
finite vector of handle labels, never for the real-valued history. -/
open MeasureTheory Set

namespace Task006.AdaptiveSphereObservedHandles
open Task006.Full Task006.Full.OracleAlgorithm Task006.HaarRebalancing
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStopped Task006.AdaptiveSphereJoint
open Task006.AdaptiveSphereGlobal Task006.RankHandleCount
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) := ⊤
instance optionNatMeasurableSingletonClass : MeasurableSingletonClass (Option ℕ) := ⟨fun _ => trivial⟩

def actionLabel (a : QueryAction d) : Option ℕ := a.map Prod.fst

theorem actionLabel_measurable : Measurable (actionLabel (d := d)) := by
  let encoded : Unit ⊕ (ℕ × Space d) → Option ℕ :=
    Sum.elim (fun _ => none) (fun p => some p.1)
  have hsome : Measurable (some : ℕ → Option ℕ) := measurable_of_countable _
  have he : Measurable encoded := measurable_const.sumElim (hsome.comp measurable_fst)
  have heq : actionLabel (d := d) = encoded ∘ actionToSum d := by
    funext a
    cases a <;> rfl
  rw [heq]
  exact he.comp measurable_actionToSum

def labelHandles (labels : Fin N → Option ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => (labels i).toFinset)

def labelInformativeCount (labels : Fin N → Option ℕ) (tape : ℕ → ℝ) : ℝ :=
  ∑ h ∈ labelHandles labels, nonzeroStatus (tape h)

theorem labelInformativeCount_joint_measurable :
    Measurable (fun p : (Fin N → Option ℕ) × (ℕ → ℝ) => labelInformativeCount p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro labels
  change Measurable (fun tape : ℕ → ℝ => ∑ h ∈ labelHandles labels, nonzeroStatus (tape h))
  have hm := Finset.measurable_fun_sum (labelHandles labels)
    (fun h _ => nonzeroStatus_measurable.comp (measurable_pi_apply h))
  simpa only [Function.comp_def] using hm

def observedLabels (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (w : Exogenous S × Transcript N) : Fin N → Option ℕ :=
  fun i => actionLabel (stopAction A id w.1.2 w.1.1 k hkd i w.2)

theorem observedLabels_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) :
    Measurable (observedLabels A k hkd) := by
  apply measurable_pi_lambda
  intro i
  exact actionLabel_measurable.comp (stopAction_joint_measurable A k hkd i)

def observedStoppedK (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (w : Exogenous S × Transcript N) : ℝ :=
  labelInformativeCount (observedLabels A k hkd w) w.1.2

theorem observedStoppedK_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) :
    Measurable (observedStoppedK A k hkd) := by
  have hm := (labelInformativeCount_joint_measurable (N := N)).comp
    ((observedLabels_measurable A k hkd).prodMk measurable_fst.snd)
  change Measurable (fun w => labelInformativeCount (observedLabels A k hkd w) w.1.2)
  simpa only [Function.comp_def] using hm

theorem observedStoppedK_actual_eq (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (w : Exogenous S × OrthogonalGroup d) :
    observedStoppedK A k hkd (jointObservation A k hkd N j w) =
      (((stoppedObserver A id w.1.2 w.1.1 k hkd).informativeHandles
        (linearSample id (column w.2 j)) w.1.2 ()).card : ℝ) := by
  let B := stoppedObserver A id w.1.2 w.1.1 k hkd
  let F := linearSample id (column w.2 j)
  have hlabels : observedLabels A k hkd (jointObservation A k hkd N j w) =
      fun i : Fin N => (B.executedAction F w.1.2 () i).map Prod.fst := by
    funext i
    have ha := action_finalTranscript_eq B F w.1.2 () i
    exact congrArg (fun a : QueryAction d => a.map Prod.fst) ha
  have hhandles : labelHandles (observedLabels A k hkd (jointObservation A k hkd N j w)) =
      B.queriedHandles F w.1.2 () := by
    rw [hlabels]
    rfl
  change (∑ h ∈ labelHandles (observedLabels A k hkd (jointObservation A k hkd N j w)),
    nonzeroStatus (w.1.2 h)) = _
  rw [hhandles]
  calc
    _ = ∑ h ∈ B.informativeHandles F w.1.2 (), (1:ℝ) := by
      rw [informativeHandles,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hz : w.1.2 h = 0 <;> simp [nonzeroStatus,hz]
    _ = _ := by simp [B,F]

#print axioms observedStoppedK_measurable
#print axioms observedStoppedK_actual_eq
end
end Task006.AdaptiveSphereObservedHandles
