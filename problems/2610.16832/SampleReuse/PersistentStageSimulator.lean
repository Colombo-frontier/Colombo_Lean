import SampleReuse.PersistentSignStage
import SampleReuse.PersistentPathwiseTransfer
import SecondOrder.FiniteObservableTransport

/-! A concrete stage simulator for the full scalar value/gradient/Hessian
oracle. All past blocks of all handles are fixed; exactly one current-block
array is supplied at each selected response. -/

open SecondOrder MeasureTheory ProbabilityTheory
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type}

def persistentStageIndex (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (β : ℝ) (j : Fin (T + 1)) (start n : ℕ) (s : S) : ℕ :=
  firstOrderLimitedProgress Θ β (P.query (start + n) s).1 j.val

def persistentStageStep (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start n : ℕ)
    (s : S) (a : Fin d → SignedCoefficient R) : S :=
  let q := P.query (start + n) s
  P.update (start + n) s (scaledFirstOrderTruncatedReply Θ A β
    (Function.update (past q.2) j a) (persistentStageIndex P Θ β j start n s) q.1)

def persistentStageState (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S)
    (n : ℕ) (h : FiniteHistory Unit (Fin d → SignedCoefficient R) n) : S :=
  finiteStateRun s₀ (persistentStageStep P Θ A β past j start) n h

def persistentStageKey (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S)
    (n : ℕ) (h : FiniteHistory Unit (Fin d → SignedCoefficient R) n) : Option Handle :=
  let s := persistentStageState P Θ A β past j start s₀ n h
  if persistentStageIndex P Θ β j start n s = j.val then some (P.query (start + n) s).2 else none

def persistentStagePoint (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S)
    (n : ℕ) (h : FiniteHistory Unit (Fin d → SignedCoefficient R) n) : Point d :=
  firstOrderDilation d T β (P.query (start + n) (persistentStageState P Θ A β past j start s₀ n h)).1 j

/-- A lower-index response cannot depend on the target array at all. -/
theorem persistentStageStep_array_irrelevant (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start n : ℕ) (s : S)
    (a b : Fin d → SignedCoefficient R) (hk : persistentStageIndex P Θ β j start n s < j.val) :
    persistentStageStep P Θ A β past j start n s a = persistentStageStep P Θ A β past j start n s b := by
  unfold persistentStageStep
  dsimp only
  apply congrArg (P.update (start + n) s)
  apply scaledFirstOrderTruncatedReply_prefix_invariant _ _ _ _ _ _ (by omega)
  · intro _ _; rfl
  · intro i hi
    have hn : i ≠ j := by intro he; subst i; omega
    simp only [Function.update_of_ne hn]

/-- The simulator computes the exact scalar jet using fixed past arrays
and the queried handle's target array. All future arrays and the target
hidden sign are absent from its input. -/
theorem persistentStageStep_full_reply (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start n : ℕ) (s : S)
    (hΘ : ∀ i, i.val < j.val → Θ i = Θ' i)
    (hz : ∀ r i, i.val < j.val → past r i = table r i) :
    persistentStageStep P Θ A β past j start n s (table (P.query (start + n) s).2 j) =
      P.update (start + n) s (scaledFirstOrderTruncatedReply Θ' A β
        (table (P.query (start + n) s).2)
        (persistentStageIndex P Θ' β j start n s) (P.query (start + n) s).1) := by
  have hk := (firstOrderLimitedProgress_le Θ β (P.query (start + n) s).1 j.val).2
  have hidx : persistentStageIndex P Θ β j start n s = persistentStageIndex P Θ' β j start n s :=
    firstOrderLimitedProgress_prefix Θ Θ' β _ j.val hΘ
  unfold persistentStageStep
  dsimp only
  rw [← hidx]
  apply congrArg (P.update (start + n) s)
  apply scaledFirstOrderTruncatedReply_prefix_invariant _ _ _ _ _ _ (by
    change persistentStageIndex P Θ β j start n s ≤ j.val at hk
    omega)
  · intro i hi
    exact hΘ i (lt_of_lt_of_le hi hk)
  · intro i hi
    by_cases he : i = j
    · subst i; simp only [Function.update_self]
    · rw [Function.update_of_ne he]
      apply hz
      have hv : i.val ≠ j.val := fun he' => he (Fin.ext he')
      change persistentStageIndex P Θ β j start n s ≤ j.val at hk
      omega

variable [Fintype Handle]
local instance : MeasurableSpace (Option Handle) := ⊤
local instance : MeasurableSingletonClass (Option Handle) := ⟨fun _ => trivial⟩

/-- The actual scalar-jet simulator with persistent current-block arrays
satisfies the capped stage activation bound. Only scalar horizon/calibration
conditions remain as hypotheses here. -/
theorem persistentStageSimulator_one_thirty_second
    (P : PersistentFirstOrderPolicy d T Handle S) (Θ : Fin (T + 1) → Fin d → Bool)
    (A β R : ℝ) (hR : 2 ≤ R) (past : Handle → FirstOrderCoefficients d T R)
    (j : Fin (T + 1)) (start : ℕ) (s₀ : S) (a₀ : Fin d → SignedCoefficient R) (cap N : ℕ)
    {L : ℝ} (hL : 0 < L)
    (hlog : L ≤ Real.log (1 / ((N + 1 : ℕ) * (2 * Real.exp (-(d : ℝ) / 128)))))
    (hbudget : 32 * ((cap : ℝ) * ((d : ℝ) / R ^ 2) + Real.log 2) ≤ L) :
    (kernelStageTrueLaw (signLaw d) (Measure.dirac ())
      (targetDisclosure (persistentStageKey P Θ A β past j start s₀) (fun r => r.isSome = true))
      (targetDisclosure_measurable _ (fun _ => measurable_of_countable _) _) cap
      (hiddenDisclosureKernel (persistentStageKey P Θ A β past j start s₀)
        (fun _ => measurable_of_countable _)
        (signStageTrueArray R hR (fun r => r.isSome = true) (fun _ => PMF.pure a₀)))
      (fun n => Kernel.const (FiniteHistory Unit (Fin d → SignedCoefficient R) n) (Measure.dirac a₀)) N).real
      (kernelSurvivalSet (fun n =>
        (kernelHiddenEvent (signStageActivation (persistentStagePoint P Θ A β past j start s₀)) n)ᶜ) N)ᶜ ≤ 1 / 32 := by
  exact persistent_sign_stage_one_thirty_second (Measure.dirac ()) R hR
    (persistentStageKey P Θ A β past j start s₀) (fun _ => measurable_of_countable _) (fun r => r.isSome = true)
    (fun _ => PMF.pure a₀) cap _ (persistentStagePoint P Θ A β past j start s₀)
    (fun _ => measurable_of_countable _) N hL hlog hbudget

end
end SampleReuse
