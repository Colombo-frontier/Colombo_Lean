import AdaptiveSphereStepControls
import AdaptiveSphereStopped

/-! Concrete transcript/frame identities for the genuinely stopped adaptive
observer. These instantiate the geometric controls with the canonical policy. -/

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereActualStep

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStepControls Task006.AdaptiveSphereStopped
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable

noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem column_mul_action (R Q : OrthogonalGroup d) (j : Fin d) :
    column (R*Q) j = action R (column Q j) := by
  apply WithLp.ofLp_injective 2
  funext i
  rfl

def stepControls (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N)
    (g : ResidualControls d) (h : Transcript N) : ResidualControls d :=
  embedStepControls k hkd (frameFromTranscript A weight tape seed k hkd t.val h).2
    (effectiveVector weight tape (A.action t seed h)) g

theorem stepControls_joint_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) :
    Measurable (fun p : ResidualControls d × Transcript N =>
      stepControls A weight tape seed k hkd t p.1 p.2) := by
  have hB := (measurable_snd.comp
    (measurable_frameFromTranscript A weight tape seed k hkd t.val)).comp
      (measurable_snd : Measurable (Prod.snd : ResidualControls d × Transcript N → Transcript N))
  have hinput : Measurable (fun h : Transcript N => (seed,h)) :=
    measurable_const.prodMk measurable_id
  have hq := ((measurable_effectiveVector weight tape).comp
    ((A.action_measurable t).comp hinput)).comp
      (measurable_snd : Measurable (Prod.snd : ResidualControls d × Transcript N → Transcript N))
  have hr := (embedStepControls_joint_measurable k hkd).comp
    (measurable_fst.prodMk (hB.prodMk hq))
  simpa only [stepControls, Function.comp_def] using hr

theorem stepControls_control_continuous (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (h : Transcript N) :
    Continuous (fun g => stepControls A weight tape seed k hkd t g h) :=
  embedStepControls_control_continuous k hkd _ _

theorem actualState_succ (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N)
    (j : Fin d) (Q : OrthogonalGroup d) :
    actualState A weight tape seed k hkd (t.val+1) j Q =
      stateStep k hkd (actualState A weight tape seed k hkd t.val j Q)
        (effectiveVector weight tape (A.action t seed (history A weight tape seed t.val j Q))) := by
  have hpast : ∀ i : Fin N, i.val < t.val →
      history A weight tape seed (t.val+1) j Q i = history A weight tape seed t.val j Q i := by
    intro i hi
    exact runPrefix_coordinate_stable A (linearSample weight (column Q j)) tape seed
      t.val (t.val+1) (Nat.le_succ _) i hi
  unfold actualState
  rw [frameFromTranscript_succ_old_past_only A weight tape seed k hkd t.val
    (history A weight tape seed (t.val+1) j Q) (history A weight tape seed t.val j Q) hpast]
  simp only [frameFromTranscript, dif_pos t.isLt]

theorem orbitTransform_step_factorization (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N)
    (j : Fin d) (g : ResidualControls d) (Q : OrthogonalGroup d) :
    orbitTransform A weight tape seed k hkd (t.val+1) j g Q =
      orbitTransform A weight tape seed k hkd t.val j
        (stepControls A weight tape seed k hkd t g (history A weight tape seed t.val j Q)) Q := by
  unfold orbitTransform
  rw [actualState_succ]
  rw [← rotateAtState_embedStepControls]
  rfl

/-- A real scalar reply is fixed by the constructed next-frame rotation. The
RankStopped premise is a protocol fact satisfied by stoppedObserver, not a
posterior or risk premise. -/
theorem next_rotation_fixes_effective_query (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N)
    (j : Fin d) (g : ResidualControls d) (Q : OrthogonalGroup d)
    (hstop : RankStopped A weight tape seed k hkd) :
    action (rotateAtState (actualState A weight tape seed k hkd (t.val+1) j Q) g)
      (effectiveVector weight tape (A.action t seed (history A weight tape seed t.val j Q))) =
        effectiveVector weight tape (A.action t seed (history A weight tape seed t.val j Q)) := by
  rw [actualState_succ, ← rotateAtState_embedStepControls]
  apply rotateAtState_embedStepControls_fixes_query
  intro hr
  have ha := hstop t (history A weight tape seed t.val j Q) hr
  rw [ha]
  rfl

/-- Pointwise refinement of transcript invariance, using the actual reply
recursion and the fact that the full query is fixed. -/
theorem next_history_fixed_of_old_history_fixed (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : Fin N) (j : Fin d) (g : ResidualControls d) (Q : OrthogonalGroup d)
    (hstop : RankStopped A weight tape seed k hkd)
    (hfix : history A weight tape seed t.val j
      (orbitTransform A weight tape seed k hkd (t.val+1) j g Q) =
        history A weight tape seed t.val j Q) :
    history A weight tape seed (t.val+1) j
      (orbitTransform A weight tape seed k hkd (t.val+1) j g Q) =
        history A weight tape seed (t.val+1) j Q := by
  let R := rotateAtState (actualState A weight tape seed k hkd (t.val+1) j Q) g
  let q := effectiveVector weight tape (A.action t seed (history A weight tape seed t.val j Q))
  have hRq : action R q = q := next_rotation_fixes_effective_query A weight tape seed k hkd t j g Q hstop
  have hinner : inner ℝ (column (orbitTransform A weight tape seed k hkd (t.val+1) j g Q) j) q =
      inner ℝ (column Q j) q := by
    change inner ℝ (column (R*Q) j) q = _
    rw [column_mul_action]
    calc
      inner ℝ (action R (column Q j)) q = inner ℝ (action R (column Q j)) (action R q) := by rw [hRq]
      _ = inner ℝ (column Q j) q := (action R).inner_map_map _ _
  unfold history at hfix ⊢
  rw [runPrefix, runPrefix, dif_pos t.isLt, dif_pos t.isLt, hfix]
  apply congrArg (Function.update _ t)
  rw [scalarReply_linear, scalarReply_linear]
  exact hinner

#print axioms column_mul_action
#print axioms stepControls_joint_measurable
#print axioms actualState_succ
#print axioms orbitTransform_step_factorization
#print axioms next_rotation_fixes_effective_query
#print axioms next_history_fixed_of_old_history_fixed
end
end Task006.AdaptiveSphereActualStep
