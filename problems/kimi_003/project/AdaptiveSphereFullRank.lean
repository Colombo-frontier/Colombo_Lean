import AdaptiveSphereActualStep

/-! No stopping restriction is needed for an original policy when k=d: after
full rank the residual group is trivial, so every subsequent observation is
fixed pointwise. -/
open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereFullRank
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStepControls Task006.AdaptiveSphereStopped
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereActualStep Task006.AdaptiveSphereOrbit Task006.AdaptiveSphereGeometry
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem blockOrthogonal_full (g : OrthogonalGroup (d-d)) :
    blockOrthogonal d d le_rfl g = 1 := by
  apply Subtype.ext
  ext i j
  change (blockOrthogonal d d le_rfl g : Matrix (Fin d) (Fin d) ℝ) i j =
    (1 : Matrix (Fin d) (Fin d) ℝ) i j
  rw [blockOrthogonal_apply]
  simp only [j.isLt,dif_pos,Matrix.one_apply]

theorem rotateAtState_full_rank (state : FrameState d) (hr : state.1.val = d)
    (g : ResidualControls d) : rotateAtState state g = 1 := by
  have heq : state = (⟨d,by omega⟩,state.2) := by
    exact Prod.ext (Fin.ext hr) rfl
  rw [heq]
  simp only [rotateAtState,blockOrthogonal_full,mul_one,mul_inv_cancel]

theorem next_rotation_fixes_effective_query_full (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : Fin N) (j : Fin d)
    (g : ResidualControls d) (Q : OrthogonalGroup d) :
    action (rotateAtState (actualState A weight tape seed d le_rfl (t.val+1) j Q) g)
      (effectiveVector weight tape (A.action t seed (history A weight tape seed t.val j Q))) =
        effectiveVector weight tape (A.action t seed (history A weight tape seed t.val j Q)) := by
  rw [actualState_succ]
  by_cases hr : (actualState A weight tape seed d le_rfl t.val j Q).1.val < d
  · rw [← rotateAtState_embedStepControls]
    apply rotateAtState_embedStepControls_fixes_query
    intro hge
    omega
  · have hfull : (actualState A weight tape seed d le_rfl t.val j Q).1.val = d := by omega
    have hs : stateStep d le_rfl (actualState A weight tape seed d le_rfl t.val j Q)
        (effectiveVector weight tape (A.action t seed (history A weight tape seed t.val j Q))) =
        actualState A weight tape seed d le_rfl t.val j Q := by
      simp only [stateStep,dif_neg hr]
    rw [hs,rotateAtState_full_rank _ hfull,action_one]

theorem next_history_fixed_of_old_history_fixed_full (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (t : Fin N)
    (j : Fin d) (g : ResidualControls d) (Q : OrthogonalGroup d)
    (hfix : history A weight tape seed t.val j
      (orbitTransform A weight tape seed d le_rfl (t.val+1) j g Q) =
        history A weight tape seed t.val j Q) :
    history A weight tape seed (t.val+1) j
      (orbitTransform A weight tape seed d le_rfl (t.val+1) j g Q) =
        history A weight tape seed (t.val+1) j Q := by
  let R := rotateAtState (actualState A weight tape seed d le_rfl (t.val+1) j Q) g
  let q := effectiveVector weight tape (A.action t seed (history A weight tape seed t.val j Q))
  have hRq : action R q = q := next_rotation_fixes_effective_query_full A weight tape seed t j g Q
  have hinner : inner ℝ (column (orbitTransform A weight tape seed d le_rfl (t.val+1) j g Q) j) q =
      inner ℝ (column Q j) q := by
    change inner ℝ (column (R*Q) j) q = _
    rw [column_mul_action]
    calc
      inner ℝ (action R (column Q j)) q = inner ℝ (action R (column Q j)) (action R q) := by rw [hRq]
      _ = inner ℝ (column Q j) q := (action R).inner_map_map _ _
  unfold history at hfix ⊢
  rw [runPrefix,runPrefix,dif_pos t.isLt,dif_pos t.isLt,hfix]
  apply congrArg (Function.update _ t)
  rw [scalarReply_linear,scalarReply_linear]
  exact hinner

/-- Actual residual symmetry for EVERY original canonical adaptive policy,
without requiring it to stop its queries when the direction becomes known. -/
theorem original_residual_invariance (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (j : Fin d)
    (t : ℕ) (ht : t ≤ N) :
    (∀ g : ResidualControls d,
      MeasurePreserving (orbitTransform A weight tape seed d le_rfl t j g)
        (orthogonalHaarProbability d) (orthogonalHaarProbability d)) ∧
    (∀ (g : ResidualControls d) (Q : OrthogonalGroup d),
      history A weight tape seed t j (orbitTransform A weight tape seed d le_rfl t j g Q) =
        history A weight tape seed t j Q) := by
  induction t with
  | zero =>
    exact ⟨orbitTransform_zero_measurePreserving A weight tape seed d le_rfl j,
      orbitTransform_zero_fixes_history A weight tape seed d le_rfl j⟩
  | succ t ih =>
    have hlt : t < N := by omega
    let ti : Fin N := ⟨t,hlt⟩
    obtain ⟨hmp,hfix⟩ := ih (by omega)
    have hnewmp (g : ResidualControls d) :
        MeasurePreserving (orbitTransform A weight tape seed d le_rfl (t+1) j g)
          (orthogonalHaarProbability d) (orthogonalHaarProbability d) := by
      have hcontrol : Measurable (stepControls A weight tape seed d le_rfl ti g) := by
        have hr := (stepControls_joint_measurable A weight tape seed d le_rfl ti).comp
          (measurable_const.prodMk measurable_id : Measurable (fun h : Transcript N => (g,h)))
        simpa only [Function.comp_def] using hr
      have h := observable_dependent_symmetry_measurePreserving
        (history A weight tape seed t j) (measurable_history A weight tape seed t j)
        (stepControls A weight tape seed d le_rfl ti g) hcontrol
        (orbitTransform A weight tape seed d le_rfl t j) hmp
        (orbitTransform_joint_measurable A weight tape seed d le_rfl t j)
        (orbitTransform_control_continuous A weight tape seed d le_rfl t j) hfix
      have heq : (fun Q => orbitTransform A weight tape seed d le_rfl t j
          (stepControls A weight tape seed d le_rfl ti g (history A weight tape seed t j Q)) Q) =
          orbitTransform A weight tape seed d le_rfl (t+1) j g := by
        funext Q
        exact (orbitTransform_step_factorization A weight tape seed d le_rfl ti j g Q).symm
      rw [heq] at h
      exact h
    refine ⟨hnewmp,?_⟩
    intro g Q
    apply next_history_fixed_of_old_history_fixed_full A weight tape seed ti j g Q
    rw [orbitTransform_step_factorization A weight tape seed d le_rfl ti j g Q]
    exact hfix _ Q

#print axioms blockOrthogonal_full
#print axioms rotateAtState_full_rank
#print axioms original_residual_invariance
end
end Task006.AdaptiveSphereFullRank
