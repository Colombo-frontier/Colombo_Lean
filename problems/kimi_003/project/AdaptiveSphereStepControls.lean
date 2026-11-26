import AdaptiveSphereAction
import AdaptiveSphereStabilizer

/-! Explicit measurable old-past controls realizing every next-frame rotation.
The whole fixed product control space is used, so rank changes introduce no
measurable choice or varying-codomain premise. -/

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereStepControls

open Task006.Full Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStabilizer

noncomputable section
variable {d : ℕ}

/-- At every hypothetical old rank, conjugate the new residual control by the
explicit Householder step, or retain it when there is no rank increment. -/
def embedStepControls (k : ℕ) (hkd : k ≤ d) (B : OrthogonalGroup d)
    (q : E d) (g : ResidualControls d) : ResidualControls d := fun r =>
  if hr : r.val < k then
    let pivot : Fin d := ⟨r.val, by omega⟩
    if residualCoordinates r.val (by omega) (action B⁻¹ q) = 0 then g r
    else embedNext pivot (residualHouseholder pivot (action B⁻¹ q))
      (g (⟨r.val+1, by omega⟩ : Fin (d+1)))
  else g r

theorem embedStepControls_joint_measurable (k : ℕ) (hkd : k ≤ d) :
    Measurable (fun p : ResidualControls d × (OrthogonalGroup d × E d) =>
      embedStepControls k hkd p.2.1 p.2.2 p.1) := by
  classical
  apply measurable_pi_lambda
  intro r
  by_cases hr : r.val < k
  · let pivot : Fin d := ⟨r.val, by omega⟩
    have hcoords : Measurable (fun p : ResidualControls d × (OrthogonalGroup d × E d) =>
        action p.2.1⁻¹ p.2.2) := orthogonal_inverse_action_measurable.comp measurable_snd
    have hres := (continuous_residualCoordinates r.val (by omega)).measurable.comp hcoords
    have hH := (measurable_residualHouseholder pivot).comp hcoords
    have hg : Measurable (fun p : ResidualControls d × (OrthogonalGroup d × E d) => p.1 r) :=
      (measurable_pi_apply r).comp measurable_fst
    have hgNext : Measurable (fun p : ResidualControls d × (OrthogonalGroup d × E d) =>
        p.1 (⟨r.val+1, by omega⟩ : Fin (d+1))) :=
      (measurable_pi_apply _).comp measurable_fst
    have he := (embedNext_joint_measurable pivot).comp (hH.prodMk hgNext)
    have hresult : Measurable (fun p : ResidualControls d × (OrthogonalGroup d × E d) =>
        if residualCoordinates r.val (by omega) (action p.2.1⁻¹ p.2.2) = 0 then p.1 r
        else embedNext pivot (residualHouseholder pivot (action p.2.1⁻¹ p.2.2))
          (p.1 (⟨r.val+1, by omega⟩ : Fin (d+1)))) := by
      exact Measurable.ite (hres (measurableSet_singleton 0)) hg he
    simpa only [embedStepControls, dif_pos hr, Function.comp_def] using hresult
  · simpa only [embedStepControls, dif_neg hr, Function.comp_def] using
      ((measurable_pi_apply r).comp measurable_fst : Measurable
        (fun p : ResidualControls d × (OrthogonalGroup d × E d) => p.1 r))

theorem embedStepControls_control_continuous (k : ℕ) (hkd : k ≤ d)
    (B : OrthogonalGroup d) (q : E d) : Continuous (embedStepControls k hkd B q) := by
  apply continuous_pi
  intro r
  by_cases hr : r.val < k
  · let pivot : Fin d := ⟨r.val, by omega⟩
    by_cases hx : residualCoordinates r.val (by omega) (action B⁻¹ q) = 0
    · simpa only [embedStepControls, dif_pos hr, if_pos hx] using
        (continuous_apply r : Continuous (fun g : ResidualControls d => g r))
    · have hresult := (embedNext_control_continuous pivot
        (residualHouseholder pivot (action B⁻¹ q))).comp
        (continuous_apply (⟨r.val+1, by omega⟩ : Fin (d+1)) : Continuous
          (fun g : ResidualControls d => g (⟨r.val+1, by omega⟩ : Fin (d+1))))
      simpa only [embedStepControls, dif_pos hr, if_neg hx, Function.comp_def] using hresult
  · simpa only [embedStepControls, dif_neg hr] using
      (continuous_apply r : Continuous (fun g : ResidualControls d => g r))

/-- The old-history control realizes the exact next-frame rotation. -/
theorem rotateAtState_embedStepControls (k : ℕ) (hkd : k ≤ d)
    (state : FrameState d) (q : E d) (g : ResidualControls d) :
    rotateAtState state (embedStepControls k hkd state.2 q g) =
      rotateAtState (stateStep k hkd state q) g := by
  by_cases hr : state.1.val < k
  · let pivot : Fin d := ⟨state.1.val, by omega⟩
    by_cases hx : residualCoordinates state.1.val (by omega) (action state.2⁻¹ q) = 0
    · have hs : stateStep k hkd state q = state := by
        simp only [stateStep, dif_pos hr, if_pos hx]
      rw [hs]
      simp only [rotateAtState, embedStepControls, dif_pos hr, if_pos hx]
    · have hs : stateStep k hkd state q =
          ((⟨state.1.val+1, by omega⟩, residualUpdate pivot state.2 q) : FrameState d) := by
        simp only [stateStep, dif_pos hr, if_neg hx, pivot]
      rw [hs]
      have he := embedNext_full_identity pivot
        (residualHouseholder pivot (action state.2⁻¹ q))
        (g (⟨state.1.val+1, by omega⟩ : Fin (d+1)))
      simp only [rotateAtState, embedStepControls, dif_pos hr, if_neg hx]
      rw [he]
      simp only [residualUpdate, fullResidualStep, mul_inv_rev]
      dsimp only [pivot]
      group
  · have hs : stateStep k hkd state q = state := by
      simp only [stateStep, dif_neg hr]
    rw [hs]
    simp only [rotateAtState, embedStepControls, dif_neg hr]

/-- Before the stopping threshold, every resulting next-frame rotation fixes
this actual query. At or after the threshold a genuinely stopped policy has q=0. -/
theorem rotateAtState_embedStepControls_fixes_query (k : ℕ) (hkd : k ≤ d)
    (state : FrameState d) (q : E d) (g : ResidualControls d)
    (hstop : k ≤ state.1.val → q = 0) :
    action (rotateAtState state (embedStepControls k hkd state.2 q g)) q = q := by
  by_cases hr : state.1.val < k
  · let pivot : Fin d := ⟨state.1.val, by omega⟩
    by_cases hx : residualCoordinates state.1.val (by omega) (action state.2⁻¹ q) = 0
    · apply conjugated_action_fixes_query
      simpa only [embedStepControls, dif_pos hr, if_pos hx] using
        block_rotation_fixes_zero_residual state.1.val (by omega)
          (action state.2⁻¹ q) hx (g state.1)
    · apply conjugated_action_fixes_query
      simpa only [embedStepControls, dif_pos hr, if_neg hx] using
        embedded_rotation_fixes_query pivot (action state.2⁻¹ q) hx
          (g (⟨state.1.val+1, by omega⟩ : Fin (d+1)))
  · rw [hstop (not_lt.mp hr), map_zero]

#print axioms embedStepControls_joint_measurable
#print axioms embedStepControls_control_continuous
#print axioms rotateAtState_embedStepControls
#print axioms rotateAtState_embedStepControls_fixes_query
end
end Task006.AdaptiveSphereStepControls
