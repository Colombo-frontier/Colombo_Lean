import NCConcave16991.GlobalHardConnectorDirection
import NCConcave16991.GlobalHardStateTransport
import NCConcave16991.GlobalHardDual
import NCConcave16991.GlobalHardConnectorLocalGradient

/-! # The exact averaged connector ray and its actual derivative -/

namespace NCConcave16991.GlobalHard
noncomputable section
open LocalizationScalar LocalizationRadial
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def outerSum (z : Joint V) : ℝ := ∑ j, outerAt V u v z j

def outerConnectorSumDerivative (z : Joint V) : ℝ := ∑ j,
  outerConnectorDerivative (u j) (v j) (precedingScore V v j z) (stateProj V j z) (aProj V j z) (bProj V j z)

theorem average_zero_dual_connector_form (d r μ : ℝ) (x : Primal V) :
    average V B u v d r μ (atDual V x 0) =
      d * ‖connectorTuple V (atDual V x 0)‖ ^ 2 + outerSum V u v (atDual V x 0) := by
  rw [average_eq_sum, connectorTuple_norm_sq, Finset.mul_sum]
  unfold outerSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold stageAverage
  have hp := BranchGeometry.fullPipe_average (B j) d r μ
    (aProj V j (atDual V x 0)) (bProj V j (atDual V x 0))
    (fun k ↦ (0 : V j k))
  change (1 / (Fintype.card ι : ℝ)) * ∑ i,
    PipeSmoothness.component (B j) d r μ i (pipeProj V j (atDual V x 0)) = _ at hp
  rw [hp]
  simp only [inner_zero_right, sub_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    map_zero, sub_self, Finset.sum_const_zero, mul_zero, zero_add, add_zero]
  rfl

theorem average_connector_normal_form (d r μ : ℝ) (z : Joint V) :
    average V B u v d r μ z = d * ‖connectorTuple V z‖ ^ 2 +
      dualLinear V r (WithLp.fst z) (WithLp.snd z) -
      BranchGeometry.beta ι / 2 * (μ * ‖WithLp.snd z‖ ^ 2 + dualEdgeEnergy V B (WithLp.snd z)) +
      outerSum V u v z := by
  have hh := average_dual_normal_form V B u v d r μ (WithLp.fst z) (WithLp.snd z)
  rw [average_zero_dual_connector_form] at hh
  change average V B u v d r μ z = _ at hh
  have hc : connectorTuple V (atDual V (WithLp.fst z) 0) = connectorTuple V z := rfl
  have ho : outerSum V u v (atDual V (WithLp.fst z) 0) = outerSum V u v z := rfl
  rw [hc, ho] at hh
  linarith

theorem connectorTuple_connectorRay (z : Joint V) (t : ℝ) :
    connectorTuple V (connectorRay V z t) = t • connectorTuple V z := by
  apply PiLp.ext
  intro j
  exact connectorProj_connectorRay V z t j

theorem dual_connectorRay (z : Joint V) (t : ℝ) : WithLp.snd (connectorRay V z t) = WithLp.snd z := by
  apply PiLp.ext
  intro j
  exact dualProj_connectorRay V z t j

theorem dualLinear_connectorRay (r : ℝ) (z : Joint V) (t : ℝ) :
    dualLinear V r (WithLp.fst (connectorRay V z t)) (WithLp.snd z) =
      t * dualLinear V r (WithLp.fst z) (WithLp.snd z) := by
  simp only [dualLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  change (∑ j, r * (⟪aProj V j (connectorRay V z t), dualLayer V j 0 (WithLp.snd z)⟫_ℝ -
    ⟪bProj V j (connectorRay V z t), dualLayer V j (Fin.last N) (WithLp.snd z)⟫_ℝ)) = _
  simp only [aProj_connectorRay, bProj_connectorRay, real_inner_smul_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change r * (t * ⟪aProj V j z, dualLayer V j 0 (WithLp.snd z)⟫_ℝ -
    t * ⟪bProj V j z, dualLayer V j (Fin.last N) (WithLp.snd z)⟫_ℝ) =
    t * (r * (⟪aProj V j z, dualLayer V j 0 (WithLp.snd z)⟫_ℝ -
      ⟪bProj V j z, dualLayer V j (Fin.last N) (WithLp.snd z)⟫_ℝ))
  ring

theorem average_connector_ray (d r μ : ℝ) (z : Joint V) (t : ℝ) :
    average V B u v d r μ (connectorRay V z t) =
      d * t ^ 2 * ‖connectorTuple V z‖ ^ 2 + t * dualLinear V r (WithLp.fst z) (WithLp.snd z) -
      BranchGeometry.beta ι / 2 * (μ * ‖WithLp.snd z‖ ^ 2 + dualEdgeEnergy V B (WithLp.snd z)) +
      outerSum V u v (connectorRay V z t) := by
  rw [average_connector_normal_form, connectorTuple_connectorRay, dual_connectorRay, dualLinear_connectorRay]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem outerSum_connector_ray_hasDerivAt (z : Joint V) :
    HasDerivAt (fun t : ℝ ↦ outerSum V u v (connectorRay V z t)) (outerConnectorSumDerivative V u v z) 1 := by
  have hj (j : Fin M) : HasDerivAt (fun t : ℝ ↦ outerAt V u v (connectorRay V z t) j)
      (outerConnectorDerivative (u j) (v j) (precedingScore V v j z) (stateProj V j z) (aProj V j z) (bProj V j z)) 1 := by
    have hh := outerStage_connector_ray_hasDerivAt (u j) (v j) (precedingScore V v j z)
      (stateProj V j z) (aProj V j z) (bProj V j z)
    convert hh using 1
    funext t
    simp only [outerAt, precedingScore_connectorRay, stateProj_connectorRay, aProj_connectorRay, bProj_connectorRay]
  convert (HasDerivAt.sum (u := Finset.univ) (fun j _ ↦ hj j)) using 1
  · funext t
    simp only [outerSum, Finset.sum_apply]
  · rfl

theorem average_connector_ray_hasDerivAt (d r μ : ℝ) (z : Joint V) :
    HasDerivAt (fun t : ℝ ↦ average V B u v d r μ (connectorRay V z t))
      (2 * d * ‖connectorTuple V z‖ ^ 2 + dualLinear V r (WithLp.fst z) (WithLp.snd z) +
        outerConnectorSumDerivative V u v z) 1 := by
  have hq := (((hasDerivAt_id (1 : ℝ)).pow 2).const_mul (d * ‖connectorTuple V z‖ ^ 2)).add
    ((hasDerivAt_id (1 : ℝ)).mul_const (dualLinear V r (WithLp.fst z) (WithLp.snd z)))
  have hh := (hq.sub_const (BranchGeometry.beta ι / 2 *
    (μ * ‖WithLp.snd z‖ ^ 2 + dualEdgeEnergy V B (WithLp.snd z)))).add
      (outerSum_connector_ray_hasDerivAt V u v z)
  convert hh using 1
  · funext t
    rw [average_connector_ray]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  · norm_num <;> ring

end
end NCConcave16991.GlobalHard
