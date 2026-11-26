import SecondOrder.EuclideanBlocks
import SecondOrder.FirstOrderProgress

namespace SecondOrder
noncomputable section

abbrev FirstOrderDimension (d T : ℕ) := (T+1)*d

/-- Flattening preserves the actual Euclidean block norm. -/
def firstOrderCoordinates (d T : ℕ) : Point (FirstOrderDimension d T) ≃ₗᵢ[ℝ] FirstOrderSpace d T :=
  euclideanBlockEquiv (T+1) d

theorem firstOrderCoordinates_norm (d T : ℕ) (x : Point (FirstOrderDimension d T)) :
    ‖firstOrderCoordinates d T x‖=‖x‖ := (firstOrderCoordinates d T).norm_map x

def firstOrderDilation (d T : ℕ) (β : ℝ) :
    Point (FirstOrderDimension d T) →L[ℝ] FirstOrderSpace d T :=
  β • (firstOrderCoordinates d T).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem firstOrderDilation_apply (d T : ℕ) (β : ℝ) (x : Point (FirstOrderDimension d T)) :
    firstOrderDilation d T β x=β • firstOrderCoordinates d T x := rfl

theorem firstOrderDilation_norm (d T : ℕ) (β : ℝ) : ‖firstOrderDilation d T β‖≤|β| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg β)
  intro x
  simp only [firstOrderDilation_apply,norm_smul,Real.norm_eq_abs,firstOrderCoordinates_norm,le_refl]

theorem scaledFirstOrderProgress_joint_measurable (d T : ℕ) (β : ℝ) :
    Measurable (fun w : (Fin (T+1) → Fin d → Bool) × Point (FirstOrderDimension d T) =>
      firstOrderProgress w.1 (firstOrderDilation d T β w.2)) := by
  apply positiveGateFrontier_measurable
  intro i
  have hL : Measurable (firstOrderDilation d T β) := (firstOrderDilation d T β).continuous.measurable
  have hy : Measurable (fun x : Point (FirstOrderDimension d T) =>
      fun j : Fin d => (firstOrderDilation d T β x i) j) :=
    measurable_pi_iff.mpr (fun j => (EuclideanSpace.proj j).continuous.measurable.comp
      ((blockProj (E := Point d) i).continuous.measurable.comp hL))
  have hc : Measurable (fun w : (Fin (T+1) → Fin d → Bool) × Point (FirstOrderDimension d T) =>
      (w.2,w.1 i)) := measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)
  have hm := (firstOrderEncoding_joint_measurable hy).comp hc
  change Measurable (fun w : (Fin (T+1) → Fin d → Bool) × Point (FirstOrderDimension d T) =>
    firstOrderCompletion (firstOrderBlockEncoding (w.1 i) (firstOrderDilation d T β w.2 i)))
  simp only [firstOrderBlockEncoding_eq]
  exact firstOrderCompletion_contDiff.continuous.measurable.comp hm

theorem scaledFirstOrderProgress_zero (Θ : Fin (T+1) → Fin d → Bool) (β : ℝ) :
    firstOrderProgress Θ (firstOrderDilation d T β 0)=0 := by
  rw [map_zero,firstOrderProgress_zero]

end
end SecondOrder
