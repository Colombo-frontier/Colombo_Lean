import GradientHessian.AugmentedDisclosure
import GradientHessian.GeometricRepairMeasurability
import GradientHessian.RawFactorCoefficients

/-! Joint raw-data/state measurability of the full public comparison view.
No good-event or unit-vector assumption is used. -/

noncomputable section
namespace GradientHessian.AugmentedDisclosure
open Classical HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState
  GeometricRepair GeometricDisclosure ControllerMeasurable Matrix LowRank

universe u
variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

instance directionMeasurable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
    (a : Action t m) : MeasurableSpace (DirectionValue E H t m a) := by
  cases a <;> dsimp [DirectionValue] <;> infer_instance

instance viewMeasurable [MeasurableSpace Y] [MeasurableSpace E] [∀ h,MeasurableSpace (H h)] :
    MeasurableSpace (View Y E H t m ell) := by
  letI : MeasurableSpace (Y →L[ℝ] Y) := borel _
  unfold View
  infer_instance

end GradientHessian.AugmentedDisclosure

namespace GradientHessian.AugmentedDisclosure
open Classical HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState
  GeometricRepair GeometricDisclosure ControllerMeasurable Matrix LowRank

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) (t : ℕ)

theorem raw_matrix_measurable (leaf : Leaf (t+1)) :
    @Measurable (Raw d n r J E H t) (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      inferInstance (borel _) (fun raw => (leafCoefficients (assemble P B fallback t raw) leaf).A) := by
  simp only [leafCoefficients,RawLeafFactor.leaf_A_assemble]
  have hm : @Measurable (Matrix (Fin d) (Fin d) ℝ)
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) inferInstance (borel _) matrixEuclideanMap :=
    (continuous_matrixEuclideanMap d d).borel_measurable.mono OpensMeasurableSpace.borel_le le_rfl
  exact hm.comp
    ((ReadoutMeasurability.sourceMatrix_measurable P J).comp
      (measurable_fst.comp (RawLeafFactor.leafNumerical_measurable (d := d) (n := n) (r := r) (J := J)
        (E := E) (H := H) t ((leafEquiv t).symm leaf))))

theorem raw_mark_measurable (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1)) :
    Measurable (fun raw : Raw d n r J E H t => (leafCoefficients (assemble P B fallback t raw) leaf).b j) := by
  simp only [leafCoefficients,RawLeafFactor.leaf_b_assemble]
  exact measurable_const.smul ((matrixEuclideanMap B).continuous.measurable.comp
    ((measurable_pi_apply j).comp (measurable_snd.comp
      (RawLeafFactor.leafNumerical_measurable (d := d) (n := n) (r := r) (J := J)
        (E := E) (H := H) t ((leafEquiv t).symm leaf)))))

theorem raw_direction_measurable (K : ℝ) (a : Action t (4096*J^2)) :
    Measurable (fun raw : Raw d n r J E H t => direction K (assemble P B fallback t raw) a) := by
  cases a with
  | localized h w i => exact raw_localCenter_measurable P B fallback K t h w i
  | old w i j => exact raw_oldDirection_measurable (E := E) (H := H) P B fallback t w i j
  | inner leaf j k => exact raw_leafDirection_measurable (E := E) (H := H) P B fallback t ((leafEquiv t).symm leaf) j k
  | futureMark leaf j => exact measurable_const

theorem view_fixed_measurable (K : ℝ) (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun raw : Raw d n r J E H t => view K (assemble P B fallback t raw) s) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := borel _
  change Measurable (fun raw : Raw d n r J E H t =>
    (s,matrix (assemble P B fallback t raw) s,mark (assemble P B fallback t raw) s,
      readout (assemble P B fallback t raw) s,completion K (assemble P B fallback t raw) s))
  apply measurable_const.prodMk
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro leaf
    by_cases h : leaf∈TaskState.retired s
    · simpa only [matrix,if_pos h] using raw_matrix_measurable P B fallback t leaf
    · simp only [matrix,if_neg h]; exact measurable_const
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro leaf
    apply measurable_pi_lambda
    intro j
    by_cases h : MarkSupplied s leaf j
    · simpa only [mark,if_pos h] using raw_mark_measurable P B fallback t leaf j
    · simp only [mark,if_neg h]; exact measurable_const
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro leaf
    apply measurable_pi_lambda
    intro j
    by_cases h : TaskDisclosed s leaf j
    · simpa only [readout,if_pos h,leafCoefficients] using
        raw_leafReadout_measurable P B fallback t ((leafEquiv t).symm leaf) j
    · simp only [readout,if_neg h]; exact measurable_const
  · apply measurable_pi_lambda
    intro a
    by_cases h : directionDisclosed s a
    · simpa only [completion,if_pos h] using raw_direction_measurable P B fallback t K a
    · simp only [completion,if_neg h]; exact measurable_const

theorem view_joint_measurable (K : ℝ) :
    Measurable (fun q : Raw d n r J E H t × State (t+1) (4096*J^2+1) ell =>
      view K (assemble P B fallback t q.1) q.2) :=
  measurable_from_prod_countable (view_fixed_measurable P B fallback t K)

end GradientHessian.AugmentedDisclosure
