import GradientHessian.GeometricRepairRules
import GradientHessian.RawHierarchyMeasurability
import GradientHessian.HierarchyAddressLaws
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! Joint raw-coefficient/physical-point measurability of every literal
geometric test, including the normalized readout at its exceptional inputs. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical Matrix LowRank HigherHierarchy HierarchyAddresses
open scoped InnerProductSpace

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h, MeasurableSpace (H h)] [∀ h, BorelSpace (H h)] [∀ h, FiniteDimensional ℝ (H h)]

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem raw_localCenter_measurable (K : ℝ) (t : ℕ) (h : Fin t)
    (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8) :
    Measurable (fun x : RawHierarchy.Raw d n r J E H t =>
      localCenter K (RawHierarchy.assemble P B fallback t x) h path i) := by
  have ha := rawAtHeight_measurable (d := d) (n := n) (r := r) (J := J)
    (E := E) (H := H) t (h.val+1) (Nat.succ_le_of_lt h.isLt) path
  have hv := (measurable_pi_apply i).comp (measurable_snd.comp ha)
  have hc := (measurable_const : Measurable (fun _ : RawHierarchy.Raw d n r J E H t =>
    radius (4096*J^2) K h.val)).smul hv
  convert hc using 1
  funext x
  simp only [localCenter,dataAtHeight_assemble]
  rfl

theorem raw_oldDirection_measurable (t : ℕ) (path : Fin t → Fin 8) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    Measurable (fun x : RawHierarchy.Raw d n r J E H t =>
      oldDirection (RawHierarchy.assemble P B fallback t x) path i j) := by
  have ha := rawAtHeight_measurable (d := d) (n := n) (r := r) (J := J)
    (E := E) (H := H) t 0 (Nat.zero_le t) path
  have he : (fun x : RawHierarchy.Raw d n r J E H t =>
      oldDirection (RawHierarchy.assemble P B fallback t x) path i j) =
      (fun x => (rawAtHeight t 0 (Nat.zero_le t) path x).2.2.2 i j) := by
    funext x
    simp only [oldDirection,oldData,dataAtHeight_assemble]
    rfl
  rw [he]
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp ha))))

theorem raw_leafDirection_measurable : ∀ (t : ℕ) (i : LeafSlot t)
    (task : Fin (4096*J^2+1)) (j : Fin (Inner.absoluteDepth+2)),
    Measurable (fun x : RawHierarchy.Raw d n r J E H t =>
      (leafData t (RawHierarchy.assemble P B fallback t x) i).v task j)
  | 0,i,task,j => by
    change Measurable (fun x : RawHierarchy.Raw d n r J E H 0 => x.2.2.1 i task j)
    fun_prop
  | t+1,i,task,j => by
    change Measurable (fun x : RawHierarchy.Raw d n r J E H (t+1) =>
      (leafData t (RawHierarchy.assemble P B fallback t (x.1 i.1)) i.2).v task j)
    exact (raw_leafDirection_measurable t i.2 task j).comp (by fun_prop)

theorem raw_leafReadout_measurable : ∀ (t : ℕ) (i : LeafSlot t) (task : Fin (4096*J^2+1)),
    Measurable (fun x : RawHierarchy.Raw d n r J E H t =>
      (leafData t (RawHierarchy.assemble P B fallback t x) i).a task)
  | 0,i,task => by
    apply RawHierarchy.readoutVector_measurable P fallback (by fun_prop)
    exact (matrixEuclideanMap B).continuous.measurable.comp (by fun_prop)
  | t+1,i,task => by
    change Measurable (fun x : RawHierarchy.Raw d n r J E H (t+1) =>
      (leafData t (RawHierarchy.assemble P B fallback t (x.1 i.1)) i.2).a task)
    exact (raw_leafReadout_measurable t i.2 task).comp (by fun_prop)

variable (t : ℕ)
  [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]

theorem localDistance_joint_measurable (K : ℝ) (h : Fin t)
    (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8) :
    Measurable (fun p : RawHierarchy.Raw d n r J E H t ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      ‖localProjection h i p.2-localCenter K (RawHierarchy.assemble P B fallback t p.1) h path i‖) :=
  (((localProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) h i).continuous.measurable.comp measurable_snd).sub
    ((raw_localCenter_measurable P B fallback K t h path i).comp measurable_fst)).norm

theorem oldReadout_joint_measurable (path : Fin t → Fin 8) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    Measurable (fun p : RawHierarchy.Raw d n r J E H t ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      oldReadout (RawHierarchy.assemble P B fallback t p.1) path i j p.2) := by
  have hu : Continuous (fun q : E × E =>
      LatchChain.u (Inner.radius (FirstHeight.depth (4096*J^2+1)) j) q.1 q.2) :=
    (JointMarkedCalculus.readout_contDiff _ contDiff_fst contDiff_snd).continuous
  exact hu.measurable.comp (((raw_oldDirection_measurable P B fallback t path i j).comp measurable_fst).prodMk
    ((oldRegisterProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) t i j).continuous.measurable.comp measurable_snd))

theorem innerReadout_joint_measurable (leaf : FrontierState.Leaf (t+1))
    (task : Fin (4096*J^2+1)) (j : Fin (Inner.absoluteDepth+2)) :
    Measurable (fun p : RawHierarchy.Raw d n r J E H t ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      innerReadout (RawHierarchy.assemble P B fallback t p.1) leaf task j p.2) := by
  have hu : Continuous (fun q : E × E => LatchChain.u (Inner.radius Inner.absoluteDepth j) q.1 q.2) :=
    (JointMarkedCalculus.readout_contDiff _ contDiff_fst contDiff_snd).continuous
  exact hu.measurable.comp (((raw_leafDirection_measurable P B fallback t (leafEquiv t |>.symm leaf) task j).comp
    measurable_fst).prodMk ((innerRegisterProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) t task j).continuous.measurable.comp measurable_snd))

theorem markReadout_joint_measurable (leaf : FrontierState.Leaf (t+1)) (task : Fin (4096*J^2+1)) :
    Measurable (fun p : RawHierarchy.Raw d n r J E H t ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      markReadout (RawHierarchy.assemble P B fallback t p.1) leaf task p.2) := by
  unfold markReadout leafCoefficients
  apply Measurable.inner
  · exact (raw_leafReadout_measurable (n := n) (E := E) (H := H) P B fallback t
      ((leafEquiv t).symm leaf) task).comp measurable_fst
  · exact BoundedNumericalTest.test_contDiff.continuous.measurable.comp
      ((HierarchyAddresses.numericalProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E)
        (H := H) (m := 4096*J^2) t).continuous.measurable.comp measurable_snd)

end GradientHessian.GeometricRepair

