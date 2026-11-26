import GradientHessian.GeometricRepairInventory
import GradientHessian.GeometricControllerMeasurability
import GradientHessian.ControllerTrajectoryMeasurability
import GradientHessian.ControllerRepairProbability

/-! Expected actual geometric repair charge, with all measurability and
finite action costs discharged. The per-action stopped-event probability
estimates are explicit inputs, not asserted independence conclusions. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical Matrix LowRank HigherHierarchy TaskState TaskSlots ComparisonController
  ControllerMeasurable ControllerRepairProbability MeasureTheory
open scoped BigOperators

theorem measurable_raw_pullback {Ω Ξ X V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace X] [MeasurableSpace V] (f : Ξ × X → V) (hf : Measurable f)
    (raw : Ω → Ξ) (hr : Measurable raw) :
    Measurable (fun q : Ω × X => f (raw q.1,q.2)) :=
  hf.comp ((hr.comp measurable_fst).prodMk measurable_snd)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h, MeasurableSpace (H h)] [∀ h, BorelSpace (H h)] [∀ h, FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (K : ℝ)
  [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]

theorem projected_trigger_measurable
    (raw : Ω → RawHierarchy.Raw d n r J E H t) (hraw : Measurable raw)
    (s : State (t+1) (4096*J^2+1) ell) (a : Action t (4096*J^2)) :
    Measurable (fun q : Ω × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      trigger K (RawHierarchy.assemble P B fallback t (raw q.1)) s q.2 a) :=
  measurable_raw_pullback _ (trigger_fixed_joint_measurable (n := n) (J := J) (E := E) (H := H)
    P B fallback t K s a) raw hraw

theorem projected_hit_measurable
    (raw : Ω → RawHierarchy.Raw d n r J E H t) (hraw : Measurable raw)
    (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : Ω × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      hit (RawHierarchy.assemble P B fallback t (raw q.1)) s q.2) :=
  measurable_raw_pullback _ (hit_fixed_joint_measurable (n := n) (J := J) (E := E) (H := H)
    P B fallback t s) raw hraw

theorem expected_repairs_le_families (μ : Measure Ω) [IsFiniteMeasure μ]
    (raw : Ω → RawHierarchy.Raw d n r J E H t) (hraw : Measurable raw)
    (ps : List (Ω → Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)))
    (hps : ∀ p ∈ ps, Measurable p) (s : Ω → State (t+1) (4096*J^2+1) ell)
    (hsm : Measurable s) (hs : ∀ w, Ready (s w)) (hell : 0<ell)
    (loc : Fin t → ℝ) (old inner mark : ℝ)
    (hprob : ∀ a : Action t (4096*J^2),
      μ.real (event (fun w => rules K (RawHierarchy.assemble P B fallback t (raw w)))
        (fun w => ps.map (fun p => p w)) s a) ≤ familyBound loc old inner mark a) :
    (∫ w, (count (fun w => rules K (RawHierarchy.assemble P B fallback t (raw w)))
      (fun w => ps.map (fun p => p w)) s w : ℝ) ∂μ) ≤
      (8:ℝ)^(t+1)*(4096*(J:ℝ)^2+1)*((15/8:ℝ)*(∑ h, loc h) +
        8*(FirstHeight.depth (4096*J^2+1)+2)*old +
        (4096*(J:ℝ)^2+1)*(Inner.absoluteDepth+2)*inner + (4096*(J:ℝ)^2+1)*mark) := by
  let tr := fun w => trigger (ell := ell) K (RawHierarchy.assemble P B fallback t (raw w))
  let hi := fun w => hit (ell := ell) (RawHierarchy.assemble P B fallback t (raw w))
  have htr (s : State (t+1) (4096*J^2+1) ell) (a : Action t (4096*J^2)) :
      Measurable (fun q : Ω × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
        tr q.1 s q.2 a) :=
    projected_trigger_measurable P B fallback t K raw hraw s a
  have hhi (s : State (t+1) (4096*J^2+1) ell) :
      Measurable (fun q : Ω × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
        hi q.1 s q.2) :=
    projected_hit_measurable P B fallback t raw hraw s
  have hm := repair_tally_measurable (priority t (4096*J^2)) target tr hi htr hhi ps hps s hsm
  have he := action_event_measurable (priority t (4096*J^2)) target tr hi htr hhi ps hps s hsm
  let trajectory : Ω → List (Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)) :=
    fun w => ps.map (fun p => p w)
  change Measurable (count (parameterRules (priority t (4096*J^2)) target tr hi) trajectory s) at hm
  change ∀ a, MeasurableSet (event (parameterRules (priority t (4096*J^2)) target tr hi) trajectory s a) at he
  have hb := mean_le_probability_bounds μ
    (parameterRules (priority t (4096*J^2)) target tr hi)
    trajectory s hs hell publicCost (fun _ _ => le_rfl)
    hm he (familyBound loc old inner mark) hprob
  rw [family_cost_sum] at hb
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,parameterRules,tr,hi,rules,trajectory] using hb

end GradientHessian.GeometricRepair
