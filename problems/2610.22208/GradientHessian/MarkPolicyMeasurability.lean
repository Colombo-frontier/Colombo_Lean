import GradientHessian.MarkPolicyReplay
import GradientHessian.ControllerPolicyMeasurability
import GradientHessian.GeometricControllerMeasurability

/-! Joint measurability of the actual future-mark shadow, including an
arbitrary private seed and policy state. The external factor coordinate is
the original presampled raw law's coordinate, not independent advice. -/

noncomputable section
namespace GradientHessian.MarkPolicyReplay
open Classical HigherHierarchy HierarchyAddresses RawHierarchy HierarchyParameters
open FrontierState TaskState GeometricRepair ComparisonController ComparisonControllerReplay ControllerMeasurable

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (targetLeaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
variable [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
  (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
    Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
  (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
    Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]

theorem ordinary_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      ordinary P B fallback t K q.1 before after q.2) :=
  (CensoredPolicy.ordinaryReply_continuous hK t before after).measurable.comp
    (((coefficients_measurable P B fallback t).comp measurable_fst).prodMk measurable_snd)

theorem rich_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      rich P B fallback t K q.1 before after q.2) :=
  (CensoredPolicy.richReply_continuous hK t before after).measurable.comp
    (((coefficients_measurable P B fallback t).comp measurable_fst).prodMk measurable_snd)

theorem suppressed_guard_measurable (K : ℝ) :
    Measurable (fun q : Raw d n r J E H t × Phase (t+1) (4096*J^2+1) ell
        (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
      guardedTick (suppress (rules K (assemble P B fallback t q.1)) (blockMark targetLeaf j))
        (markSupplied targetLeaf j) q.2) := by
  apply guardedTick_joint_measurable (priority t (4096*J^2)) GeometricRepair.target
    (fun raw s Z a => if blockMark targetLeaf j a then false else trigger K (assemble P B fallback t raw) s Z a)
    (fun raw => hit (assemble P B fallback t raw))
  · intro s a
    cases hb : blockMark targetLeaf j a with
    | true => simpa only [hb,if_true] using (measurable_const (a := false) : Measurable (fun _ :
        Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => false))
    | false => simpa only [hb,Bool.false_eq_true,if_false] using trigger_fixed_joint_measurable P B fallback t K s a
  · exact hit_fixed_joint_measurable P B fallback t

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

theorem run_joint_measurable {K : ℝ} (hK : 0<K) (fuel : ℕ) :
    Measurable (fun q : Raw d n r J E H t × ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
        (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
      run P B fallback t targetLeaf j policy K q.1 fuel q.2) := by
  exact ControllerPolicyDriver.run_joint_measurable
    (Ω := Raw d n r J E H t) (L := t+1) (M := 4096*J^2+1) (ell := ell)
    (S := S) (A := Action t (4096*J^2))
    (X := Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) policy
    (fun raw => suppress (rules K (assemble P B fallback t raw)) (blockMark targetLeaf j))
    (markSupplied targetLeaf j) (ordinary P B fallback t K) (rich P B fallback t K)
    (suppressed_guard_measurable P B fallback t targetLeaf j K)
    (ordinary_fixed_measurable P B fallback t hK) (rich_fixed_measurable P B fallback t hK) fuel

theorem shadow_joint_measurable {K : ℝ} (hK : 0<K) (fuel : ℕ) :
    Measurable (fun q : RawMarkFactor.Rest d n r J E H t ×
        ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
          (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
      shadow (n := n) (E := E) (H := H) (ell := ell) P B fallback t targetLeaf j policy K q.1 fuel q.2) := by
  let C := ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))
  let e : Raw d n r J E H t ≃ᵐ EuclideanSpace ℝ (Fin r) × RawMarkFactor.Rest d n r J E H t :=
    RawMarkFactor.factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H)
      t ((leafEquiv t).symm targetLeaf) j
  have hrun := run_joint_measurable (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) (ell := ell)
    P B fallback t targetLeaf j policy hK fuel
  have hmap : Measurable (fun q : RawMarkFactor.Rest d n r J E H t × C =>
      (e.symm (0,q.1),q.2)) :=
    ((e.symm.measurable.comp
      (measurable_const.prodMk (measurable_fst : Measurable (Prod.fst : RawMarkFactor.Rest d n r J E H t × C → _)))).prodMk
        (measurable_snd : Measurable (Prod.snd : RawMarkFactor.Rest d n r J E H t × C → C)))
  simpa only [shadow,e,Function.comp_def] using hrun.comp hmap

theorem shadow_seed_measurable {K : ℝ} (hK : 0<K) (fuel N : ℕ)
    (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : RawMarkFactor.Rest d n r J E H t × Seed =>
      shadow (n := n) (E := E) (H := H) (ell := ell) P B fallback t targetLeaf j policy K q.1 fuel
        (ControllerPolicyDriver.initial policy N q.2 s)) := by
  have hshadow := shadow_joint_measurable (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) (ell := ell)
    P B fallback t targetLeaf j policy hK fuel
  have hinitial := ControllerPolicyDriver.initial_measurable (A := Action t (4096*J^2)) policy N s
  have hmap : Measurable (fun q : RawMarkFactor.Rest d n r J E H t × Seed =>
      (q.1,ControllerPolicyDriver.initial (Action := Action t (4096*J^2)) policy N q.2 s)) :=
    (measurable_fst : Measurable (Prod.fst : RawMarkFactor.Rest d n r J E H t × Seed → _)).prodMk
      (hinitial.comp (measurable_snd : Measurable (Prod.snd : RawMarkFactor.Rest d n r J E H t × Seed → Seed)))
  simpa only [Function.comp_def] using hshadow.comp hmap

end GradientHessian.MarkPolicyReplay
