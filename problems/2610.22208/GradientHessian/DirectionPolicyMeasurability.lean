import GradientHessian.DirectionPolicyReplay
import GradientHessian.ControllerPolicyMeasurability
import GradientHessian.GeometricControllerMeasurability

/-! Joint measurability of actual direction-censored executions and their
original external-factor/private-seed shadows. No target coordinate is
passed to a shadow after the fixed replacement value is chosen. -/

noncomputable section
namespace GradientHessian.DirectionPolicyReplay
open Classical HigherHierarchy HierarchyAddresses RawHierarchy HierarchyParameters
  FrontierState TaskState GeometricRepair ComparisonController ComparisonControllerReplay ControllerMeasurable RawDirection

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (Ordinary d J E H t)]
  [∀ t,MeasurableSpace (Rich d J E H t)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (target : Slot J t) (stop : State (t+1) (4096*J^2+1) ell → Bool)
variable [BorelSpace (Point d J E H t)] [BorelSpace (Ordinary d J E H t)]
  [BorelSpace (Rich d J E H t)]

theorem ordinary_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : Raw d n r J E H t × Point d J E H t =>
      DirectionPolicy.ordinary K t (coefficients P B fallback t q.1) before after q.2) := by
  have hd := (DirectionPolicy.ordinary_continuous (Y := EuclideanSpace ℝ (Fin d))
    (E := E) (H := H) (m := 4096*J^2) hK t before after).borel_measurable
  have hm : @Measurable
      (Parameters (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t × Point d J E H t)
      (Ordinary d J E H t) inferInstance (borel _)
      (fun q => DirectionPolicy.ordinary K t q.1 before after q.2) :=
    hd.mono OpensMeasurableSpace.borel_le le_rfl
  have hc := hm.comp
    (((coefficients_measurable (n := n) (J := J) (E := E) (H := H) P B fallback t).comp measurable_fst).prodMk measurable_snd)
  exact hc.mono le_rfl (le_of_eq BorelSpace.measurable_eq)

theorem rich_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : Raw d n r J E H t × Point d J E H t =>
      DirectionPolicy.rich K t (coefficients P B fallback t q.1) before after q.2) := by
  have hd := (DirectionPolicy.rich_continuous (Y := EuclideanSpace ℝ (Fin d))
    (E := E) (H := H) (m := 4096*J^2) hK t before after).borel_measurable
  have hm : @Measurable
      (Parameters (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t × Point d J E H t)
      (Rich d J E H t) inferInstance (borel _)
      (fun q => DirectionPolicy.rich K t q.1 before after q.2) :=
    hd.mono OpensMeasurableSpace.borel_le le_rfl
  have hc := hm.comp
    (((coefficients_measurable (n := n) (J := J) (E := E) (H := H) P B fallback t).comp measurable_fst).prodMk measurable_snd)
  exact hc.mono le_rfl (le_of_eq BorelSpace.measurable_eq)

theorem suppressed_guard_measurable (K : ℝ) :
    Measurable (fun q : Raw d n r J E H t × Phase (t+1) (4096*J^2+1) ell
        (Point d J E H t) (Action t (4096*J^2)) =>
      guardedTick (suppress (rules K (assemble P B fallback t q.1)) (blockDirection target)) stop q.2) := by
  apply guardedTick_joint_measurable (priority t (4096*J^2)) GeometricRepair.target
    (fun raw s Z a => if blockDirection target a then false else trigger K (assemble P B fallback t raw) s Z a)
    (fun raw => hit (assemble P B fallback t raw))
  · intro s a
    cases hb : blockDirection target a with
    | true => simpa only [hb,if_true] using (measurable_const (a := false) :
        Measurable (fun _ : Raw d n r J E H t × Point d J E H t => false))
    | false => simpa only [hb,Bool.false_eq_true,if_false] using trigger_fixed_joint_measurable P B fallback t K s a
  · exact hit_fixed_joint_measurable P B fallback t

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Point d J E H t) (Ordinary d J E H t) (Rich d J E H t))

theorem run_joint_measurable {K : ℝ} (hK : 0<K) (fuel : ℕ) :
    Measurable (fun q : Raw d n r J E H t × ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
        (Point d J E H t) (Action t (4096*J^2)) => run P B fallback t policy K target stop q.1 fuel q.2) := by
  exact ControllerPolicyDriver.run_joint_measurable
    (Ω := Raw d n r J E H t) (L := t+1) (M := 4096*J^2+1) (ell := ell)
    (S := S) (A := Action t (4096*J^2)) (X := Point d J E H t) policy
    (fun raw => suppress (rules K (assemble P B fallback t raw)) (blockDirection target)) stop
    (fun raw => DirectionPolicy.ordinary K t (coefficients P B fallback t raw))
    (fun raw => DirectionPolicy.rich K t (coefficients P B fallback t raw))
    (suppressed_guard_measurable P B fallback t target stop K)
    (ordinary_fixed_measurable P B fallback t hK) (rich_fixed_measurable P B fallback t hK) fuel

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]

def shadow (e : Raw d n r J E H t ≃ᵐ V × W) (replacement : V) (K : ℝ) (rest : W) (fuel : ℕ)
    (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S (Point d J E H t) (Action t (4096*J^2))) :=
  run P B fallback t policy K target stop (e.symm (replacement,rest)) fuel q

theorem shadow_joint_measurable (e : Raw d n r J E H t ≃ᵐ V × W) (replacement : V)
    {K : ℝ} (hK : 0<K) (fuel : ℕ) :
    Measurable (fun q : W × ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
        (Point d J E H t) (Action t (4096*J^2)) =>
      shadow P B fallback t target stop policy e replacement K q.1 fuel q.2) := by
  let C := ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S (Point d J E H t) (Action t (4096*J^2))
  have hrun := run_joint_measurable (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) (ell := ell)
    P B fallback t target stop policy hK fuel
  have hmap : Measurable (fun q : W × C => (e.symm (replacement,q.1),q.2)) :=
    ((e.symm.measurable.comp (measurable_const.prodMk
      (measurable_fst : Measurable (Prod.fst : W × C → W)))).prodMk
        (measurable_snd : Measurable (Prod.snd : W × C → C)))
  simpa only [shadow,Function.comp_def] using hrun.comp hmap

theorem shadow_seed_measurable (e : Raw d n r J E H t ≃ᵐ V × W) (replacement : V)
    {K : ℝ} (hK : 0<K) (fuel N : ℕ) (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : W × Seed => shadow P B fallback t target stop policy e replacement K q.1 fuel
      (ControllerPolicyDriver.initial policy N q.2 s)) := by
  have hshadow := shadow_joint_measurable (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) (ell := ell)
    P B fallback t target stop policy e replacement hK fuel
  have hinitial := ControllerPolicyDriver.initial_measurable (A := Action t (4096*J^2)) policy N s
  have hmap : Measurable (fun q : W × Seed =>
      (q.1,ControllerPolicyDriver.initial (Action := Action t (4096*J^2)) policy N q.2 s)) :=
    (measurable_fst : Measurable (Prod.fst : W × Seed → W)).prodMk
      (hinitial.comp (measurable_snd : Measurable (Prod.snd : W × Seed → Seed)))
  simpa only [Function.comp_def] using hshadow.comp hmap

end GradientHessian.DirectionPolicyReplay
