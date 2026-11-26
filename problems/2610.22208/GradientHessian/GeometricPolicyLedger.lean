import GradientHessian.ControllerPolicyTrace
import GradientHessian.GeometricSuccessRetirement

/-! The actual policy-selected trace and its virtual output satisfy the
task ledger on a small-gradient output. Success-to-retirement and the two
resource comparisons are proved from the geometric controller and policy
definitions, with no assumed ledger or decoder-agreement premise. -/

noncomputable section
namespace GradientHessian.GeometricPolicyLedger
open Classical FrontierState TaskState TaskSlots ComparisonController
  ComparisonControllerLedger GeometricDisclosure GeometricRepair HigherHierarchy
  VisibilityWindow ControllerPolicyTrace Machine

theorem controller_run_append {L M ell : ℕ} {X A : Type*} (R : Rules L M ell X A)
    (ps qs : List (Pending X)) (s : State L M ell) :
    VisibilityWindow.run R (ps++qs) s=VisibilityWindow.run R qs (VisibilityWindow.run R ps s) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => exact ih (serve R p s).afterNormal

universe u
variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

theorem run_lastChildClosed (K : ℝ) (data : Data Y E H m t)
    (ps : List (Pending (Space Y E H m t))) (s : State (t+1) (m+1) ell)
    (hs : LastChildClosed (TaskState.retired s)) :
    LastChildClosed (TaskState.retired (VisibilityWindow.run (rules (ell := ell) K data) ps s)) := by
  induction ps generalizing s with
  | nil => exact hs
  | cons p ps ih => exact ih _ (serve_lastChildClosed K data p s hs).2

variable [CompleteSpace Y] [CompleteSpace E] [∀ h, CompleteSpace (H h)]
variable {Seed S O V : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
  [MeasurableSpace (Space Y E H m t)] [MeasurableSpace O] [MeasurableSpace V]

theorem output_retired {K : ℝ} (hK : 16≤K) (data : Data Y E H m t) (hd : Valid Y E H m t data)
    (P : Policy Seed S (Space Y E H m t) O V) (o : Space Y E H m t → O) (r : Space Y E H m t → V)
    (n : ℕ) (seed : Seed)
    (hg : ‖gradient (HigherHierarchy.scalar K t data) (P.output (P.run o r n seed))‖≤1) :
    TaskState.retired (VisibilityWindow.run (rules (ell := ell) K data)
      (withOutput P o r n seed) initial)=Finset.univ := by
  unfold withOutput
  rw [controller_run_append]
  change TaskState.retired (serve (rules (ell := ell) K data) ⟨P.output (P.run o r n seed),.ordinary⟩
    (VisibilityWindow.run (rules (ell := ell) K data) (trace P o r n seed) initial)).afterNormal=Finset.univ
  apply serve_small_gradient_after_retired hK data hd _ _ _ hg
  exact run_lastChildClosed K data _ _ (initial_lastChildClosed (by omega))

theorem policy_task_ledger {K : ℝ} (hK : 16≤K) (data : Data Y E H m t) (hd : Valid Y E H m t data)
    (P : Policy Seed S (Space Y E H m t) O V) (o : Space Y E H m t → O) (r : Space Y E H m t → V)
    (n : ℕ) (seed : Seed) (hell : 0<ell)
    (hg : ‖gradient (HigherHierarchy.scalar K t data) (P.output (P.run o r n seed))‖≤1) :
    8^(t+1)*(m+1)≤P.richCount o r n seed*(m+1)+(P.ordinaryCount o r n seed+1)/ell+
      tally (rules (ell := ell) K data) (early (rules (ell := ell) K data)) (withOutput P o r n seed) initial+
      tally (rules (ell := ell) K data) (repairs (rules (ell := ell) K data)) (withOutput P o r n seed) initial :=
  output_task_ledger P o r (rules (ell := ell) K data) n seed hell (output_retired hK data hd P o r n seed hg)

theorem policy_capped_ledger {K : ℝ} (hK : 16≤K) (data : Data Y E H m t) (hd : Valid Y E H m t data)
    (P : Policy Seed S (Space Y E H m t) O V) (o : Space Y E H m t → O) (r : Space Y E H m t → V)
    (n : ℕ) (seed : Seed) (hell : 0<ell) (G Hcap : ℕ) (hcaps : P.HasCaps o r G Hcap)
    (hg : ‖gradient (HigherHierarchy.scalar K t data) (P.output (P.run o r n seed))‖≤1) :
    8^(t+1)*(m+1)≤Hcap*(m+1)+(G+1)/ell+
      tally (rules (ell := ell) K data) (early (rules (ell := ell) K data)) (withOutput P o r n seed) initial+
      tally (rules (ell := ell) K data) (repairs (rules (ell := ell) K data)) (withOutput P o r n seed) initial := by
  have hb := policy_task_ledger hK data hd P o r n seed hell hg
  have hh := Nat.mul_le_mul_right (m+1) (hcaps seed n).2
  have ho : (P.ordinaryCount o r n seed+1)/ell ≤ (G+1)/ell := Nat.div_le_div_right (Nat.add_le_add_right (hcaps seed n).1 1)
  omega

end GradientHessian.GeometricPolicyLedger
