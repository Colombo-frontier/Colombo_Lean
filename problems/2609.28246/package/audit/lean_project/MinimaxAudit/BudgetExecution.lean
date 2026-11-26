import MinimaxAudit.RevisedModel
import MinimaxAudit.Deterministic

/-! Increasing a total all-history query cap leaves its true saved output
unchanged. This connects domain-dependent finite upper caps to one public
uniform complexity budget without adding any objective calls. -/
namespace MinimaxAudit
open Deterministic
section Execution
variable {p dx dy N M : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

theorem runScalarPolicy_same_decisions
    (A : DeterministicScalarPolicy p dx dy N X Y)
    (B : DeterministicScalarPolicy p dx dy M X Y)
    (hq : ∀ h, A.query h = B.query h) (ho : ∀ h, A.output h = B.output h)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (fuel : ℕ) (hist : ScalarHistory p dx dy) :
    runScalarPolicy A oracle fuel hist = runScalarPolicy B oracle fuel hist := by
  induction fuel generalizing hist with
  | zero => exact ho hist
  | succ fuel ih =>
    simp only [runScalarPolicy, hq]
    cases hb : B.query hist with
    | none => exact ho hist
    | some z => exact ih _

theorem runScalarPolicy_extra_fuel
    (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (fuel extra : ℕ) (hist : ScalarHistory p dx dy)
    (hcap : N ≤ fuel + hist.length) :
    runScalarPolicy A oracle (fuel + extra) hist = runScalarPolicy A oracle fuel hist := by
  induction fuel generalizing hist with
  | zero =>
    have hq : A.query hist = none := A.cap hist (by simpa using hcap)
    cases extra <;> simp [runScalarPolicy, hq]
  | succ fuel ih =>
    rw [Nat.succ_add]
    cases hq : A.query hist with
    | none => simp [runScalarPolicy, hq]
    | some z =>
      simp only [runScalarPolicy, hq]
      apply ih
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega

/-- The public cap enlargement has exactly the same saved output on the
actual scalar oracle. The all-history cap is used to justify the extra fuel. -/
theorem borel_monoBudget_run {B : ℕ}
    (A : BorelDeterministicScalarPolicy p dx dy N X Y) (hNB : N ≤ B)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) :
    runScalarPolicy (A.monoBudget hNB).policy oracle B [] =
      runScalarPolicy A.policy oracle N [] := by
  have hsame := runScalarPolicy_same_decisions (A.monoBudget hNB).policy A.policy
    (fun _ => rfl) (fun _ => rfl) oracle B []
  rw [hsame]
  have hf := runScalarPolicy_extra_fuel A.policy oracle N (B-N) [] (by simp)
  simpa only [Nat.add_sub_of_le hNB] using hf
end Execution
end MinimaxAudit
