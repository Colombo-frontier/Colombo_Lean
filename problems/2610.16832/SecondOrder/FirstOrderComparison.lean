import SecondOrder.CurvatureComparison
import SecondOrder.FirstOrderPrefixFrontier

open scoped Classical

namespace SecondOrder
noncomputable section

variable {d T : ℕ} {S : Type*}

abbrev FirstOrderPolicy (d T : ℕ) (S : Type*) :=
  QueryPolicy (Point (FirstOrderDimension d T)) (RichReply (FirstOrderDimension d T)) S

def firstOrderComparisonStep (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (n : ℕ) (s : ℕ × S) (z : FirstOrderCoefficients d T R) : ℕ × S :=
  let x := P.query n s.2
  let k := firstOrderLimitedProgress Θ β x (s.1+1)
  (max s.1 k,P.update n s.2 (scaledFirstOrderTruncatedReply Θ A β z k x))

/-- The comparison interaction inspects at most the next hidden block. Its
historical progress is monotone, while the chosen response index may decrease. -/
def firstOrderComparisonRun (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) : ℕ → ℕ × S
  | 0 => (0,P.initial)
  | n+1 => firstOrderComparisonStep P Θ A β n (firstOrderComparisonRun P Θ A β z n) (z n)

def firstOrderComparisonQuery (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ) : Point (FirstOrderDimension d T) :=
  P.query n (firstOrderComparisonRun P Θ A β z n).2

def firstOrderComparisonIndex (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ) : ℕ :=
  firstOrderLimitedProgress Θ β (firstOrderComparisonQuery P Θ A β z n) ((firstOrderComparisonRun P Θ A β z n).1+1)

theorem firstOrderComparisonRun_progress_succ (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ) :
    (firstOrderComparisonRun P Θ A β z (n+1)).1 =
      max (firstOrderComparisonRun P Θ A β z n).1 (firstOrderComparisonIndex P Θ A β z n) := rfl

theorem firstOrderComparisonRun_progress_le (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) :
    ∀ n, (firstOrderComparisonRun P Θ A β z n).1≤T+1 := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [firstOrderComparisonRun_progress_succ]
    exact max_le ih (firstOrderLimitedProgress_le Θ β _ _).1

theorem firstOrderComparisonRun_progress_mono (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) :
    Monotone (fun n => (firstOrderComparisonRun P Θ A β z n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [firstOrderComparisonRun_progress_succ]
  exact le_max_left _ _

theorem firstOrderComparisonRun_progress_step (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ) :
    (firstOrderComparisonRun P Θ A β z (n+1)).1≤(firstOrderComparisonRun P Θ A β z n).1+1 := by
  rw [firstOrderComparisonRun_progress_succ]
  exact max_le (Nat.le_succ _) (firstOrderLimitedProgress_le Θ β _ _).2

theorem firstOrderComparisonIndex_le_next (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ) :
    firstOrderComparisonIndex P Θ A β z n≤(firstOrderComparisonRun P Θ A β z (n+1)).1 := by
  rw [firstOrderComparisonRun_progress_succ]
  exact le_max_right _ _

def firstOrderNoFarJump (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (N : ℕ) : Prop :=
  ∀ n, n<N → ∀ i, (firstOrderComparisonRun P Θ A β z n).1+1 ≤ i.val →
    ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β (firstOrderComparisonQuery P Θ A β z n) i)

/-- On the complement of the far-jump event, the actual and comparison
interactions coincide pointwise under the same coefficient tape. -/
theorem firstOrderComparisonRun_coupling (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) :
    ∀ N, firstOrderNoFarJump P Θ A β z N →
      queryPolicyRun P (fun x a => richReply (scaledFirstOrderSample Θ A β) a x) z N =
        (firstOrderComparisonRun P Θ A β z N).2 := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro hsafe
    have hs : firstOrderNoFarJump P Θ A β z N := fun n hn => hsafe n (by omega)
    have he := ih hs
    change P.update N (queryPolicyRun P _ z N) (richReply (scaledFirstOrderSample Θ A β) (z N)
      (P.query N (queryPolicyRun P _ z N))) = _
    rw [he]
    change P.update N (firstOrderComparisonRun P Θ A β z N).2
      (richReply (scaledFirstOrderSample Θ A β) (z N) (firstOrderComparisonQuery P Θ A β z N)) =
      P.update N (firstOrderComparisonRun P Θ A β z N).2
        (scaledFirstOrderTruncatedReply Θ A β (z N) (firstOrderComparisonIndex P Θ A β z N)
          (firstOrderComparisonQuery P Θ A β z N))
    rw [firstOrderLimitedProgress_reply Θ A β (z N) _ _ (hsafe N (by omega))]
    rfl

end
end SecondOrder

