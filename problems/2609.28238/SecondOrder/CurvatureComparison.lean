import SecondOrder.PrefixFrontier

open scoped Classical

namespace SecondOrder
noncomputable section

/-- A deterministic adaptive query policy. A randomized algorithm is obtained
by fixing its private seed. The final query map may represent its output. -/
structure QueryPolicy (X Y S : Type*) where
  initial : S
  query : ℕ → S → X
  update : ℕ → S → Y → S

def queryPolicyRun {X Y S A : Type*} (P : QueryPolicy X Y S) (reply : X → A → Y) (z : ℕ → A) : ℕ → S
  | 0 => P.initial
  | n+1 => P.update n (queryPolicyRun P reply z n) (reply (P.query n (queryPolicyRun P reply z n)) (z n))

variable {m T : ℕ} {S : Type*}

abbrev CurvaturePolicy (m T : ℕ) (S : Type*) :=
  QueryPolicy (Point (CurvatureDimension m T)) (RichReply (CurvatureDimension m T)) S

def curvatureComparisonStep (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (n : ℕ) (s : ℕ × S) (z : CurvatureCoefficients m T R) : ℕ × S :=
  let x := P.query n s.2
  let k := curvatureLimitedProgress Θ β x (s.1+1)
  (max s.1 k,P.update n s.2 (scaledCurvatureTruncatedReply Θ A β z k x))

/-- The comparison interaction inspects at most the next hidden block. Its
historical progress is monotone, while the chosen response index may decrease. -/
def curvatureComparisonRun (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) : ℕ → ℕ × S
  | 0 => (0,P.initial)
  | n+1 => curvatureComparisonStep P Θ A β n (curvatureComparisonRun P Θ A β z n) (z n)

def curvatureComparisonQuery (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (n : ℕ) : Point (CurvatureDimension m T) :=
  P.query n (curvatureComparisonRun P Θ A β z n).2

def curvatureComparisonIndex (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (n : ℕ) : ℕ :=
  curvatureLimitedProgress Θ β (curvatureComparisonQuery P Θ A β z n) ((curvatureComparisonRun P Θ A β z n).1+1)

theorem curvatureComparisonRun_progress_succ (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (n : ℕ) :
    (curvatureComparisonRun P Θ A β z (n+1)).1 =
      max (curvatureComparisonRun P Θ A β z n).1 (curvatureComparisonIndex P Θ A β z n) := rfl

theorem curvatureComparisonRun_progress_le (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) :
    ∀ n, (curvatureComparisonRun P Θ A β z n).1≤T+1 := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [curvatureComparisonRun_progress_succ]
    exact max_le ih (curvatureLimitedProgress_le Θ β _ _).1

theorem curvatureComparisonRun_progress_mono (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) :
    Monotone (fun n => (curvatureComparisonRun P Θ A β z n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [curvatureComparisonRun_progress_succ]
  exact le_max_left _ _

theorem curvatureComparisonRun_progress_step (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (n : ℕ) :
    (curvatureComparisonRun P Θ A β z (n+1)).1≤(curvatureComparisonRun P Θ A β z n).1+1 := by
  rw [curvatureComparisonRun_progress_succ]
  exact max_le (Nat.le_succ _) (curvatureLimitedProgress_le Θ β _ _).2

theorem curvatureComparisonIndex_le_next (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (n : ℕ) :
    curvatureComparisonIndex P Θ A β z n≤(curvatureComparisonRun P Θ A β z (n+1)).1 := by
  rw [curvatureComparisonRun_progress_succ]
  exact le_max_right _ _

def curvatureNoFarJump (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (N : ℕ) : Prop :=
  ∀ n, n<N → ∀ i, (curvatureComparisonRun P Θ A β z n).1+1 ≤ i.val →
    ¬0<periodicCompletion (Θ i) (curvatureDilation m T β (curvatureComparisonQuery P Θ A β z n) i)

/-- On the complement of the far-jump event, the actual and comparison
interactions coincide pointwise under the same coefficient tape. -/
theorem curvatureComparisonRun_coupling (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) :
    ∀ N, curvatureNoFarJump P Θ A β z N →
      queryPolicyRun P (fun x a => richReply (scaledCurvatureSample Θ A β) a x) z N =
        (curvatureComparisonRun P Θ A β z N).2 := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro hsafe
    have hs : curvatureNoFarJump P Θ A β z N := fun n hn => hsafe n (by omega)
    have he := ih hs
    change P.update N (queryPolicyRun P _ z N) (richReply (scaledCurvatureSample Θ A β) (z N)
      (P.query N (queryPolicyRun P _ z N))) = _
    rw [he]
    change P.update N (curvatureComparisonRun P Θ A β z N).2
      (richReply (scaledCurvatureSample Θ A β) (z N) (curvatureComparisonQuery P Θ A β z N)) =
      P.update N (curvatureComparisonRun P Θ A β z N).2
        (scaledCurvatureTruncatedReply Θ A β (z N) (curvatureComparisonIndex P Θ A β z N)
          (curvatureComparisonQuery P Θ A β z N))
    rw [curvatureLimitedProgress_reply Θ A β (z N) _ _ (hsafe N (by omega))]
    rfl

end
end SecondOrder
