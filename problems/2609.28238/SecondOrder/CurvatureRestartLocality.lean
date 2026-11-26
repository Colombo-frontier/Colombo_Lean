import SecondOrder.CurvatureEntryDisintegration

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

theorem curvatureRestartRun_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start p : ℕ) (s₀ : S) {R : ℝ}
    (z z' : ℕ → CurvatureCoefficients m T R) (n : ℕ)
    (hz : ∀ t, t<n → z t=z' t) :
    curvatureRestartRun P Θ A β start p s₀ z n=curvatureRestartRun P Θ A β start p s₀ z' n :=
  stateTapeRun_tape_congr _ _ z z' n hz

theorem curvatureRestartIndex_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start p : ℕ) (s₀ : S) {R : ℝ}
    (z z' : ℕ → CurvatureCoefficients m T R) (n : ℕ)
    (hz : ∀ t, t<n → z t=z' t) :
    curvatureRestartIndex P Θ A β start p s₀ z n=curvatureRestartIndex P Θ A β start p s₀ z' n := by
  unfold curvatureRestartIndex
  rw [curvatureRestartRun_tape_congr P Θ A β start p s₀ z z' n hz]

theorem curvatureRestartCount_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start p stage : ℕ) (s₀ : S) {R : ℝ}
    (z z' : ℕ → CurvatureCoefficients m T R) : ∀ n,
    (∀ t, t<n → z t=z' t) →
    curvatureRestartCount P Θ A β start p stage s₀ z n=
      curvatureRestartCount P Θ A β start p stage s₀ z' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hz
    have hn : ∀ t, t<n → z t=z' t := fun t ht => hz t (by omega)
    rw [curvatureRestartCount, curvatureRestartCount, ih hn,
      curvatureRestartIndex_tape_congr P Θ A β start p s₀ z z' n hn]

def curvatureRestartActive (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (s₀ : S) {R : ℝ}
    (n : ℕ) (z : ℕ → CurvatureCoefficients m T R) : Prop :=
  0<periodicCompletion (Θ i) (curvatureDilation m T β
    (P.query (start+n) (curvatureRestartRun P Θ A β start p s₀ z n).2) i)

def curvatureRestartExit (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (n : ℕ) (z : ℕ → CurvatureCoefficients m T R) : Prop :=
  curvatureRestartActive P Θ A β start p i s₀ n z ∨
    cap≤curvatureRestartCount P Θ A β start p i.val s₀ z n

def curvatureRestartFast (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (n : ℕ) (z : ℕ → CurvatureCoefficients m T R) : Prop :=
  curvatureRestartActive P Θ A β start p i s₀ n z ∧
    curvatureRestartCount P Θ A β start p i.val s₀ z n<cap

theorem curvatureRestartActive_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (s₀ : S) {R : ℝ}
    (n : ℕ) (z z' : ℕ → CurvatureCoefficients m T R) (hz : ∀ t, t<n → z t=z' t) :
    curvatureRestartActive P Θ A β start p i s₀ n z ↔
      curvatureRestartActive P Θ A β start p i s₀ n z' := by
  unfold curvatureRestartActive
  rw [curvatureRestartRun_tape_congr P Θ A β start p s₀ z z' n hz]

theorem curvatureRestartExit_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (n : ℕ) (z z' : ℕ → CurvatureCoefficients m T R) (hz : ∀ t, t<n → z t=z' t) :
    curvatureRestartExit P Θ A β start p i cap s₀ n z ↔
      curvatureRestartExit P Θ A β start p i cap s₀ n z' := by
  unfold curvatureRestartExit
  rw [curvatureRestartActive_tape_congr P Θ A β start p i s₀ n z z' hz,
    curvatureRestartCount_tape_congr P Θ A β start p i.val s₀ z z' n hz]

theorem curvatureRestartFast_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (n : ℕ) (z z' : ℕ → CurvatureCoefficients m T R) (hz : ∀ t, t<n → z t=z' t) :
    curvatureRestartFast P Θ A β start p i cap s₀ n z ↔
      curvatureRestartFast P Θ A β start p i cap s₀ n z' := by
  unfold curvatureRestartFast
  rw [curvatureRestartActive_tape_congr P Θ A β start p i s₀ n z z' hz,
    curvatureRestartCount_tape_congr P Θ A β start p i.val s₀ z z' n hz]

end
end SecondOrder
