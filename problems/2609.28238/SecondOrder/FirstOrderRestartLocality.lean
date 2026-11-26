import SecondOrder.FirstOrderEntryDisintegration

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderRestartRun_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (s₀ : S) {R : ℝ}
    (z z' : ℕ → FirstOrderCoefficients d T R) (n : ℕ)
    (hz : ∀ t, t<n → z t=z' t) :
    firstOrderRestartRun P Θ A β start p s₀ z n=firstOrderRestartRun P Θ A β start p s₀ z' n :=
  stateTapeRun_tape_congr _ _ z z' n hz

theorem firstOrderRestartIndex_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (s₀ : S) {R : ℝ}
    (z z' : ℕ → FirstOrderCoefficients d T R) (n : ℕ)
    (hz : ∀ t, t<n → z t=z' t) :
    firstOrderRestartIndex P Θ A β start p s₀ z n=firstOrderRestartIndex P Θ A β start p s₀ z' n := by
  unfold firstOrderRestartIndex
  rw [firstOrderRestartRun_tape_congr P Θ A β start p s₀ z z' n hz]

theorem firstOrderRestartCount_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p stage : ℕ) (s₀ : S) {R : ℝ}
    (z z' : ℕ → FirstOrderCoefficients d T R) : ∀ n,
    (∀ t, t<n → z t=z' t) →
    firstOrderRestartCount P Θ A β start p stage s₀ z n=
      firstOrderRestartCount P Θ A β start p stage s₀ z' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hz
    have hn : ∀ t, t<n → z t=z' t := fun t ht => hz t (by omega)
    rw [firstOrderRestartCount, firstOrderRestartCount, ih hn,
      firstOrderRestartIndex_tape_congr P Θ A β start p s₀ z z' n hn]

def firstOrderRestartActive (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (s₀ : S) {R : ℝ}
    (n : ℕ) (z : ℕ → FirstOrderCoefficients d T R) : Prop :=
  0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β
    (P.query (start+n) (firstOrderRestartRun P Θ A β start p s₀ z n).2) i)

def firstOrderRestartExit (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (n : ℕ) (z : ℕ → FirstOrderCoefficients d T R) : Prop :=
  firstOrderRestartActive P Θ A β start p i s₀ n z ∨
    cap≤firstOrderRestartCount P Θ A β start p i.val s₀ z n

def firstOrderRestartFast (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (n : ℕ) (z : ℕ → FirstOrderCoefficients d T R) : Prop :=
  firstOrderRestartActive P Θ A β start p i s₀ n z ∧
    firstOrderRestartCount P Θ A β start p i.val s₀ z n<cap

theorem firstOrderRestartActive_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (s₀ : S) {R : ℝ}
    (n : ℕ) (z z' : ℕ → FirstOrderCoefficients d T R) (hz : ∀ t, t<n → z t=z' t) :
    firstOrderRestartActive P Θ A β start p i s₀ n z ↔
      firstOrderRestartActive P Θ A β start p i s₀ n z' := by
  unfold firstOrderRestartActive
  rw [firstOrderRestartRun_tape_congr P Θ A β start p s₀ z z' n hz]

theorem firstOrderRestartExit_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (n : ℕ) (z z' : ℕ → FirstOrderCoefficients d T R) (hz : ∀ t, t<n → z t=z' t) :
    firstOrderRestartExit P Θ A β start p i cap s₀ n z ↔
      firstOrderRestartExit P Θ A β start p i cap s₀ n z' := by
  unfold firstOrderRestartExit
  rw [firstOrderRestartActive_tape_congr P Θ A β start p i s₀ n z z' hz,
    firstOrderRestartCount_tape_congr P Θ A β start p i.val s₀ z z' n hz]

theorem firstOrderRestartFast_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (n : ℕ) (z z' : ℕ → FirstOrderCoefficients d T R) (hz : ∀ t, t<n → z t=z' t) :
    firstOrderRestartFast P Θ A β start p i cap s₀ n z ↔
      firstOrderRestartFast P Θ A β start p i cap s₀ n z' := by
  unfold firstOrderRestartFast
  rw [firstOrderRestartActive_tape_congr P Θ A β start p i s₀ n z z' hz,
    firstOrderRestartCount_tape_congr P Θ A β start p i.val s₀ z z' n hz]

end
end SecondOrder
