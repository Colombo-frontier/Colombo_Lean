import SecondOrder.FirstOrderContinuationAgreement

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderRestartRun (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start p : ℕ) (s₀ : S) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) : ℕ → ℕ × S :=
  stateTapeRun (p,s₀) (fun t => firstOrderComparisonStep P Θ A β (start+t)) z

def firstOrderRestartIndex (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start p : ℕ) (s₀ : S) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (t : ℕ) : ℕ :=
  let s := firstOrderRestartRun P Θ A β start p s₀ z t
  firstOrderLimitedProgress Θ β (P.query (start+t) s.2) (s.1+1)

def firstOrderRestartCount (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start p stage : ℕ) (s₀ : S) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) : ℕ → ℕ
  | 0 => 0
  | n+1 => firstOrderRestartCount P Θ A β start p stage s₀ z n+
      if firstOrderRestartIndex P Θ A β start p s₀ z n=stage then 1 else 0

theorem firstOrderRestartCount_mono (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start p stage : ℕ) (s₀ : S) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) :
    Monotone (firstOrderRestartCount P Θ A β start p stage s₀ z) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [firstOrderRestartCount]
  exact Nat.le_add_right _ _

/-- Up to a target's first activation, fewer than cap actual stage responses
force exact equality with the capped continuation, including response counts. -/
theorem firstOrderContinuation_coupling (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (hp : p+1=i.val ∨ p=i.val) :
    ∀ n, (∀ t, t<n → ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β
        (P.query (start+t) (firstOrderRestartRun P Θ A β start p s₀ z t).2) i)) →
      firstOrderRestartCount P Θ A β start p i.val s₀ z n<cap →
      ((firstOrderRestartRun P Θ A β start p s₀ z n).1+1=i.val ∨
        (firstOrderRestartRun P Θ A β start p s₀ z n).1=i.val) ∧
      (firstOrderRestartRun P Θ A β start p s₀ z n).2=
        (stateTapeRun (0,s₀) (firstOrderContinuationStep P Θ A β start i.val cap dummy) z n).2 ∧
      (stateTapeRun (0,s₀) (firstOrderContinuationStep P Θ A β start i.val cap dummy) z n).1=
        firstOrderRestartCount P Θ A β start p i.val s₀ z n := by
  intro n
  induction n with
  | zero => intro _ _; exact ⟨hp,rfl,rfl⟩
  | succ n ih =>
    intro hi hc
    have hcount : firstOrderRestartCount P Θ A β start p i.val s₀ z n<cap :=
      lt_of_le_of_lt (firstOrderRestartCount_mono P Θ A β start p i.val s₀ z (Nat.le_succ n)) hc
    obtain ⟨hp',hs',hc'⟩ := ih (fun t ht => hi t (by omega)) hcount
    have hn := hi n (by omega)
    have hcap : (stateTapeRun (0,s₀) (firstOrderContinuationStep P Θ A β start i.val cap dummy) z n).1<cap := by
      rw [hc']; exact hcount
    have hr : firstOrderRestartRun P Θ A β start p s₀ z (n+1)=
        firstOrderComparisonStep P Θ A β (start+n) (firstOrderRestartRun P Θ A β start p s₀ z n) (z n) := rfl
    refine ⟨?_,?_,?_⟩
    · rw [hr]
      exact firstOrderComparisonStep_before_target P Θ A β (start+n) i (z n) _ _ hp' hn
    · rw [hr, stateTapeRun]
      have hh := firstOrderContinuationStep_agree P Θ A β start n i cap dummy (z n)
        (firstOrderRestartRun P Θ A β start p s₀ z n).2
        (firstOrderRestartRun P Θ A β start p s₀ z n).1
        (stateTapeRun (0,s₀) (firstOrderContinuationStep P Θ A β start i.val cap dummy) z n).1 hp' hcap hn
      have hstate : ((stateTapeRun (0,s₀) (firstOrderContinuationStep P Θ A β start i.val cap dummy) z n).1,
          (firstOrderRestartRun P Θ A β start p s₀ z n).2)=
          stateTapeRun (0,s₀) (firstOrderContinuationStep P Θ A β start i.val cap dummy) z n := by
        rw [hs']
      rw [hstate] at hh
      exact hh
    · rw [stateTapeRun, firstOrderContinuationStep_count, firstOrderRestartCount]
      have hk := firstOrderLimitedProgress_stage_agree Θ β
        (P.query (start+n) (firstOrderRestartRun P Θ A β start p s₀ z n).2) i
        (firstOrderRestartRun P Θ A β start p s₀ z n).1 hp' hn
      unfold firstOrderRestartIndex
      dsimp only
      rw [hk, hs', hc']
      simp only [hcount, true_and]

theorem firstOrderContinuation_activation_transfer (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ)
    (hbefore : ∀ t, t<n → ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β
      (P.query (start+t) (firstOrderRestartRun P Θ A β start p s₀ z t).2) i))
    (hcount : firstOrderRestartCount P Θ A β start p i.val s₀ z n<cap)
    (hactive : 0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β
      (P.query (start+n) (firstOrderRestartRun P Θ A β start p s₀ z n).2) i)) :
    0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β
      (P.query (start+n) (stateTapeRun (0,s₀) (firstOrderContinuationStep P Θ A β start i.val cap dummy) z n).2) i) := by
  rw [←(firstOrderContinuation_coupling P Θ A β start p i cap dummy s₀ z hp n hbefore hcount).2.1]
  exact hactive

end
end SecondOrder
