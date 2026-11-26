import SecondOrder.CurvatureContinuationAgreement

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

def curvatureRestartRun (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start p : ℕ) (s₀ : S) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) : ℕ → ℕ × S :=
  stateTapeRun (p,s₀) (fun t => curvatureComparisonStep P Θ A β (start+t)) z

def curvatureRestartIndex (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start p : ℕ) (s₀ : S) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (t : ℕ) : ℕ :=
  let s := curvatureRestartRun P Θ A β start p s₀ z t
  curvatureLimitedProgress Θ β (P.query (start+t) s.2) (s.1+1)

def curvatureRestartCount (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start p stage : ℕ) (s₀ : S) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) : ℕ → ℕ
  | 0 => 0
  | n+1 => curvatureRestartCount P Θ A β start p stage s₀ z n+
      if curvatureRestartIndex P Θ A β start p s₀ z n=stage then 1 else 0

theorem curvatureRestartCount_mono (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start p stage : ℕ) (s₀ : S) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) :
    Monotone (curvatureRestartCount P Θ A β start p stage s₀ z) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [curvatureRestartCount]
  exact Nat.le_add_right _ _

/-- Up to a target's first activation, fewer than cap actual stage responses
force exact equality with the capped continuation, including response counts. -/
theorem curvatureContinuation_coupling (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (hp : p+1=i.val ∨ p=i.val) :
    ∀ n, (∀ t, t<n → ¬0<periodicCompletion (Θ i) (curvatureDilation m T β
        (P.query (start+t) (curvatureRestartRun P Θ A β start p s₀ z t).2) i)) →
      curvatureRestartCount P Θ A β start p i.val s₀ z n<cap →
      ((curvatureRestartRun P Θ A β start p s₀ z n).1+1=i.val ∨
        (curvatureRestartRun P Θ A β start p s₀ z n).1=i.val) ∧
      (curvatureRestartRun P Θ A β start p s₀ z n).2=
        (stateTapeRun (0,s₀) (curvatureContinuationStep P Θ A β start i.val cap dummy) z n).2 ∧
      (stateTapeRun (0,s₀) (curvatureContinuationStep P Θ A β start i.val cap dummy) z n).1=
        curvatureRestartCount P Θ A β start p i.val s₀ z n := by
  intro n
  induction n with
  | zero => intro _ _; exact ⟨hp,rfl,rfl⟩
  | succ n ih =>
    intro hi hc
    have hcount : curvatureRestartCount P Θ A β start p i.val s₀ z n<cap :=
      lt_of_le_of_lt (curvatureRestartCount_mono P Θ A β start p i.val s₀ z (Nat.le_succ n)) hc
    obtain ⟨hp',hs',hc'⟩ := ih (fun t ht => hi t (by omega)) hcount
    have hn := hi n (by omega)
    have hcap : (stateTapeRun (0,s₀) (curvatureContinuationStep P Θ A β start i.val cap dummy) z n).1<cap := by
      rw [hc']; exact hcount
    have hr : curvatureRestartRun P Θ A β start p s₀ z (n+1)=
        curvatureComparisonStep P Θ A β (start+n) (curvatureRestartRun P Θ A β start p s₀ z n) (z n) := rfl
    refine ⟨?_,?_,?_⟩
    · rw [hr]
      exact curvatureComparisonStep_before_target P Θ A β (start+n) i (z n) _ _ hp' hn
    · rw [hr, stateTapeRun]
      have hh := curvatureContinuationStep_agree P Θ A β start n i cap dummy (z n)
        (curvatureRestartRun P Θ A β start p s₀ z n).2
        (curvatureRestartRun P Θ A β start p s₀ z n).1
        (stateTapeRun (0,s₀) (curvatureContinuationStep P Θ A β start i.val cap dummy) z n).1 hp' hcap hn
      have hstate : ((stateTapeRun (0,s₀) (curvatureContinuationStep P Θ A β start i.val cap dummy) z n).1,
          (curvatureRestartRun P Θ A β start p s₀ z n).2)=
          stateTapeRun (0,s₀) (curvatureContinuationStep P Θ A β start i.val cap dummy) z n := by
        rw [hs']
      rw [hstate] at hh
      exact hh
    · rw [stateTapeRun, curvatureContinuationStep_count, curvatureRestartCount]
      have hk := curvatureLimitedProgress_stage_agree Θ β
        (P.query (start+n) (curvatureRestartRun P Θ A β start p s₀ z n).2) i
        (curvatureRestartRun P Θ A β start p s₀ z n).1 hp' hn
      unfold curvatureRestartIndex
      dsimp only
      rw [hk, hs', hc']
      simp only [hcount, true_and]

theorem curvatureContinuation_activation_transfer (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ)
    (hbefore : ∀ t, t<n → ¬0<periodicCompletion (Θ i) (curvatureDilation m T β
      (P.query (start+t) (curvatureRestartRun P Θ A β start p s₀ z t).2) i))
    (hcount : curvatureRestartCount P Θ A β start p i.val s₀ z n<cap)
    (hactive : 0<periodicCompletion (Θ i) (curvatureDilation m T β
      (P.query (start+n) (curvatureRestartRun P Θ A β start p s₀ z n).2) i)) :
    0<periodicCompletion (Θ i) (curvatureDilation m T β
      (P.query (start+n) (stateTapeRun (0,s₀) (curvatureContinuationStep P Θ A β start i.val cap dummy) z n).2) i) := by
  rw [←(curvatureContinuation_coupling P Θ A β start p i cap dummy s₀ z hp n hbefore hcount).2.1]
  exact hactive

end
end SecondOrder
