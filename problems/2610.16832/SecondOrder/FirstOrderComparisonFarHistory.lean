import SecondOrder.FirstOrderComparisonFarJump

open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- Far jumps among all queries represented by a finite history, including
the output query after its last sampled response. -/
def firstOrderHistoryFar (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (a₀ : FirstOrderCoefficients d T R) :
    (n : ℕ) → FiniteHistory Unit (FirstOrderCoefficients d T R) n → Prop
  | 0, h => ∃ i, firstOrderFarAt P Θ A β (finiteHistoryTape a₀ 0 h) 0 i
  | n+1, h => firstOrderHistoryFar P Θ A β a₀ n h.1 ∨
      ∃ i, firstOrderFarAt P Θ A β (finiteHistoryTape a₀ (n+1) h) (n+1) i

theorem firstOrderHistoryFar_iff (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (a₀ : FirstOrderCoefficients d T R) :
    ∀ n h, firstOrderHistoryFar P Θ A β a₀ n h ↔
      ∃ t, t≤n ∧ ∃ i, firstOrderFarAt P Θ A β (finiteHistoryTape a₀ n h) t i := by
  intro n
  induction n with
  | zero => intro h; simp only [Nat.le_zero, exists_eq_left, firstOrderHistoryFar]
  | succ n ih =>
    intro h
    have ht (t : ℕ) (ht : t≤n) (i : Fin (T+1)) :
        firstOrderFarAt P Θ A β (finiteHistoryTape a₀ (n+1) h) t i ↔
          firstOrderFarAt P Θ A β (finiteHistoryTape a₀ n h.1) t i :=
      firstOrderFarAt_tape_congr P Θ A β _ _ t
        (fun u hu => finiteHistoryTape_succ_lt a₀ n h u (by omega)) i
    change (_ ∨ _) ↔ _
    rw [ih]
    constructor
    · rintro (⟨t,htt,i,hi⟩ | ⟨i,hi⟩)
      · exact ⟨t,by omega,i,(ht t htt i).mpr hi⟩
      · exact ⟨n+1,le_rfl,i,hi⟩
    · rintro ⟨t,htt,i,hi⟩
      by_cases he : t=n+1
      · subst t; exact Or.inr ⟨i,hi⟩
      · exact Or.inl ⟨t,by omega,i,(ht t (by omega) i).mp hi⟩

theorem firstOrderHistoryFar_noFarJump (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) :
    firstOrderHistoryFar P Θ A β a₀ n h ↔
      ¬firstOrderNoFarJump P Θ A β (finiteHistoryTape a₀ n h) (n+1) := by
  rw [firstOrderHistoryFar_iff]
  constructor
  · rintro ⟨t,ht,i,hi⟩ hs
    exact hs t (by omega) i hi.1 hi.2
  · intro hs
    by_contra hn
    apply hs
    intro t ht i hi hp
    exact hn ⟨t,by omega,i,hi,hp⟩

theorem firstOrderComparisonJointLaw_previous_mean (P : FirstOrderPolicy d T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (F : (Fin (T+1) → (Fin d → Bool)) → FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℝ) :
    pmfMean (firstOrderComparisonJointLaw P A β R hR a₀ (n+1)) (fun w => F w.1 w.2.1)=
      pmfMean (firstOrderComparisonJointLaw P A β R hR a₀ n) (fun w => F w.1 w.2) := by
  simp only [firstOrderComparisonJointLaw, finiteConditionalPMF_mean]
  apply pmfMean_congr
  intro Θ
  exact finiteConditionalPMF_mean_fst _ _ (F Θ)

/-- Union bound under the joint law of the actual finite comparison history.
No independence of the query points is assumed. -/
theorem firstOrderComparison_history_far_probability (P : FirstOrderPolicy d T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : FirstOrderCoefficients d T R) :
    ∀ n, pmfEventProbability (firstOrderComparisonJointLaw P A β R hR a₀ n)
      (fun w => decide (firstOrderHistoryFar P w.1 A β a₀ n w.2))≤
      (n+1:ℕ)*((T+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))) := by
  intro n
  induction n with
  | zero => simpa only [Nat.zero_add, Nat.cast_one, one_mul, pmfEventProbability_mean,
      decide_eq_true_eq, firstOrderHistoryFar] using
      firstOrderComparison_far_any_at P A β R hR a₀ 0
  | succ n ih =>
    rw [pmfEventProbability_mean]
    simp only [decide_eq_true_eq, firstOrderHistoryFar]
    have hpoint : ∀ w : (Fin (T+1) → (Fin d → Bool)) × FiniteHistory Unit (FirstOrderCoefficients d T R) (n+1),
        (if firstOrderHistoryFar P w.1 A β a₀ n w.2.1 ∨
          ∃ i, firstOrderFarAt P w.1 A β (finiteHistoryTape a₀ (n+1) w.2) (n+1) i then (1:ℝ) else 0)≤
        (if firstOrderHistoryFar P w.1 A β a₀ n w.2.1 then (1:ℝ) else 0)+
          (if ∃ i, firstOrderFarAt P w.1 A β (finiteHistoryTape a₀ (n+1) w.2) (n+1) i then (1:ℝ) else 0) := by
      intro w
      split_ifs <;> norm_num <;> tauto
    apply (pmfMean_mono _ hpoint).trans
    rw [pmfMean_add, firstOrderComparisonJointLaw_previous_mean P A β R hR a₀ n
      (fun Θ h => if firstOrderHistoryFar P Θ A β a₀ n h then 1 else 0)]
    have hn := firstOrderComparison_far_any_at P A β R hR a₀ (n+1)
    rw [pmfEventProbability_mean] at hn ih
    simp only [decide_eq_true_eq] at hn ih
    push_cast
    push_cast at ih hn
    linarith only [ih, hn]

theorem firstOrderComparison_noFarJump_probability (P : FirstOrderPolicy d T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :
    pmfEventProbability (firstOrderComparisonJointLaw P A β R hR a₀ n)
      (fun w => decide (¬firstOrderNoFarJump P w.1 A β (finiteHistoryTape a₀ n w.2) (n+1)))≤
      (n+1:ℕ)*((T+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))) := by
  have he : (fun w : (Fin (T+1) → (Fin d → Bool)) × FiniteHistory Unit (FirstOrderCoefficients d T R) n =>
      decide (¬firstOrderNoFarJump P w.1 A β (finiteHistoryTape a₀ n w.2) (n+1)))=
      (fun w => decide (firstOrderHistoryFar P w.1 A β a₀ n w.2)) := by
    funext w
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, firstOrderHistoryFar_noFarJump]
  rw [he]
  exact firstOrderComparison_history_far_probability P A β R hR a₀ n

end
end SecondOrder

