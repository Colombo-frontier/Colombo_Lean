import NCConcave16991.DenseWeakInformationDivergence

/-! # A finite event-transfer inequality from actual relative entropy -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

variable {I : Type*} [Fintype I]

attribute [local instance] Classical.propDecidable

def eventMass (P : FiniteLaw I) (E : Set I) : ℝ := ∑ i, if i ∈ E then P.mass i else 0

theorem eventMass_nonneg (P : FiniteLaw I) (E : Set I) : 0 ≤ P.eventMass E := by
  classical
  exact Finset.sum_nonneg (fun i _ ↦ by split_ifs; exact P.nonneg i; exact le_rfl)

theorem eventMass_le_one (P : FiniteLaw I) (E : Set I) : P.eventMass E ≤ 1 := by
  classical
  rw [← P.sum_one]
  exact Finset.sum_le_sum (fun i _ ↦ by split_ifs <;> simp_all [P.nonneg i])

theorem exponentialMoment_event (Q : FiniteLaw I) (E : Set I) (s : ℝ) :
    Q.exponentialMoment (fun i ↦ if i ∈ E then s else 0) =
      1 + (Real.exp s - 1) * Q.eventMass E := by
  classical
  have he (i : I) : Q.mass i * Real.exp (if i ∈ E then s else 0) =
      Q.mass i + (Real.exp s - 1) * (if i ∈ E then Q.mass i else 0) := by
    by_cases hi : i ∈ E <;> simp [hi] <;> ring
  unfold exponentialMoment
  rw [Finset.sum_congr rfl (fun i _ ↦ he i), Finset.sum_add_distrib,
    ← Finset.mul_sum, Q.sum_one]
  rfl

theorem exponentialMoment_event_le_two (Q : FiniteLaw I) (E : Set I) (s : ℝ)
    (hq : Q.eventMass E ≤ Real.exp (-s)) :
    Q.exponentialMoment (fun i ↦ if i ∈ E then s else 0) ≤ 2 := by
  classical
  rw [exponentialMoment_event]
  have hmul := mul_le_mul_of_nonneg_left hq (Real.exp_pos s).le
  rw [← Real.exp_add] at hmul
  simp only [add_neg_cancel, Real.exp_zero] at hmul
  have hn := Q.eventMass_nonneg E
  nlinarith

theorem event_transfer (P Q : FiniteLaw I) (hs : P.SupportedBy Q)
    (E : Set I) (s : ℝ) (hq : Q.eventMass E ≤ Real.exp (-s)) :
    s * P.eventMass E ≤ P.relativeEntropy Q + 1 := by
  classical
  have hv := relativeEntropy_variational P Q hs (fun i ↦ if i ∈ E then s else 0)
  have he : (∑ i, P.mass i * (if i ∈ E then s else 0)) = s * P.eventMass E := by
    rw [eventMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ E <;> simp [hi, mul_comm]
  rw [he] at hv
  have hlog : Real.log (Q.exponentialMoment (fun i ↦ if i ∈ E then s else 0)) ≤ 1 := by
    have hm := exponentialMoment_event_le_two Q E s hq
    exact (Real.log_le_log (Q.exponentialMoment_pos _) hm).trans
      (by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); norm_num at hh; exact hh)
  linarith

theorem mutualInformation_event_transfer {J : Type*} [Fintype J]
    (P : FiniteLaw (I × J)) (E : Set (I × J)) (s : ℝ)
    (hq : (P.fst.product P.snd).eventMass E ≤ Real.exp (-s)) :
    s * P.eventMass E ≤ P.mutualInformation + 1 := by
  rw [P.mutualInformation_eq_relativeEntropy]
  exact event_transfer P (P.fst.product P.snd) (P.joint_supportedBy_product) E s hq

end NCConcave16991.DenseWeakHiding.FiniteLaw
