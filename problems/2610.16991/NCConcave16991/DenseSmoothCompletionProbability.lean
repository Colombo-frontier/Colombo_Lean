import NCConcave16991.DenseSmoothStageProbability
import NCConcave16991.DenseSmoothFutureProbe
import NCConcave16991.SequentialStageCounting

/-! # Actual completion counting and arbitrary-policy stationary success -/

noncomputable section

namespace NCConcave16991.DenseSmooth.Revelation

open DenseWeakHiding MeasureTheory

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable (n m T D : ℕ) (hn : 0 < n) (hD : 0 < D) (hm : m ≤ n)
  (hparity : m % 2 = n % 2) (hρ : 0 < (m : ℝ) / n)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ((m : ℝ) / n) hρ) (n := n)
    (dx := primalDimension (CensoredSpace D) T) Ω)

def CompletedEvent (seed : Ω) (N : ℕ) : Set (StageBank n m D (T + 1)) :=
  {bank | T ≤ frontier (CensoredSpace D) n T hn ((m : ℝ) / n) hρ
      (runWithTable (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed (signTable hn hD hm hparity bank) N)}

theorem completion_probability_le (seed : Ω) (N r : ℕ) (hT : 0 < T) (hr : 0 < r)
    (hwork : 2 * N ≤ r * T) (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (hDim : 512 * Real.log (((N + 2 : ℕ) : ℝ) + 2) + 2048 ≤ (D : ℝ)) :
    (stageBankLaw n m D (T + 1) hm).eventMass
      (CompletedEvent n m T D hn hD hm hparity hρ P seed N) ≤ 1 / 4 := by
  letI : MeasurableSpace (StageBank n m D (T + 1)) := ⊤
  let law := stageBankLaw n m D (T + 1) hm
  let E := ShortCompletedEvent n m T D hn hD hm hparity hρ P seed N r
  let cost := fun (bank : StageBank n m D (T + 1)) (j : Fin T) ↦
    (runWithTable (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed
      (signTable hn hD hm hparity bank) N).assigned j.castSucc
  have hprob (j : Fin T) : law.law.real (E j) ≤ (1 / 8 : ℝ) := by
    rw [← FiniteLaw.eventMass_eq_probability]
    exact short_completed_probability_le n m T D hn hD hm hparity hρ P seed N r j hrn hbudget hcoef hDim
  have htotal (bank : StageBank n m D (T + 1)) : 2 * (∑ j, cost bank j) ≤ r * T := by
    have hh := run_assigned_prefix_le (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed
      (signTable hn hD hm hparity bank) N
    exact (Nat.mul_le_mul_left 2 hh).trans hwork
  have hshort : ∀ bank ∈ CompletedEvent n m T D hn hD hm hparity hρ P seed N,
      ∀ j, cost bank j < r → bank ∈ E j := by
    intro bank hb j hj
    exact ⟨j.isLt.trans_le hb,hj⟩
  have hp := SequentialStages.completion_probability_le law.law hT hr E
    (fun _ ↦ MeasurableSet.of_discrete) hprob
    (CompletedEvent n m T D hn hD hm hparity hρ P seed N) cost
    (fun bank _ ↦ htotal bank) hshort
  rw [FiniteLaw.eventMass_eq_probability]
  exact hp.trans (by norm_num)

def ActualSuccessEvent (hρ1 : (m : ℝ) / n ≤ 1) (seed : Ω) (N : ℕ) :
    Set (StageBank n m D (T + 1)) :=
  {bank | StationaryOutput (finiteSum hn hρ hρ1 (signTable hn hD hm hparity bank)).toProblem
    (OraclePolicy.run (Domain n T hn ((m : ℝ) / n) hρ) P
      (oracleResponse (finiteSum hn hρ hρ1 (signTable hn hD hm hparity bank)).toProblem) seed N).1}

def FutureBadEvent (seed : Ω) (N : ℕ) : Set (StageBank n m D (T + 1)) :=
  {bank | ¬ NoFutureAlignment (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed
      (signTable hn hD hm hparity bank) N}

theorem success_subset_completed_union_futureBad (hρ1 : (m : ℝ) / n ≤ 1) (seed : Ω) (N : ℕ) :
    ActualSuccessEvent n m T D hn hD hm hparity hρ P hρ1 seed N ⊆
      CompletedEvent n m T D hn hD hm hparity hρ P seed N ∪
        FutureBadEvent n m T D hn hD hm hparity hρ P seed N := by
  intro bank hb
  by_cases hg : NoFutureAlignment (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed
      (signTable hn hD hm hparity bank) N
  · apply Or.inl
    by_contra hf
    have hnot := not_stationary_of_unfinished (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed hρ1
      (signTable hn hD hm hparity bank) N
      (noFutureAlignment_queryGood (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed _ N hg)
      (Nat.lt_of_not_ge hf)
      (noFutureAlignment_outputGood (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed _ N hg)
    exact hnot hb
  · exact Or.inr hg

private theorem eventMass_union_le {I : Type*} [Fintype I] (law : FiniteLaw I) (A B : Set I) :
    law.eventMass (A ∪ B) ≤ law.eventMass A + law.eventMass B := by
  classical
  unfold FiniteLaw.eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [ha,hb] <;> linarith [law.nonneg i]

theorem stationary_success_probability_additive (hρ1 : (m : ℝ) / n ≤ 1) (seed : Ω) (N r : ℕ)
    (hT : 0 < T) (hr : 0 < r) (hwork : 2 * N ≤ r * T)
    (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (hDim : 512 * Real.log (((N + 2 : ℕ) : ℝ) + 2) + 2048 ≤ (D : ℝ)) :
    (stageBankLaw n m D (T + 1) hm).eventMass
        (ActualSuccessEvent n m T D hn hD hm hparity hρ P hρ1 seed N) ≤
      1 / 4 + (stageBankLaw n m D (T + 1) hm).eventMass
        (FutureBadEvent n m T D hn hD hm hparity hρ P seed N) := by
  apply (FiniteLaw.eventMass_mono _
    (success_subset_completed_union_futureBad n m T D hn hD hm hparity hρ P hρ1 seed N)).trans
  apply (eventMass_union_le _ _ _).trans
  have hc := completion_probability_le n m T D hn hD hm hparity hρ P seed N r hT hr hwork hrn hbudget hcoef hDim
  linarith

theorem stationary_success_probability_small_budget (hρ1 : (m : ℝ) / n ≤ 1) (seed : Ω) (N : ℕ)
    (hNT : N < T) :
    (stageBankLaw n m D (T + 1) hm).eventMass
        (ActualSuccessEvent n m T D hn hD hm hparity hρ P hρ1 seed N) ≤
      (stageBankLaw n m D (T + 1) hm).eventMass
        (FutureBadEvent n m T D hn hD hm hparity hρ P seed N) := by
  apply FiniteLaw.eventMass_mono
  intro bank hb
  rcases success_subset_completed_union_futureBad n m T D hn hD hm hparity hρ P hρ1 seed N hb with hc | hbad
  · have hh := run_frontier_le (CensoredSpace D) n T hn ((m : ℝ) / n) hρ P seed
      (signTable hn hD hm hparity bank) N
    change T ≤ _ at hc
    omega
  · exact hbad

end NCConcave16991.DenseSmooth.Revelation
