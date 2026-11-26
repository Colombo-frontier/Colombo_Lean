import Matvec.Model

namespace Matvec
open MeasureTheory

theorem measurable_oracle_joint (m n : ℕ) :
    Measurable (fun p : Payoff m n × Query m n => oracle p.1 p.2) := by
  unfold oracle
  apply Measurable.prodMk
  all_goals
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    fun_prop

theorem Algorithm.joint_measurable_transcript {m n T : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (alg : Algorithm m n T Seed) (j : ℕ) :
    Measurable (fun p : Seed × Payoff m n => alg.transcript p.2 p.1 j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Algorithm.transcript, Fin.snoc_last]
      exact (measurable_oracle_joint m n).comp (measurable_snd.prodMk
        ((alg.query_measurable j).comp (measurable_fst.prodMk ih)))
    · simpa only [Algorithm.transcript, Fin.snoc_castSucc] using
        (measurable_pi_apply i).comp ih

theorem Algorithm.joint_measurable_run {m n T : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (alg : Algorithm m n T Seed) :
    Measurable (fun p : Seed × Payoff m n => alg.run p.2 p.1) :=
  alg.output_measurable.comp (measurable_fst.prodMk (alg.joint_measurable_transcript T))

theorem isClosed_simplex (n : ℕ) : IsClosed {x : Vec n | SimplexFeasible x} := by
  change IsClosed ({x : Vec n | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i = 1})
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const

theorem isClosed_ball (n : ℕ) : IsClosed {x : Vec n | InBall x} := by
  exact isClosed_le (by fun_prop) continuous_const

theorem isClosed_primal (g : Geometry) (n : ℕ) :
    IsClosed {x : Vec n | PrimalFeasible g x} := by
  cases g
  · exact isClosed_ball n
  · exact isClosed_simplex n

theorem continuous_payoff {m n : ℕ} (A : Payoff m n) :
    Continuous (fun p : Query m n => payoff A p.1 p.2) := by
  unfold payoff Matrix.mulVec dotProduct
  fun_prop

/-- Success is a Borel event even in the ball geometry: its universal gap
constraint is an arbitrary intersection of closed half-spaces. -/
theorem isClosed_gameSuccess {m n : ℕ} (g : Geometry) (A : Payoff m n) (ε : ℝ) :
    IsClosed {out : Query m n | GameSuccess g A ε out} := by
  change IsClosed ({out : Query m n | PrimalFeasible g out.1} ∩
    ({out | SimplexFeasible out.2} ∩
      {out | ∀ x y, PrimalFeasible g x → SimplexFeasible y →
        payoff A out.1 y - payoff A x out.2 ≤ ε}))
  apply IsClosed.inter ((isClosed_primal g n).preimage continuous_fst)
  apply IsClosed.inter ((isClosed_simplex m).preimage continuous_snd)
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro _hx
  apply isClosed_iInter
  intro _hy
  apply isClosed_le _ continuous_const
  unfold payoff Matrix.mulVec dotProduct
  fun_prop

theorem measurableSet_algorithm_success {m n T : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (alg : Algorithm m n T Seed) (g : Geometry)
    (A : Payoff m n) (ε : ℝ) :
    MeasurableSet {seed | GameSuccess g A ε (alg.run A seed)} :=
  (isClosed_gameSuccess g A ε).measurableSet.preimage (alg.measurable_run A)

end Matvec
