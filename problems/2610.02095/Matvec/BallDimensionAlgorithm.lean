import Matvec.DimensionAlgorithm
import Matvec.MeasurableGameReduction

/-!
# Same-query-count ball--simplex dimension extension

Rows are duplicated, and extra primal coordinates are zero columns. The
compiled algorithm projects its primal output and aggregates its dual output.
All queries are unrestricted; both replies are simulated by one core oracle
call. The seed measure and the hard horizon remain exactly unchanged.
-/

namespace Matvec.DimensionExtension
open Matrix MeasureTheory MeasurableSimulation
open scoped Matrix Classical
noncomputable section
universe u

variable {m n M N e : ℕ}

def ballProject (ec : Fin N ≃ (Fin n ⊕ Fin e)) (x : Vec N) : Vec n :=
  fun j => x (ec.symm (Sum.inl j))

def ballLift (ec : Fin N ≃ (Fin n ⊕ Fin e)) (x : Vec n) : Vec N :=
  fun j => Sum.elim x (fun _ => 0) (ec j)

theorem ballProject_ballLift (ec : Fin N ≃ (Fin n ⊕ Fin e)) (x : Vec n) :
    ballProject ec (ballLift ec x) = x := by
  ext j
  simp [ballProject, ballLift]

theorem ballProject_feasible (ec : Fin N ≃ (Fin n ⊕ Fin e)) (x : Vec N) (hx : InBall x) :
    InBall (ballProject ec x) := by
  have hs : ∑ j : Fin n ⊕ Fin e, (x (ec.symm j)) ^ 2 ≤ 1 := by
    rw [ec.symm.sum_comp (fun j => (x j) ^ 2)]
    exact hx
  exact projected_ball_feasible (fun j => x (ec.symm j)) hs

theorem ballLift_feasible (ec : Fin N ≃ (Fin n ⊕ Fin e)) (x : Vec n) (hx : InBall x) :
    InBall (ballLift ec x) := by
  change (∑ j, (Sum.elim x (fun _ : Fin e => (0 : ℝ)) (ec j)) ^ 2) ≤ 1
  rw [ec.sum_comp (fun j => (Sum.elim x (fun _ : Fin e => (0 : ℝ)) j) ^ 2)]
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero] using hx

def paddedBallMatrix (A : Payoff m n) (ρ : Fin M → Fin m)
    (ec : Fin N ≃ (Fin n ⊕ Fin e)) : Payoff M N :=
  fun i j => padBallMatrix A ρ i (ec j)

theorem paddedBall_admissible (A : Payoff m n) (ρ : Fin M → Fin m)
    (ec : Fin N ≃ (Fin n ⊕ Fin e)) (hA : Admissible .ballSimplex A) :
    Admissible .ballSimplex (paddedBallMatrix A ρ ec) := by
  intro i
  change (∑ j, (padBallMatrix A ρ i (ec j)) ^ 2) ≤ 1
  rw [ec.sum_comp (fun j => (padBallMatrix A ρ i j) ^ 2), padBall_row_sq]
  exact hA (ρ i)

theorem paddedBall_mulVec (A : Payoff m n) (ρ : Fin M → Fin m)
    (ec : Fin N ≃ (Fin n ⊕ Fin e)) (x : Vec N) :
    paddedBallMatrix A ρ ec *ᵥ x = fun i => (A *ᵥ ballProject ec x) (ρ i) := by
  exact (reindex_mulVec (Equiv.refl (Fin M)) ec
    (padBallMatrix A ρ : Matrix (Fin M) (Fin n ⊕ Fin e) ℝ) x).trans
      (padBall_mulVec A ρ (x ∘ ec.symm))

theorem paddedBall_transpose_mulVec (A : Payoff m n) (ρ : Fin M → Fin m)
    (ec : Fin N ≃ (Fin n ⊕ Fin e)) (y : Vec M) :
    (paddedBallMatrix A ρ ec).transpose *ᵥ y = ballLift ec (A.transpose *ᵥ aggregate ρ y) := by
  exact (reindex_mulVec ec (Equiv.refl (Fin M))
    (padBallMatrix A ρ : Matrix (Fin M) (Fin n ⊕ Fin e) ℝ).transpose y).trans
      (congrArg (fun f : (Fin n ⊕ Fin e) → ℝ => f ∘ ec) (padBall_transpose_mulVec A ρ y))

def projectBallQuery (ρ : Fin M → Fin m) (ec : Fin N ≃ (Fin n ⊕ Fin e))
    (q : Query M N) : Query m n := (ballProject ec q.1, aggregate ρ q.2)

theorem measurable_projectBallQuery (ρ : Fin M → Fin m) (ec : Fin N ≃ (Fin n ⊕ Fin e)) :
    Measurable (projectBallQuery ρ ec) := by
  apply Measurable.prodMk
  · unfold ballProject
    fun_prop
  · exact (measurable_aggregate ρ).comp measurable_snd

def padBallReply (ρ : Fin M → Fin m) (ec : Fin N ≃ (Fin n ⊕ Fin e))
    (r : Reply m n) : Reply M N := ((fun i => r.1 (ρ i)), ballLift ec r.2)

theorem measurable_padBallReply (ρ : Fin M → Fin m) (ec : Fin N ≃ (Fin n ⊕ Fin e)) :
    Measurable (padBallReply ρ ec) := by
  apply Measurable.prodMk
  · fun_prop
  · apply measurable_pi_lambda
    intro j
    change Measurable (fun r : Reply m n => Sum.elim r.2 (fun _ => 0) (ec j))
    cases ec j <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem paddedBall_oracle (A : Payoff m n) (ρ : Fin M → Fin m)
    (ec : Fin N ≃ (Fin n ⊕ Fin e)) :
    padBallReply ρ ec ∘ oracle A ∘ projectBallQuery ρ ec = oracle (paddedBallMatrix A ρ ec) := by
  funext q
  apply Prod.ext
  · exact (paddedBall_mulVec A ρ ec q.1).symm
  · exact (paddedBall_transpose_mulVec A ρ ec q.2).symm

theorem paddedBall_payoff (A : Payoff m n) (ρ : Fin M → Fin m)
    (ec : Fin N ≃ (Fin n ⊕ Fin e)) (x : Vec N) (y : Vec M) :
    payoff (paddedBallMatrix A ρ ec) x y = payoff A (ballProject ec x) (aggregate ρ y) := by
  unfold payoff
  rw [paddedBall_mulVec]
  simpa only [dotProduct, mul_comm] using
    (aggregate_weighted_sum ρ y (A *ᵥ ballProject ec x)).symm

theorem paddedBall_gameSuccess (A : Payoff m n) (ρ : Fin M → Fin m)
    (hρ : Function.Surjective ρ) (ec : Fin N ≃ (Fin n ⊕ Fin e))
    (ε : ℝ) (out : Query M N)
    (hs : GameSuccess .ballSimplex (paddedBallMatrix A ρ ec) ε out) :
    GameSuccess .ballSimplex A ε (projectBallQuery ρ ec out) := by
  refine ⟨ballProject_feasible ec out.1 hs.1, aggregate_simplex ρ out.2 hs.2.1, ?_⟩
  intro x y hx hy
  have hrow (i : Fin m) :
      (A *ᵥ ballProject ec out.1) i - payoff A x (aggregate ρ out.2) ≤ ε := by
    obtain ⟨i', hi'⟩ := hρ i
    have h := hs.2.2 (ballLift ec x) (Pi.single i' 1)
      (ballLift_feasible ec x hx) (simplexFeasible_vertex i')
    rw [paddedBall_payoff A ρ ec (ballLift ec x) out.2, ballProject_ballLift] at h
    have hv : payoff (paddedBallMatrix A ρ ec) out.1 (Pi.single i' 1) =
        (A *ᵥ ballProject ec out.1) i := by
      unfold payoff
      rw [paddedBall_mulVec]
      simp [hi']
    rwa [hv] at h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hrow i) (hy.1 i))
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hy.2, one_mul] at hsum
  exact hsum

def paddedBallAlgorithm {T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Algorithm M N T Seed) (ρ : Fin M → Fin m) (ec : Fin N ≃ (Fin n ⊕ Fin e)) :
    Algorithm m n T Seed :=
  algorithmOfPolicy (((ofAlgorithm alg).mapOracle (projectBallQuery ρ ec) (padBallReply ρ ec)
    (measurable_projectBallQuery ρ ec) (measurable_padBallReply ρ ec)).mapOutput
      (fun _ q => projectBallQuery ρ ec q) ((measurable_projectBallQuery ρ ec).comp measurable_snd))

theorem paddedBallAlgorithm_run {T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Algorithm M N T Seed) (ρ : Fin M → Fin m) (ec : Fin N ≃ (Fin n ⊕ Fin e))
    (A : Payoff m n) (seed : Seed) :
    (paddedBallAlgorithm alg ρ ec).run A seed =
      projectBallQuery ρ ec (alg.run (paddedBallMatrix A ρ ec) seed) := by
  rw [paddedBallAlgorithm, algorithmOfPolicy_run, Policy.mapOutput_run, Policy.mapOracle_run,
    paddedBall_oracle, ofAlgorithm_run]

theorem paddedBallAlgorithm_solves {T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Algorithm M N T Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (ρ : Fin M → Fin m) (hρ : Function.Surjective ρ) (ec : Fin N ≃ (Fin n ⊕ Fin e))
    (ε : ℝ) (hsolve : Solves alg ν .ballSimplex ε) :
    Solves (paddedBallAlgorithm alg ρ ec) ν .ballSimplex ε := by
  intro A hA
  have hlarge := hsolve (paddedBallMatrix A ρ ec) (paddedBall_admissible A ρ ec hA)
  apply hlarge.trans
  refine measureReal_mono (fun seed hs => ?_) (measure_ne_top _ _)
  change GameSuccess .ballSimplex A ε ((paddedBallAlgorithm alg ρ ec).run A seed)
  rw [paddedBallAlgorithm_run]
  exact paddedBall_gameSuccess A ρ hρ ec ε _ hs

def ballPaddingEquiv (hN : n ≤ N) : Fin N ≃ (Fin n ⊕ Fin (N - n)) :=
  (finCongr (show N = n + (N - n) by omega)).trans finSumFinEquiv.symm

/-- Larger ball--simplex dimensions solve the smaller core with the same
random seed law and exactly the same hard query horizon. -/
theorem exists_ball_core_algorithm {T : ℕ} (hm : 0 < m) (_hn : 0 < n)
    (hM : m ≤ M) (hN : n ≤ N) {Seed : Type u} [MeasurableSpace Seed]
    (alg : Algorithm M N T Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (ε : ℝ) (hsolve : Solves alg ν .ballSimplex ε) :
    ∃ core : Algorithm m n T Seed, Solves core ν .ballSimplex ε :=
  ⟨paddedBallAlgorithm alg (coreProjection hm hM) (ballPaddingEquiv hN),
    paddedBallAlgorithm_solves alg ν _ (coreProjection_surjective hm hM) _ ε hsolve⟩

end
end Matvec.DimensionExtension
