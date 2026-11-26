import NCConcave16991.DenseSmoothFutureProbability
import NCConcave16991.DenseSmoothRevelationAccounting
import NCConcave16991.FiniteLowerYao
import NCConcave16991.TheoremStatements

/-! # Actual finite static-bank families against arbitrary randomized policies -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NCConcave16991.DenseSmooth

open DenseWeakHiding Revelation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem invalid_budget_of_static_bank_bound {n m D T : ℕ} (hn : 0 < n) (hD : 0 < D)
    (hm : m ≤ n) (hp : m % 2 = n % 2) (hρ : 0 < (m : ℝ) / n)
    (hρ1 : (m : ℝ) / n ≤ 1) (N : ℕ) (c : ℝ) (hc : c < 2 / 3)
    (hupper : ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : OraclePolicy.AdaptivePolicy (Domain n T hn ((m : ℝ) / n) hρ) (n := n)
        (dx := primalDimension (EuclideanSpace ℝ (Fin D)) T) Ω) (seed : Ω),
      (stageBankLaw n m D (T + 1) hm).eventMass {bank |
        StationaryOutput (finiteSum hn hρ hρ1 (signTable hn hD hm hp bank)).toProblem
          (OraclePolicy.run (Domain n T hn ((m : ℝ) / n) hρ) P
            (oracleResponse (finiteSum hn hρ hρ1 (signTable hn hD hm hp bank)).toProblem) seed N).1} ≤ c) :
    ¬ ValidBudget (parameters hn hρ T) .individual N := by
  intro hvalid
  let E := EuclideanSpace ℝ (Fin D)
  obtain ⟨A,hA⟩ := hvalid (primalDimension E T) 0 (Domain n T hn ((m : ℝ) / n) hρ) 0
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  letI : MeasurableSpace (StageBank n m D (T + 1)) := ⊤
  letI : MeasurableSingletonClass (StageBank n m D (T + 1)) := ⟨fun _ ↦ trivial⟩
  let family := fun bank : StageBank n m D (T + 1) ↦
    (finiteSum hn hρ hρ1 (signTable hn hD hm hp bank)).toProblem
  let S := fun bank : StageBank n m D (T + 1) ↦ {seed : A.Seed |
    StationaryOutput (family bank)
      (OraclePolicy.run (Domain n T hn ((m : ℝ) / n) hρ) A.policy (oracleResponse (family bank)) seed N).1}
  have hs (bank : StageBank n m D (T + 1)) : MeasurableSet (S bank) ∧
      (2 / 3 : ℝ≥0∞) ≤ A.law (S bank) :=
    hA (family bank) rfl (SmoothFiniteSum.toProblem_individualSmooth _)
  apply finite_prior_uniform_success_contradiction (stageBankLaw n m D (T + 1) hm) A.law S
    (fun bank ↦ (hs bank).1) (q := 2 / 3)
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) (fun bank ↦ (hs bank).2)
    (c := c) (by norm_num; exact hc)
  intro seed
  rw [← FiniteLaw.eventMass_eq_probability]
  exact hupper A.Seed A.policy seed

/-- Before T calls the sequential frontier cannot reach stage T. The
actual future-stage tail then defeats every uniform randomized policy. -/
theorem stage_progress_randomized_lower {n m : ℕ} (hn : 0 < n)
    (hm : m ≤ n) (hp : m % 2 = n % 2) (hρ : 0 < (m : ℝ) / n)
    (hρ1 : (m : ℝ) / n ≤ 1) (T : ℕ) :
    LowerBudgetBound (parameters hn hρ T) .individual (T : ℝ) := by
  intro N hvalid
  by_contra hN
  have hNT : N < T := by exact_mod_cast (lt_of_not_ge hN)
  let D := alignmentDimension (N + 2) (T + 1)
  have hD : 0 < D := alignmentDimension_pos _ _
  apply invalid_budget_of_static_bank_bound hn hD hm hp hρ hρ1 N (1 / 128) (by norm_num) ?_ hvalid
  intro Ω _ P seed
  let law := stageBankLaw n m D (T + 1) hm
  apply (FiniteLaw.eventMass_mono law (fun bank hs ↦ ?_)).trans
    (future_alignment_probability_small hn hD hm hp hρ P seed N rfl)
  change ¬ NoFutureAlignment (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P seed
    (signTable hn hD hm hp bank) N
  intro hgood
  apply not_stationary_of_unfinished (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P seed hρ1
    (signTable hn hD hm hp bank) N
    (noFutureAlignment_queryGood _ _ _ _ _ _ _ _ _ _ hgood)
    ((run_frontier_le _ _ _ _ _ _ _ _ _ _).trans_lt hNT)
    (noFutureAlignment_outputGood _ _ _ _ _ _ _ _ _ _ hgood) hs

theorem one_randomized_lower (n : ℕ) (hn : 0 < n) (T : ℕ) :
    LowerBudgetBound (parameters hn (ρ := 1) (by norm_num) T) .individual (T : ℝ) := by
  have he : (n : ℝ) / n = 1 := div_self (by exact_mod_cast hn.ne')
  have hρ : 0 < (n : ℝ) / n := by rw [he]; norm_num
  have hρ1 : (n : ℝ) / n ≤ 1 := he.le
  simpa only [he] using stage_progress_randomized_lower hn (m := n) le_rfl rfl hρ hρ1 T

end NCConcave16991.DenseSmooth
