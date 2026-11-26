import VIReference.Pilot.UpperRestart
import VIReference.Pilot.UpperBaseAdaptiveCost
import VIReference.Pilot.UpperBaseLog

/-!
# Complete certified restart transformation

This file installs the two finite public schedules used by `lem:restart`:
the inner halving schedule of one `RestartTrial`, and the outer doubling list
of radius guesses.  Every child call is locally capped.  Thus an invalid
radius can only return a genuinely verified certificate or explicit failure,
while the final public radius `D` succeeds on every valid strongly monotone
instance.
-/

open Set
open Filter
open scoped RealInnerProductSpace BigOperators
open scoped Topology

namespace VIReference.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A public witness that repeated halving eventually reaches the final
accuracy stage of `RestartTrial`. -/
theorem exists_restart_halving_threshold (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (hR : 0 ≤ R) :
    ∃ n : ℕ, mu * (R / (2 : ℝ) ^ n) / 2 ≤ delta := by
  have ht : Tendsto (fun n : ℕ ↦ (mu * R / 2) * (1 / 2 : ℝ) ^ n)
      atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [mul_zero] using hp.const_mul (mu * R / 2)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht delta hdelta
  have hclose := hN N le_rfl
  have hnonneg : 0 ≤ (mu * R / 2) * (1 / 2 : ℝ) ^ N := by positivity
  refine ⟨N, ?_⟩
  have hle : (mu * R / 2) * (1 / 2 : ℝ) ^ N ≤ delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hclose
    exact hclose.le
  calc
    mu * (R / (2 : ℝ) ^ N) / 2 =
        (mu * R / 2) * (1 / 2 : ℝ) ^ N := by
      rw [one_div, inv_pow]
      ring
    _ ≤ delta := hle

/-- Least public number of nonfinal restart calls. -/
noncomputable def restartHalvingCount (mu delta R : ℝ) : ℕ :=
  if h : 0 < mu ∧ 0 < delta ∧ 0 ≤ R then
    Nat.find (exists_restart_halving_threshold mu delta R h.1 h.2.1 h.2.2)
  else 0

theorem restartHalvingCount_threshold (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (hR : 0 ≤ R) :
    mu * (R / (2 : ℝ) ^ restartHalvingCount mu delta R) / 2 ≤ delta := by
  rw [restartHalvingCount, dif_pos ⟨hmu, hdelta, hR⟩]
  exact Nat.find_spec (exists_restart_halving_threshold mu delta R hmu hdelta hR)

/-- Before the least stopping index, the source accuracy is strictly larger
than `delta`; this makes the installed finite program equivalent to the
`max {delta, mu*r/2}` loop. -/
theorem restartHalvingCount_prior (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (hR : 0 ≤ R)
    (i : ℕ) (hi : i < restartHalvingCount mu delta R) :
    delta < mu * (R / (2 : ℝ) ^ i) / 2 := by
  rw [restartHalvingCount, dif_pos ⟨hmu, hdelta, hR⟩] at hi
  exact lt_of_not_ge (Nat.find_min
    (exists_restart_halving_threshold mu delta R hmu hdelta hR) hi)

/-- `RestartTrial` with its public final-accuracy stopping time installed. -/
noncomputable def scheduledRestartTrialCall (data : VIPublicData E)
    (A : ResidualSolver data) (alpha : ℝ) (b : ℕ)
    (mu delta : ℝ) (center : data.X) (R : ℝ) : CappedExactJetCall data :=
  restartTrialCall data A alpha b mu delta
    (restartHalvingCount mu delta R) center R

theorem restartTrialProgram_no_false_success
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (halvings : ℕ) (center : data.X) (R : ℝ) (hR : 0 < R)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (heval : ExactJetProgram.Evaluates oracle.answer
      (restartTrialProgram data A mu delta halvings center R)
      used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  induction halvings generalizing center R used with
  | zero =>
      change ExactJetProgram.Evaluates oracle.answer
        (residualSubcallProgram data A center R delta) used (some cert) at heval
      have horig := ExactJetProgram.evaluation_of_locallyCapped_success'
        oracle.answer _ _ used cert heval
      exact hA.2.1 G oracle center R delta used cert hG hR hdelta
        (horig.1.runWithFuel_eq horig.2)
  | succ n ih =>
      change ExactJetProgram.Evaluates oracle.answer
        ((residualSubcallProgram data A center R (mu * R / 2)).bind
          (fun headCert => restartTrialProgram data A mu delta n
            headCert.point (R / 2))) used (some cert) at heval
      obtain ⟨headCert, usedHead, usedTail, _hhead, htail⟩ :=
        ExactJetProgram.evaluates_bind_some_right oracle.answer _ _ heval
      exact ih headCert.point (R / 2) (by positivity) htail

theorem scheduledRestartTrialCall_no_false_success
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (center : data.X) (R : ℝ) (hR : 0 < R)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (hrun : (scheduledRestartTrialCall data A alpha b mu delta center R).execute
      data G oracle = .finished used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  have heval : ExactJetProgram.Evaluates oracle.answer
      (restartTrialProgram data A mu delta (restartHalvingCount mu delta R)
        center R) used (some cert) :=
    ExactJetProgram.evaluates_of_runWithFuel_finished hrun
  exact restartTrialProgram_no_false_success data A alpha b hA G oracle hG
    mu delta hmu hdelta _ center R hR heval

/-- Start every guessed-radius trial from the original center.  Only an
explicitly exhausted/failed local call reaches the next guess. -/
noncomputable def adaptiveRestartProgramFrom (data : VIPublicData E)
    (A : ResidualSolver data) (alpha : ℝ) (b : ℕ)
    (mu delta : ℝ) (center : data.X) :
    (remaining j : ℕ) → ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data)
  | 0, j =>
      let call := scheduledRestartTrialCall data A alpha b mu delta center
        (adaptiveGuessRadius data mu j)
      call.program.locallyCapped call.cap
  | remaining + 1, j =>
      let call := scheduledRestartTrialCall data A alpha b mu delta center
        (adaptiveGuessRadius data mu j)
      ExactJetProgram.orElse (call.program.locallyCapped call.cap)
        (adaptiveRestartProgramFrom data A alpha b mu delta center remaining (j + 1))

noncomputable def adaptiveRestartCapFrom (data : VIPublicData E)
    (A : ResidualSolver data) (alpha : ℝ) (b : ℕ)
    (mu delta : ℝ) (center : data.X) : (remaining j : ℕ) → ℕ
  | 0, j => (scheduledRestartTrialCall data A alpha b mu delta center
      (adaptiveGuessRadius data mu j)).cap
  | remaining + 1, j =>
      (scheduledRestartTrialCall data A alpha b mu delta center
        (adaptiveGuessRadius data mu j)).cap +
      adaptiveRestartCapFrom data A alpha b mu delta center remaining (j + 1)

noncomputable def adaptiveRestartCall (data : VIPublicData E)
    (A : ResidualSolver data) (alpha : ℝ) (b : ℕ)
    (center : data.X) (mu delta : ℝ) : CappedExactJetCall data where
  cap := adaptiveRestartCapFrom data A alpha b mu delta center
    (adaptiveGuessCount data mu) 0
  program := adaptiveRestartProgramFrom data A alpha b mu delta center
    (adaptiveGuessCount data mu) 0

theorem adaptiveRestartProgramFrom_no_false_success
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (center : data.X) (remaining j : ℕ)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (heval : ExactJetProgram.Evaluates oracle.answer
      (adaptiveRestartProgramFrom data A alpha b mu delta center remaining j)
      used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  induction remaining generalizing j used cert with
  | zero =>
      have horig := ExactJetProgram.evaluation_of_locallyCapped_success'
        oracle.answer _ _ used cert (by simpa [adaptiveRestartProgramFrom] using heval)
      exact scheduledRestartTrialCall_no_false_success data A alpha b hA G oracle
        hG mu delta hmu hdelta center _ (adaptiveGuessRadius_pos data mu hmu j)
        (horig.1.runWithFuel_eq horig.2)
  | succ remaining ih =>
      simp only [adaptiveRestartProgramFrom] at heval
      apply ExactJetProgram.property_of_orElse_success oracle.answer
        (fun cert ↦ cert.IsVerifiedFor data G delta) _ _ _ _ heval
      · intro used cert hlocal
        have horig := ExactJetProgram.evaluation_of_locallyCapped_success'
          oracle.answer _ _ used cert hlocal
        exact scheduledRestartTrialCall_no_false_success data A alpha b hA G oracle
          hG mu delta hmu hdelta center _ (adaptiveGuessRadius_pos data mu hmu j)
          (horig.1.runWithFuel_eq horig.2)
      · intro used cert htail
        exact ih (j + 1) (used := used) htail

/-- If the trial at a public offset succeeds within its installed cap, the
outer wrapper succeeds no later than that offset and pays only that prefix. -/
theorem adaptiveRestartProgramFrom_succeeds_at_offset
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta) (center : data.X)
    (remaining j target : ℕ) (htarget : target ≤ remaining)
    (htrial : ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (scheduledRestartTrialCall data A alpha b mu delta center
          (adaptiveGuessRadius data mu (j + target))).program used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ (scheduledRestartTrialCall data A alpha b mu delta center
        (adaptiveGuessRadius data mu (j + target))).cap) :
    ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (adaptiveRestartProgramFrom data A alpha b mu delta center remaining j)
        used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ adaptiveRestartCapFrom data A alpha b mu delta center target j := by
  induction remaining generalizing j target with
  | zero =>
      have ht : target = 0 := by omega
      subst target
      obtain ⟨used, cert, heval, hcert, hused⟩ := htrial
      refine ⟨used, cert, ?_, hcert, ?_⟩
      · simpa [adaptiveRestartProgramFrom] using heval.locallyCapped hused
      · simpa [adaptiveRestartCapFrom] using hused
  | succ remaining ih =>
      cases target with
      | zero =>
          obtain ⟨used, cert, heval, hcert, hused⟩ := htrial
          refine ⟨used, cert, ?_, hcert, ?_⟩
          · simp only [adaptiveRestartProgramFrom]
            exact ExactJetProgram.evaluates_orElse_of_some
              (heval.locallyCapped hused)
          · simpa [adaptiveRestartCapFrom] using hused
      | succ target =>
          let call := scheduledRestartTrialCall data A alpha b mu delta center
            (adaptiveGuessRadius data mu j)
          obtain ⟨used₁, result₁, hfirst, hused₁⟩ :=
            ExactJetProgram.locallyCapped_total oracle.answer call.program call.cap
          cases result₁ with
          | some cert₁ =>
              have horig := ExactJetProgram.evaluation_of_locallyCapped_success'
                oracle.answer call.program call.cap used₁ cert₁ hfirst
              have hcert₁ := adaptiveRestartProgramFrom_no_false_success
                data A alpha b hA G oracle hG mu delta hmu hdelta
                  center 0 j (by
                    simpa [adaptiveRestartProgramFrom] using hfirst)
              refine ⟨used₁, cert₁,
                ExactJetProgram.evaluates_orElse_of_some hfirst, hcert₁, ?_⟩
              simpa [adaptiveRestartCapFrom, call] using
                hused₁.trans (Nat.le_add_right _ _)
          | none =>
              have htrial' : ∃ used cert,
                  ExactJetProgram.Evaluates oracle.answer
                    (scheduledRestartTrialCall data A alpha b mu delta center
                      (adaptiveGuessRadius data mu ((j + 1) + target))).program
                    used (some cert) ∧ cert.IsVerifiedFor data G delta ∧
                  used ≤ (scheduledRestartTrialCall data A alpha b mu delta center
                    (adaptiveGuessRadius data mu ((j + 1) + target))).cap := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrial
              obtain ⟨used₂, cert, htail, hcert, hused₂⟩ :=
                ih (j + 1) target (by omega) htrial'
              refine ⟨used₁ + used₂, cert, ?_, hcert, ?_⟩
              · simp only [adaptiveRestartProgramFrom]
                exact ExactJetProgram.evaluates_orElse_of_none hfirst htail
              · simp only [adaptiveRestartCapFrom]
                change used₁ + used₂ ≤ call.cap +
                  adaptiveRestartCapFrom data A alpha b mu delta center target (j + 1)
                omega

theorem scheduledRestartTrialProgram_succeeds
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (center : data.X) (R : ℝ) (hR : 0 < R) (hRD : R ≤ data.D)
    (hcenter : ‖center.1 - zStar‖ ≤ R) :
    ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (scheduledRestartTrialCall data A alpha b mu delta center R).program
        used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ (scheduledRestartTrialCall data A alpha b mu delta center R).cap := by
  obtain ⟨used, cert, hrun, hcert, hused⟩ := restartTrialCall_succeeds
    data A alpha b hA G oracle hG mu delta hmu hdelta hstrong zStar hz
      (restartHalvingCount mu delta R) center R hR hRD hcenter
  exact ⟨used, cert, ExactJetProgram.evaluates_of_runWithFuel_finished hrun,
    hcert, hused⟩

/-- The final installed radius is `D`; hence the executable outer wrapper
always succeeds on a valid strongly monotone instance. -/
theorem adaptiveRestartCall_succeeds
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar) :
    ∃ used cert,
      (adaptiveRestartCall data A alpha b center mu delta).execute data G oracle =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ adaptiveRestartCapFrom data A alpha b mu delta center
        (adaptiveGuessCount data mu) 0 := by
  have hcenterD : ‖center.1 - zStar‖ ≤ data.D := by
    simpa [dist_eq_norm] using data.diameter_le center.1 center.2 zStar hz.1
  have hlast := scheduledRestartTrialProgram_succeeds data A alpha b hA G oracle
    hG mu delta hmu hdelta hstrong zStar hz center data.D data.D_pos le_rfl hcenterD
  have hlast' : ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (scheduledRestartTrialCall data A alpha b mu delta center
          (adaptiveGuessRadius data mu (0 + adaptiveGuessCount data mu))).program
        used (some cert) ∧ cert.IsVerifiedFor data G delta ∧
      used ≤ (scheduledRestartTrialCall data A alpha b mu delta center
        (adaptiveGuessRadius data mu (0 + adaptiveGuessCount data mu))).cap := by
    simpa [adaptiveGuessRadius_last data mu hmu] using hlast
  obtain ⟨used, cert, heval, hcert, hused⟩ :=
    adaptiveRestartProgramFrom_succeeds_at_offset data A alpha b hA G oracle hG
      mu delta hmu hdelta center (adaptiveGuessCount data mu) 0
      (adaptiveGuessCount data mu) le_rfl hlast'
  exact ⟨used, cert, heval.runWithFuel_eq hused, hcert, hused⟩

theorem adaptiveRestartCall_no_false_success
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (hrun : (adaptiveRestartCall data A alpha b center mu delta).execute
      data G oracle = .finished used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  exact adaptiveRestartProgramFrom_no_false_success data A alpha b hA G oracle
    hG mu delta hmu hdelta center (adaptiveGuessCount data mu) 0
      (ExactJetProgram.evaluates_of_runWithFuel_finished hrun)

theorem adaptiveRestartCapFrom_mono_remaining
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ) (center : data.X)
    (j small large : ℕ) (h : small ≤ large) :
    adaptiveRestartCapFrom data A alpha b mu delta center small j ≤
      adaptiveRestartCapFrom data A alpha b mu delta center large j := by
  induction large generalizing small j with
  | zero =>
      have : small = 0 := by omega
      subst small
      exact le_rfl
  | succ large ih =>
      cases small with
      | zero =>
          simp only [adaptiveRestartCapFrom]
          exact Nat.le_add_right _ _
      | succ small =>
          simp only [adaptiveRestartCapFrom]
          exact Nat.add_le_add_left (ih (j + 1) small (by omega)) _

/-- Sharp execution bridge: the actual outer program stops by any covering
guess and pays only the caps through that guess. -/
theorem adaptiveRestartCall_succeeds_at_guess
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (j : ℕ) (hj : j ≤ adaptiveGuessCount data mu)
    (hcover : ‖center.1 - zStar‖ ≤ adaptiveGuessRadius data mu j) :
    ∃ used cert,
      (adaptiveRestartCall data A alpha b center mu delta).execute data G oracle =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ adaptiveRestartCapFrom data A alpha b mu delta center j 0 := by
  have hRpos := adaptiveGuessRadius_pos data mu hmu j
  have htrial := scheduledRestartTrialProgram_succeeds data A alpha b hA G oracle
    hG mu delta hmu hdelta hstrong zStar hz center
      (adaptiveGuessRadius data mu j) hRpos (min_le_left _ _) hcover
  obtain ⟨used, cert, heval, hcert, hused⟩ :=
    adaptiveRestartProgramFrom_succeeds_at_offset data A alpha b hA G oracle hG
      mu delta hmu hdelta center (adaptiveGuessCount data mu) 0 j hj
      (by simpa using htrial)
  have hprefix := adaptiveRestartCapFrom_mono_remaining data A alpha b mu delta
    center 0 j (adaptiveGuessCount data mu) hj
  exact ⟨used, cert, heval.runWithFuel_eq (hused.trans hprefix), hcert, hused⟩

/-- The solver transformation before its fixed-order leading constant is
attached. -/
noncomputable def restartedStrongSolver (data : VIPublicData E)
    (A : ResidualSolver data) (alpha : ℝ) (b : ℕ) : StrongSolver data where
  leadingConstant := 1
  leadingConstant_pos := by norm_num
  solve := adaptiveRestartCall data A alpha b

end

end VIReference.Pilot
