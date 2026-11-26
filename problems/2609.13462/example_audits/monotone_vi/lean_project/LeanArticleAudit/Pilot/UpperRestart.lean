import LeanArticleAudit.Pilot.UpperInterfaces

/-!
# Certified restart

The lemmas here establish the correctness kernel used by the executable
restart wrapper: a verified residual certificate for a strongly monotone VI
controls true distance, hence a call at accuracy `mu * R / 2` halves a valid
distance promise.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Equation (strong-certificate-distance). -/
theorem strong_certificate_distance
    (data : VIPublicData E) (G : E → E) (mu epsilon : ℝ)
    (hmu : 0 < mu) (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (cert : EvaluatedNormalCertificate data)
    (hcert : cert.IsVerifiedFor data G epsilon) :
    mu * ‖cert.point.1 - zStar‖ ≤ ‖cert.value + cert.normal‖ := by
  let q := ‖cert.point.1 - zStar‖
  have hstrong' := hstrong cert.point.1 cert.point.2 zStar hz.1
  have hzvi := hz.2 cert.point.1 cert.point.2
  have hn := hcert.1 zStar hz.1
  have hn' : 0 ≤ inner ℝ cert.normal (cert.point.1 - zStar) := by
    rw [show cert.point.1 - zStar = -(zStar - cert.point.1) by abel,
      inner_neg_right]
    linarith
  have hlower : mu * q ^ 2 ≤
      inner ℝ (cert.value + cert.normal) (cert.point.1 - zStar) := by
    rw [hcert.2.1, inner_add_left]
    rw [inner_sub_left] at hstrong'
    dsimp [q] at hstrong' ⊢
    linarith
  have hupper : inner ℝ (cert.value + cert.normal)
      (cert.point.1 - zStar) ≤
      ‖cert.value + cert.normal‖ * q := by
    simpa [q] using real_inner_le_norm
      (cert.value + cert.normal) (cert.point.1 - zStar)
  by_cases hq0 : q = 0
  · simp [q, hq0]
  · have hq : 0 < q := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq0)
    nlinarith

theorem verified_certificate_distance_le
    (data : VIPublicData E) (G : E → E) (mu epsilon R : ℝ)
    (hmu : 0 < mu) (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (cert : EvaluatedNormalCertificate data)
    (hcert : cert.IsVerifiedFor data G epsilon)
    (hepsilon : epsilon ≤ mu * R) :
    ‖cert.point.1 - zStar‖ ≤ R := by
  have hdist := strong_certificate_distance data G mu epsilon hmu hstrong
    zStar hz cert hcert
  have hres := hcert.2.2
  have hmul : mu * ‖cert.point.1 - zStar‖ ≤ mu * R :=
    hdist.trans (hres.trans hepsilon)
  exact (mul_le_mul_iff_right₀ hmu).mp hmul

/-- One valid nonfinal restart call returns a verified certificate and halves
the true distance.  The run and its query count come from the residual
solver's executable program, not from an assumed restart oracle. -/
theorem residualSolver_call_halves
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu R : ℝ) (hmu : 0 < mu) (hR : 0 < R) (hRD : R ≤ data.D)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (center : data.X) (hpromise : ‖center.1 - zStar‖ ≤ R) :
    ∃ used cert,
      (A.solve center R (mu * R / 2)).execute data G oracle =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data G (mu * R / 2) ∧
      ‖cert.point.1 - zStar‖ ≤ R / 2 ∧
      (used : ℝ) ≤ residualInterfaceCost data A.leadingConstant alpha b
        R (mu * R / 2) := by
  obtain ⟨used, cert, hrun, hcert, hcost⟩ := hA.2.2 G oracle center R
    (mu * R / 2) hG hR hRD (by positivity) zStar hz hpromise
  refine ⟨used, cert, hrun, hcert, ?_, hcost⟩
  apply verified_certificate_distance_le data G mu (mu * R / 2) (R / 2)
    hmu hstrong zStar hz cert hcert
  ring_nf
  exact le_rfl

/-- A final residual call at target `delta` is already a verified strong-solver
output; no exact proximal recovery or uncounted evaluation is needed. -/
theorem residualSolver_final_call
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (R delta : ℝ) (hR : 0 < R) (hRD : R ≤ data.D)
    (hdelta : 0 < delta)
    (zStar : E) (hz : IsVISolution data G zStar)
    (center : data.X) (hpromise : ‖center.1 - zStar‖ ≤ R) :
    ∃ used cert,
      (A.solve center R delta).execute data G oracle =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      (used : ℝ) ≤ residualInterfaceCost data A.leadingConstant alpha b R delta := by
  exact hA.2.2 G oracle center R delta hG hR hRD hdelta zStar hz hpromise

/-- The dimensionless condition in every nonfinal restart call has the
source's exact form `2 Lp R^(p-1) / mu`. -/
theorem residualCondition_restart_accuracy
    (data : VIPublicData E) (mu R : ℝ) (hmu : 0 < mu) (hR : 0 < R) :
    residualCondition data R (mu * R / 2) =
      2 * data.Lp * R ^ (data.p - 1) / mu := by
  have hR0 : R ≠ 0 := hR.ne'
  have hmu0 : mu ≠ 0 := hmu.ne'
  have hp : 1 ≤ data.p := le_trans (by omega : 1 ≤ 2) data.p_ge_two
  rw [residualCondition]
  rw [show R ^ data.p = R ^ (data.p - 1) * R by
    rw [← pow_succ]; congr; omega]
  field_simp

/-- Radius halving preserves positivity and the public diameter bound. -/
theorem restart_radius_halving
    (data : VIPublicData E) (R : ℝ) (hR : 0 < R) (hRD : R ≤ data.D) :
    0 < R / 2 ∧ R / 2 ≤ data.D := by
  constructor
  · positivity
  · exact (div_le_self hR.le (by norm_num)).trans hRD

section ExecutableTrial

/-- Embed a residual-solver call with its own local cap.  Local exhaustion is
an explicit failure value, so an enclosing radius-guess wrapper may safely
abandon the trial. -/
def residualSubcallProgram (data : VIPublicData E) (A : ResidualSolver data)
    (center : data.X) (R epsilon : ℝ) :
    ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data) :=
  let call := A.solve center R epsilon
  call.program.locallyCapped call.cap

/-- A finite `RestartTrial` syntax tree. `halvings` nonfinal calls use
accuracy `mu*R/2`; the final call uses `delta`. Returned points determine the
next centers, exactly as in the source algorithm. -/
def restartTrialProgram (data : VIPublicData E) (A : ResidualSolver data)
    (mu delta : ℝ) :
    (halvings : ℕ) → (center : data.X) → (R : ℝ) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data)
  | 0, center, R => residualSubcallProgram data A center R delta
  | halvings + 1, center, R =>
      (residualSubcallProgram data A center R (mu * R / 2)).bind
        (fun cert => restartTrialProgram data A mu delta halvings cert.point (R / 2))

/-- Public, center-independent enclosing cap.  It is the sum of ceilings of
the interface bounds of every descendant call. -/
def restartTrialCap (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ) : ℕ → ℝ → ℕ
  | 0, R => ⌈residualInterfaceCost data A.leadingConstant alpha b R delta⌉₊
  | halvings + 1, R =>
      ⌈residualInterfaceCost data A.leadingConstant alpha b R (mu * R / 2)⌉₊ +
        restartTrialCap data A alpha b mu delta halvings (R / 2)

/-- The executable capped call for one guessed initial radius. -/
def restartTrialCall (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ)
    (halvings : ℕ) (center : data.X) (R : ℝ) : CappedExactJetCall data where
  cap := restartTrialCap data A alpha b mu delta halvings R
  program := restartTrialProgram data A mu delta halvings center R

theorem residualSubcall_cap_le_interfaceCeil
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (center : data.X) (R epsilon : ℝ)
    (hR : 0 < R) (hRD : R ≤ data.D) (hepsilon : 0 < epsilon) :
    (A.solve center R epsilon).cap ≤
      ⌈residualInterfaceCost data A.leadingConstant alpha b R epsilon⌉₊ := by
  have hcap := hA.1 center R epsilon hR hRD hepsilon
  exact_mod_cast hcap.trans (Nat.le_ceil _)

/-- Big-step trace of the executable restart trial.  Every node records the
actual fuelled execution of one locally capped `A` call and the total original
oracle count of all descendants. -/
inductive RestartTrialTrace (data : VIPublicData E) (A : ResidualSolver data)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) :
    ℕ → data.X → ℝ → ℕ → EvaluatedNormalCertificate data → Prop where
  | final (center : data.X) (R : ℝ) (used : ℕ)
      (cert : EvaluatedNormalCertificate data)
      (hrun : (A.solve center R delta).execute data G oracle =
        .finished used (some cert)) :
      RestartTrialTrace data A G oracle mu delta 0 center R used cert
  | step (halvings : ℕ) (center : data.X) (R : ℝ)
      (usedHead usedTail : ℕ)
      (headCert finalCert : EvaluatedNormalCertificate data)
      (hhead : (A.solve center R (mu * R / 2)).execute data G oracle =
        .finished usedHead (some headCert))
      (htail : RestartTrialTrace data A G oracle mu delta halvings
        headCert.point (R / 2) usedTail finalCert) :
      RestartTrialTrace data A G oracle mu delta (halvings + 1) center R
        (usedHead + usedTail) finalCert

/-- A valid initial promise generates a successful finite restart trace for
every prescribed number of halvings. -/
theorem restartTrialTrace_exists
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (halvings : ℕ) (center : data.X) (R : ℝ)
    (hR : 0 < R) (hRD : R ≤ data.D)
    (hpromise : ‖center.1 - zStar‖ ≤ R) :
    ∃ used cert,
      RestartTrialTrace data A G oracle mu delta halvings center R used cert ∧
      cert.IsVerifiedFor data G delta := by
  induction halvings generalizing center R with
  | zero =>
      obtain ⟨used, cert, hrun, hcert, _hcost⟩ :=
        residualSolver_final_call data A alpha b hA G oracle hG R delta
          hR hRD hdelta zStar hz center hpromise
      exact ⟨used, cert, .final center R used cert hrun, hcert⟩
  | succ halvings ih =>
      obtain ⟨usedHead, headCert, hhead, hheadCert, hhalf, _hcost⟩ :=
        residualSolver_call_halves data A alpha b hA G oracle hG mu R
          hmu hR hRD hstrong zStar hz center hpromise
      obtain ⟨hRhalf, hRDhalf⟩ := restart_radius_halving data R hR hRD
      obtain ⟨usedTail, finalCert, htail, hfinal⟩ :=
        ih headCert.point (R / 2) hRhalf hRDhalf hhalf
      exact ⟨usedHead + usedTail, finalCert,
        .step halvings center R usedHead usedTail headCert finalCert hhead htail,
        hfinal⟩

theorem RestartTrialTrace.evaluates
    (data : VIPublicData E) (A : ResidualSolver data)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) {halvings : ℕ} {center : data.X} {R : ℝ}
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (htrace : RestartTrialTrace data A G oracle mu delta
      halvings center R used cert) :
    ExactJetProgram.Evaluates oracle.answer
      (restartTrialProgram data A mu delta halvings center R) used (some cert) := by
  induction htrace with
  | final center R used cert hrun =>
      have heval := ExactJetProgram.evaluates_of_runWithFuel_finished hrun
      have hused := CappedExactJetCall.finished_queries_le_cap
        data G oracle (A.solve center R delta) hrun
      exact heval.locallyCapped hused
  | step halvings center R usedHead usedTail headCert finalCert hhead htail ih =>
      have hheadEval := ExactJetProgram.evaluates_of_runWithFuel_finished hhead
      have hheadUsed := CappedExactJetCall.finished_queries_le_cap
        data G oracle (A.solve center R (mu * R / 2)) hhead
      exact (hheadEval.locallyCapped hheadUsed).bind ih

theorem RestartTrialTrace.used_le_cap
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    {halvings : ℕ} {center : data.X} {R : ℝ}
    (hR : 0 < R) (hRD : R ≤ data.D)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (htrace : RestartTrialTrace data A G oracle mu delta
      halvings center R used cert) :
    used ≤ restartTrialCap data A alpha b mu delta halvings R := by
  induction htrace with
  | final center R used cert hrun =>
      exact (CappedExactJetCall.finished_queries_le_cap
        data G oracle (A.solve center R delta) hrun).trans
          (residualSubcall_cap_le_interfaceCeil data A alpha b hA center R delta
            hR hRD hdelta)
  | step halvings center R usedHead usedTail headCert finalCert hhead htail ih =>
      have hheadLe : usedHead ≤
          ⌈residualInterfaceCost data A.leadingConstant alpha b R
            (mu * R / 2)⌉₊ :=
        (CappedExactJetCall.finished_queries_le_cap data G oracle
          (A.solve center R (mu * R / 2)) hhead).trans
          (residualSubcall_cap_le_interfaceCeil data A alpha b hA center R
            (mu * R / 2) hR hRD (by positivity))
      obtain ⟨hRhalf, hRDhalf⟩ := restart_radius_halving data R hR hRD
      exact Nat.add_le_add hheadLe (ih hRhalf hRDhalf)

/-- The flattened syntax tree and its enclosing cap execute to the same final
certificate recorded by a successful restart trace. -/
theorem RestartTrialTrace.execute
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    {halvings : ℕ} {center : data.X} {R : ℝ}
    (hR : 0 < R) (hRD : R ≤ data.D)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (htrace : RestartTrialTrace data A G oracle mu delta
      halvings center R used cert) :
    (restartTrialCall data A alpha b mu delta halvings center R).execute
      data G oracle = .finished used (some cert) := by
  exact htrace.evaluates data A G oracle mu delta |>.runWithFuel_eq
    (htrace.used_le_cap data A alpha b hA G oracle mu delta hmu hdelta hR hRD)

theorem restartTrialCall_succeeds
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (hA : A.SatisfiesInterface data alpha b)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (halvings : ℕ) (center : data.X) (R : ℝ)
    (hR : 0 < R) (hRD : R ≤ data.D)
    (hpromise : ‖center.1 - zStar‖ ≤ R) :
    ∃ used cert,
      (restartTrialCall data A alpha b mu delta halvings center R).execute
          data G oracle = .finished used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ restartTrialCap data A alpha b mu delta halvings R := by
  obtain ⟨used, cert, htrace, hcert⟩ := restartTrialTrace_exists data A alpha b
    hA G oracle hG mu delta hmu hdelta hstrong zStar hz halvings center R
    hR hRD hpromise
  exact ⟨used, cert,
    htrace.execute data A alpha b hA G oracle mu delta hmu hdelta hR hRD,
    hcert,
    htrace.used_le_cap data A alpha b hA G oracle mu delta hmu hdelta hR hRD⟩

end ExecutableTrial

end

end LeanArticleAudit.Pilot
