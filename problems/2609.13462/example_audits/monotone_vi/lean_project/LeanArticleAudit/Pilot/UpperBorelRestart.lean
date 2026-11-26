import LeanArticleAudit.Pilot.UpperBorelBoostRestart
import LeanArticleAudit.Pilot.UpperBorelOrElse
import LeanArticleAudit.Pilot.UpperBorelBase

/-!
# Joint Borel preservation for certified restart

The input invariant is stated for the *actually locally capped* residual
subcall.  This is essential because a solver's declared cap may depend on its
center, even when its uncapped program is jointly Borel.
-/

open Set MeasureTheory

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Restart

variable (data : VIPublicData E) (A : ResidualSolver data)

local instance restartCertificateMeasurableSpace :
    MeasurableSpace (EvaluatedNormalCertificate data) :=
  upperEvaluatedNormalCertificateMeasurableSpace data

local instance restartFeasibleInhabited : Inhabited data.X :=
  ⟨⟨Classical.choose data.X_nonempty,
    Classical.choose_spec data.X_nonempty⟩⟩

theorem measurable_restartCertificate_point :
    Measurable (EvaluatedNormalCertificate.point :
      EvaluatedNormalCertificate data → data.X) := by
  have h := measurable_evaluatedNormalCertificate_point data
  rw [← upperFeasible_measurable_eq_normBorel data] at h
  exact h

/-- A finite restart trial preserves joint outcome measurability, provided
every residual child is measurable after installing its own actual cap. -/
theorem restartTrialProgram_isJointlyBorelOutcome
    (hA : ∀ (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
        residualSubcallProgram data A center R epsilon))
    (mu delta : ℝ) (halvings : ℕ) (R : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      restartTrialProgram data A mu delta halvings center R) := by
  induction halvings generalizing R with
  | zero => simpa [restartTrialProgram] using hA R delta
  | succ halvings ih =>
      have hfirst := hA R (mu * R / 2)
      let next : data.X × EvaluatedNormalCertificate data →
          ExactJetProgram data.X (SymmetricExactJet E data.p)
            (EvaluatedNormalCertificate data) := fun q =>
        restartTrialProgram data A mu delta halvings q.2.point (R / 2)
      have hnext : ExactJetProgram.IsJointlyBorelOutcome next :=
        (ih (R / 2)).compParameter
          (fun q : data.X × EvaluatedNormalCertificate data => q.2.point)
          ((measurable_restartCertificate_point data).comp measurable_snd)
      have hbind := hfirst.bind hnext
      simpa [restartTrialProgram, residualSubcallProgram, next] using hbind

/-- The public stopping-count schedule and the trial's outer cap are fixed
once `(mu,delta,R)` are fixed, hence the scheduled child remains center-joint
Borel. -/
theorem scheduledRestartTrialProgram_isJointlyBorelOutcome
    (hA : ∀ (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
        residualSubcallProgram data A center R epsilon))
    (alpha : ℝ) (b : ℕ) (mu delta R : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      (scheduledRestartTrialCall data A alpha b mu delta center R).program) := by
  simpa [scheduledRestartTrialCall, restartTrialCall] using
    restartTrialProgram_isJointlyBorelOutcome data A hA mu delta
      (restartHalvingCount mu delta R) R

theorem scheduledRestartTrialProgram_locallyCapped_isJointlyBorelOutcome
    (hA : ∀ (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
        residualSubcallProgram data A center R epsilon))
    (alpha : ℝ) (b : ℕ) (mu delta R : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      let call := scheduledRestartTrialCall data A alpha b mu delta center R
      call.program.locallyCapped call.cap) := by
  have htrial := scheduledRestartTrialProgram_isJointlyBorelOutcome data A hA
    alpha b mu delta R
  have hcapped := htrial.locallyCappedOutcome
    (restartTrialCap data A alpha b mu delta
      (restartHalvingCount mu delta R) R)
  simpa [scheduledRestartTrialCall, restartTrialCall] using hcapped

/-- The complete public-radius restart search preserves the same joint Borel
invariant. -/
theorem adaptiveRestartProgramFrom_isJointlyBorelOutcome
    (hA : ∀ (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
        residualSubcallProgram data A center R epsilon))
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ) (remaining j : ℕ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      adaptiveRestartProgramFrom data A alpha b mu delta center remaining j) := by
  induction remaining generalizing j with
  | zero =>
      simpa [adaptiveRestartProgramFrom] using
        scheduledRestartTrialProgram_locallyCapped_isJointlyBorelOutcome
          data A hA alpha b mu delta (adaptiveGuessRadius data mu j)
  | succ remaining ih =>
      let R := adaptiveGuessRadius data mu j
      have hfirst := scheduledRestartTrialProgram_isJointlyBorelOutcome
        data A hA alpha b mu delta R
      have hfallback := ih (j + 1)
      have h := hfirst.orElse_locallyCapped hfallback default
        (restartTrialCap data A alpha b mu delta
          (restartHalvingCount mu delta R) R)
      simpa [adaptiveRestartProgramFrom, scheduledRestartTrialCall,
        restartTrialCall, R] using h

theorem adaptiveRestartCall_isJointlyBorelOutcome
    (hA : ∀ (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
        residualSubcallProgram data A center R epsilon))
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      (adaptiveRestartCall data A alpha b center mu delta).program) := by
  simpa [adaptiveRestartCall] using
    adaptiveRestartProgramFrom_isJointlyBorelOutcome data A hA alpha b mu delta
      (adaptiveGuessCount data mu) 0

/-- The enclosing adaptive restart cap is independent of the solve center. -/
theorem adaptiveRestartCapFrom_center_eq
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ)
    (center₁ center₂ : data.X) (remaining j : ℕ) :
    adaptiveRestartCapFrom data A alpha b mu delta center₁ remaining j =
      adaptiveRestartCapFrom data A alpha b mu delta center₂ remaining j := by
  induction remaining generalizing j with
  | zero => rfl
  | succ remaining ih =>
      simp only [adaptiveRestartCapFrom]
      congr 1
      exact ih (j + 1)

/-- The fixed-data restart call remains jointly Borel after its advertised
outer hard cap is actually installed. -/
theorem adaptiveRestartCall_installed_isJointlyBorelOutcome
    (hA : ∀ (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
        residualSubcallProgram data A center R epsilon))
    (fallback : data.X) (alpha : ℝ) (b : ℕ) (mu delta : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      (adaptiveRestartCall data A alpha b center mu delta).installedProgram data) := by
  have h := (adaptiveRestartCall_isJointlyBorelOutcome data A hA alpha b mu delta).locallyCappedOutcome
    (adaptiveRestartCapFrom data A alpha b mu delta fallback
      (adaptiveGuessCount data mu) 0)
  have heq : (fun center : data.X =>
      (adaptiveRestartCall data A alpha b center mu delta).installedProgram data) =
      (fun center : data.X =>
        (adaptiveRestartCall data A alpha b center mu delta).program.locallyCapped
          (adaptiveRestartCapFrom data A alpha b mu delta fallback
            (adaptiveGuessCount data mu) 0)) := by
    funext center
    simp only [CappedExactJetCall.installedProgram, adaptiveRestartCall]
    rw [adaptiveRestartCapFrom_center_eq data A alpha b mu delta center fallback]
  rw [heq]
  exact h

end Restart

section RestartAnchored

local instance restartAnchoredCertificateMeasurableSpace
    (data : VIPublicData E) :
    MeasurableSpace (EvaluatedNormalCertificate data) :=
  upperCertificateMeasurableSpace data

local instance restartAnchoredFeasibleInhabited (data : VIPublicData E) :
    Inhabited data.X :=
  ⟨⟨Classical.choose data.X_nonempty,
    Classical.choose_spec data.X_nonempty⟩⟩

/-- The actually capped residual subcall, transported from a datum whose
starting point is the first state component back to the fixed ambient datum. -/
def transportedResidualSubcallProgram {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (R epsilon : ℝ)
    (state : data.X × data.X) :
    ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data) :=
  let shifted := data.withStart state.1
  let call := (family.atData shifted hp).solve state.2 R epsilon
  call.anchoredInstalledProgram data state.1

theorem transportedResidualSubcallProgram_isJointlyBorelOutcome {p : ℕ}
    (family : ResidualSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (transportedResidualSubcallProgram family data hp R epsilon) := by
  unfold transportedResidualSubcallProgram
  exact hfamily.anchored data hp R epsilon

omit [BorelSpace E] in
theorem transportedResidualSubcallProgram_eq {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (R epsilon : ℝ) (anchor center : data.X) :
    transportedResidualSubcallProgram family data hp R epsilon
        (anchor, center) =
      (residualSubcallProgram (data.withStart anchor)
        (family.atData (data.withStart anchor) hp) center R epsilon).bind
          (fun cert => .halt (some (cert.fromWithStart data anchor))) := by
  let shifted := data.withStart anchor
  let call := (family.atData shifted hp).solve center R epsilon
  change (call.program.bind (fun cert => .halt (some
      (cert.fromWithStart data anchor)))).locallyCapped call.cap =
    (call.program.locallyCapped call.cap).bind
      (fun cert => .halt (some (cert.fromWithStart data anchor)))
  exact ExactJetProgram.locallyCapped_bind_halt_some call.program
    (fun cert => cert.fromWithStart data anchor) call.cap

/-- A restart trial whose anchor and current center are both explicit Borel
parameters and whose terminal certificate is transported to the base datum. -/
def transportedRestartTrialProgram {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (mu delta : ℝ) :
    (halvings : ℕ) → (state : data.X × data.X) → (R : ℝ) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data)
  | 0, state, R =>
      transportedResidualSubcallProgram family data hp R delta state
  | halvings + 1, state, R =>
      (transportedResidualSubcallProgram family data hp R (mu * R / 2)
        state).bind (fun cert =>
          transportedRestartTrialProgram family data hp mu delta halvings
            (state.1, cert.point) (R / 2))

theorem transportedRestartTrialProgram_isJointlyBorelOutcome {p : ℕ}
    (family : ResidualSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ)
    (halvings : ℕ) (R : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun state : data.X × data.X =>
      transportedRestartTrialProgram family data hp mu delta
        halvings state R) := by
  have hpoint : Measurable
      (EvaluatedNormalCertificate.point :
        EvaluatedNormalCertificate data → data.X) := by
    have h := measurable_evaluatedNormalCertificate_point data
    rw [← upperFeasible_measurable_eq_normBorel data] at h
    exact h
  induction halvings generalizing R with
  | zero =>
      simpa [transportedRestartTrialProgram] using
        transportedResidualSubcallProgram_isJointlyBorelOutcome
          family hfamily data hp R delta
  | succ halvings ih =>
      have hfirst := transportedResidualSubcallProgram_isJointlyBorelOutcome
        family hfamily data hp R (mu * R / 2)
      let next : ((data.X × data.X) × EvaluatedNormalCertificate data) →
          ExactJetProgram data.X (SymmetricExactJet E data.p)
            (EvaluatedNormalCertificate data) := fun z =>
        transportedRestartTrialProgram family data hp mu delta halvings
          (z.1.1, z.2.point) (R / 2)
      have hnext : ExactJetProgram.IsJointlyBorelOutcome next :=
        (ih (R / 2)).compParameter
          (fun z : (data.X × data.X) × EvaluatedNormalCertificate data =>
            (z.1.1, z.2.point))
          ((measurable_fst.comp measurable_fst).prodMk
            (hpoint.comp measurable_snd))
      have hbind := hfirst.bind hnext
      simpa [transportedRestartTrialProgram, next] using hbind

theorem transportedRestartTrialProgram_eq {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (mu delta : ℝ) (halvings : ℕ)
    (anchor center : data.X) (R : ℝ) :
    transportedRestartTrialProgram family data hp mu delta halvings
        (anchor, center) R =
      (restartTrialProgram (data.withStart anchor)
        (family.atData (data.withStart anchor) hp) mu delta halvings center R).bind
          (fun cert => .halt (some (cert.fromWithStart data anchor))) := by
  let shifted := data.withStart anchor
  let A := family.atData shifted hp
  change transportedRestartTrialProgram family data hp mu delta halvings
      (anchor, center) R =
    (restartTrialProgram shifted A mu delta halvings center R).bind
      (fun cert => .halt (some (cert.fromWithStart data anchor)))
  induction halvings generalizing center R with
  | zero =>
      simpa [transportedRestartTrialProgram, restartTrialProgram] using
        transportedResidualSubcallProgram_eq family data hp R delta
          anchor center
  | succ halvings ih =>
      simp only [transportedRestartTrialProgram, restartTrialProgram]
      rw [transportedResidualSubcallProgram_eq]
      change
        (((residualSubcallProgram shifted A center R (mu * R / 2)).bind
            (fun cert => .halt (some
              (cert.fromWithStart data anchor)))).bind
          (fun cert => transportedRestartTrialProgram family data hp mu delta
            halvings (anchor, cert.point) (R / 2))) =
        ((residualSubcallProgram shifted A center R (mu * R / 2)).bind
          (fun cert => restartTrialProgram shifted A mu delta halvings
            cert.point (R / 2))).bind
          (fun cert => .halt (some (cert.fromWithStart data anchor)))
      conv_lhs => rw [ExactJetProgram.bind_assoc_eq]
      conv_rhs => rw [ExactJetProgram.bind_assoc_eq]
      congr 1
      funext cert
      simp only [ExactJetProgram.bind]
      change transportedRestartTrialProgram family data hp mu delta halvings
          (anchor, cert.point) (R / 2) =
        (restartTrialProgram shifted A mu delta halvings cert.point
          (R / 2)).bind
            (fun cert => .halt (some (cert.fromWithStart data anchor)))
      exact ih cert.point (R / 2)

omit [MeasurableSpace E] [BorelSpace E] in
theorem restartTrialCap_family_withStart_eq {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (anchor : data.X) (alpha : ℝ) (b : ℕ)
    (mu delta : ℝ) (halvings : ℕ) (R : ℝ) :
    restartTrialCap (data.withStart anchor)
        (family.atData (data.withStart anchor) hp) alpha b mu delta
        halvings R =
      restartTrialCap data (family.atData data hp) alpha b mu delta
        halvings R := by
  induction halvings generalizing R with
  | zero => rfl
  | succ halvings ih =>
      simp only [restartTrialCap]
      rw [ih]
      rfl

/-- Anchor-explicit adaptive restart search.  Every trial installs the same
actual cap as the corresponding legacy call. -/
def transportedAdaptiveRestartProgramFrom {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (alpha : ℝ) (b : ℕ) (mu delta : ℝ) :
    (remaining j : ℕ) → (state : data.X × data.X) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data)
  | 0, j, state =>
      let R := adaptiveGuessRadius data mu j
      let halvings := restartHalvingCount mu delta R
      (transportedRestartTrialProgram family data hp mu delta halvings
        state R).locallyCapped
          (restartTrialCap data (family.atData data hp) alpha b mu delta
            halvings R)
  | remaining + 1, j, state =>
      let R := adaptiveGuessRadius data mu j
      let halvings := restartHalvingCount mu delta R
      ExactJetProgram.orElse
        ((transportedRestartTrialProgram family data hp mu delta halvings
          state R).locallyCapped
            (restartTrialCap data (family.atData data hp) alpha b mu delta
              halvings R))
        (transportedAdaptiveRestartProgramFrom family data hp alpha b mu delta
          remaining (j + 1) state)

theorem transportedAdaptiveRestartProgramFrom_isJointlyBorelOutcome {p : ℕ}
    (family : ResidualSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p)
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ) (remaining j : ℕ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun state : data.X × data.X =>
      transportedAdaptiveRestartProgramFrom family data hp alpha b mu delta
        remaining j state) := by
  induction remaining generalizing j with
  | zero =>
      exact (transportedRestartTrialProgram_isJointlyBorelOutcome
        family hfamily data hp mu delta
          (restartHalvingCount mu delta (adaptiveGuessRadius data mu j))
          (adaptiveGuessRadius data mu j)).locallyCappedOutcome
            (restartTrialCap data (family.atData data hp) alpha b mu delta
              (restartHalvingCount mu delta (adaptiveGuessRadius data mu j))
              (adaptiveGuessRadius data mu j))
  | succ remaining ih =>
      let R := adaptiveGuessRadius data mu j
      let halvings := restartHalvingCount mu delta R
      have hfirst := transportedRestartTrialProgram_isJointlyBorelOutcome
        family hfamily data hp mu delta halvings R
      have hfallback := ih (j + 1)
      have h := hfirst.orElse_locallyCapped hfallback default
        (restartTrialCap data (family.atData data hp) alpha b mu delta
          halvings R)
      simpa [transportedAdaptiveRestartProgramFrom, R, halvings] using h

theorem transportedAdaptiveRestartProgramFrom_eq {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (alpha : ℝ) (b : ℕ) (mu delta : ℝ)
    (remaining j : ℕ) (anchor center : data.X) :
    transportedAdaptiveRestartProgramFrom family data hp alpha b mu delta
        remaining j (anchor, center) =
      (adaptiveRestartProgramFrom (data.withStart anchor)
        (family.atData (data.withStart anchor) hp) alpha b mu delta center
        remaining j).bind
          (fun cert => .halt (some (cert.fromWithStart data anchor))) := by
  let shifted := data.withStart anchor
  let A := family.atData shifted hp
  change transportedAdaptiveRestartProgramFrom family data hp alpha b mu delta
      remaining j (anchor, center) =
    (adaptiveRestartProgramFrom shifted A alpha b mu delta center
      remaining j).bind
        (fun cert => .halt (some (cert.fromWithStart data anchor)))
  induction remaining generalizing j with
  | zero =>
      let R := adaptiveGuessRadius data mu j
      have hR : adaptiveGuessRadius shifted mu j = R := by rfl
      simp only [transportedAdaptiveRestartProgramFrom,
        adaptiveRestartProgramFrom]
      rw [show adaptiveGuessRadius shifted mu j = R from hR]
      simp only [scheduledRestartTrialCall, restartTrialCall]
      let halvings := restartHalvingCount mu delta R
      change (transportedRestartTrialProgram family data hp mu delta
          halvings (anchor, center) R).locallyCapped
            (restartTrialCap data (family.atData data hp) alpha b mu delta
              halvings R) =
        ((restartTrialProgram shifted A mu delta halvings center R).locallyCapped
          (restartTrialCap shifted A alpha b mu delta halvings R)).bind
            (fun cert => .halt (some (cert.fromWithStart data anchor)))
      rw [transportedRestartTrialProgram_eq]
      change
        ((restartTrialProgram shifted A mu delta halvings center R).bind
          (fun cert => .halt (some
            (cert.fromWithStart data anchor)))).locallyCapped
              (restartTrialCap data (family.atData data hp) alpha b mu delta
                halvings R) =
          ((restartTrialProgram shifted A mu delta halvings center R).locallyCapped
            (restartTrialCap shifted A alpha b mu delta halvings R)).bind
              (fun cert => .halt (some
                (cert.fromWithStart data anchor)))
      rw [ExactJetProgram.locallyCapped_bind_halt_some]
      congr 2
      exact (restartTrialCap_family_withStart_eq family data hp anchor alpha b
        mu delta _ _).symm
  | succ remaining ih =>
      simp only [transportedAdaptiveRestartProgramFrom,
        adaptiveRestartProgramFrom, scheduledRestartTrialCall,
        restartTrialCall]
      rw [ExactJetProgram.orElse_bind_halt_some]
      congr 1
      · let R := adaptiveGuessRadius data mu j
        have hR : adaptiveGuessRadius shifted mu j = R := by rfl
        rw [show adaptiveGuessRadius shifted mu j = R from hR]
        let halvings := restartHalvingCount mu delta R
        change (transportedRestartTrialProgram family data hp mu delta
            halvings (anchor, center) R).locallyCapped
              (restartTrialCap data (family.atData data hp) alpha b mu delta
                halvings R) =
          ((restartTrialProgram shifted A mu delta halvings center R).locallyCapped
            (restartTrialCap shifted A alpha b mu delta halvings R)).bind
              (fun cert => .halt (some (cert.fromWithStart data anchor)))
        rw [transportedRestartTrialProgram_eq]
        change
          ((restartTrialProgram shifted A mu delta halvings center R).bind
            (fun cert => .halt (some
              (cert.fromWithStart data anchor)))).locallyCapped
                (restartTrialCap data (family.atData data hp) alpha b mu delta
                  halvings R) =
            ((restartTrialProgram shifted A mu delta halvings center R).locallyCapped
              (restartTrialCap shifted A alpha b mu delta halvings R)).bind
                (fun cert => .halt (some
                  (cert.fromWithStart data anchor)))
        rw [ExactJetProgram.locallyCapped_bind_halt_some]
        congr 2
        exact (restartTrialCap_family_withStart_eq family data hp anchor alpha b
          mu delta _ _).symm
      · exact ih (j + 1)

theorem adaptiveRestartCapFrom_family_withStart_eq {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (anchor : data.X) (alpha : ℝ) (b : ℕ)
    (mu delta : ℝ) (center : data.X) (remaining j : ℕ) :
    adaptiveRestartCapFrom (data.withStart anchor)
        (family.atData (data.withStart anchor) hp) alpha b mu delta center
        remaining j =
      adaptiveRestartCapFrom data (family.atData data hp) alpha b mu delta
        center remaining j := by
  induction remaining generalizing j with
  | zero =>
      simp only [adaptiveRestartCapFrom, scheduledRestartTrialCall,
        restartTrialCall]
      exact restartTrialCap_family_withStart_eq family data hp anchor alpha b
        mu delta _ _
  | succ remaining ih =>
      simp only [adaptiveRestartCapFrom, scheduledRestartTrialCall,
        restartTrialCall]
      congr 1
      · exact restartTrialCap_family_withStart_eq family data hp anchor alpha b
          mu delta _ _
      · exact ih (j + 1)

theorem adaptiveRestartCall_anchoredInstalled_eq {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (anchor center fallback : data.X)
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ) :
    let shifted := data.withStart anchor
    let call := adaptiveRestartCall shifted (family.atData shifted hp)
      alpha b center mu delta
    call.anchoredInstalledProgram data anchor =
      (transportedAdaptiveRestartProgramFrom family data hp alpha b mu delta
        (adaptiveGuessCount data mu) 0 (anchor, center)).locallyCapped
          (adaptiveRestartCapFrom data (family.atData data hp) alpha b mu delta
            fallback (adaptiveGuessCount data mu) 0) := by
  let shifted := data.withStart anchor
  let A := family.atData shifted hp
  let call := adaptiveRestartCall shifted A alpha b center mu delta
  have hcount : adaptiveGuessCount shifted mu = adaptiveGuessCount data mu := by
    rfl
  have hprogram := transportedAdaptiveRestartProgramFrom_eq family data hp
    alpha b mu delta (adaptiveGuessCount data mu) 0 anchor center
  have hcapStart := adaptiveRestartCapFrom_family_withStart_eq family data hp
    anchor alpha b mu delta center (adaptiveGuessCount data mu) 0
  have hcapCenter := adaptiveRestartCapFrom_center_eq data
    (family.atData data hp) alpha b mu delta center fallback
      (adaptiveGuessCount data mu) 0
  change
    ((adaptiveRestartProgramFrom shifted A alpha b mu delta center
      (adaptiveGuessCount shifted mu) 0).bind
        (fun cert => .halt (some (cert.fromWithStart data anchor)))).locallyCapped
          (adaptiveRestartCapFrom shifted A alpha b mu delta center
            (adaptiveGuessCount shifted mu) 0) = _
  rw [hcount]
  rw [← hprogram]
  congr 1
  exact hcapStart.trans hcapCenter

/-- Certified restart preserves the hierarchy's actual-cap, anchor-uniform
Borel outcome invariant. -/
theorem certifiedRestartFamily_hasJointBorelCappedOutcome {p : ℕ}
    (family : ResidualSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (alpha : ℝ) (b : ℕ) :
    (certifiedRestartFamily p family alpha b).HasJointBorelCappedOutcome := by
  constructor
  · intro E _ _ _ _ _ data hp mu delta
    let A := family.atData data hp
    have hsub : ∀ (R epsilon : ℝ),
        ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
          residualSubcallProgram data A center R epsilon) := by
      intro R epsilon
      simpa [A, residualSubcallProgram,
        CappedExactJetCall.installedProgram] using
        hfamily.ordinary data hp R epsilon
    let fallback : data.X := ⟨Classical.choose data.X_nonempty,
      Classical.choose_spec data.X_nonempty⟩
    simpa only [certifiedRestartFamily_atData_solve] using
      adaptiveRestartCall_installed_isJointlyBorelOutcome data A hsub fallback
        alpha b mu delta
  · intro E _ _ _ _ _ data hp mu delta
    let fallback : data.X := ⟨Classical.choose data.X_nonempty,
      Classical.choose_spec data.X_nonempty⟩
    let fixedCap := adaptiveRestartCapFrom data (family.atData data hp)
      alpha b mu delta fallback (adaptiveGuessCount data mu) 0
    have hraw :=
      transportedAdaptiveRestartProgramFrom_isJointlyBorelOutcome
        family hfamily data hp alpha b mu delta
          (adaptiveGuessCount data mu) 0
    have hcapped := hraw.locallyCappedOutcome fixedCap
    have heq : (fun state : data.X × data.X =>
        let shifted := data.withStart state.1
        let call := ((certifiedRestartFamily p family alpha b).atData
          shifted hp).solve state.2 mu delta
        call.anchoredInstalledProgram data state.1) =
      (fun state : data.X × data.X =>
        (transportedAdaptiveRestartProgramFrom family data hp alpha b mu delta
          (adaptiveGuessCount data mu) 0 state).locallyCapped fixedCap) := by
      funext state
      simpa only [certifiedRestartFamily_atData_solve] using
        adaptiveRestartCall_anchoredInstalled_eq family data hp state.1
          state.2 fallback alpha b mu delta
    rw [heq]
    exact hcapped

end RestartAnchored

end

end LeanArticleAudit.Pilot
