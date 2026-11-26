import LeanArticleAudit.Pilot.UpperHalvingTrace
import LeanArticleAudit.Pilot.ModelExistenceClaim

open Set
open scoped RealInnerProductSpace BigOperators

namespace LeanArticleAudit.Pilot
noncomputable section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem knownModelStep_correction_bound
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (x : data.X) (r : ℝ)
    (zStar : E) (hz : IsVISolution data G zStar)
    (hradius : ‖x.1 - zStar‖ ≤ r)
    (hspec : IsKnownModelStep data x (oracle.answer x)
      (knownModelStep data x (oracle.answer x))) :
    let yn := knownModelStep data x (oracle.answer x)
    ‖G yn.1.1 + yn.2‖ ≤ correctionConstant data.p * data.Lp * r ^ data.p := by
  dsimp only
  let yn := knownModelStep data x (oracle.answer x)
  let y : E := yn.1.1
  let n : E := yn.2
  let err : E := G y - taylorModel data.p G x.1 y
  have hy : y ∈ data.X := yn.1.2
  have hn : n ∈ normalCone data.X y := hspec.1
  have hmodel : G y + n = err -
      ((2 * (data.p : ℝ) / data.p.factorial) * data.Lp *
        ‖y - x.1‖ ^ (data.p - 1)) • (y - x.1) := by
    have heq := hspec.2
    rw [taylorModelFromJet_feasible_exact data G oracle x y] at heq
    dsimp [yn, y, n, err] at *
    unfold tensorBetaCoefficient at heq
    calc
      G y + n = (G y - taylorModel data.p G x.1 y) +
          (taylorModel data.p G x.1 y +
            ((2 * (data.p : ℝ) / data.p.factorial) * data.Lp *
              ‖y - x.1‖ ^ (data.p - 1)) • (y - x.1) + n) -
          ((2 * (data.p : ℝ) / data.p.factorial) * data.Lp *
            ‖y - x.1‖ ^ (data.p - 1)) • (y - x.1) := by module
      _ = (G y - taylorModel data.p G x.1 y) -
          ((2 * (data.p : ℝ) / data.p.factorial) * data.Lp *
            ‖y - x.1‖ ^ (data.p - 1)) • (y - x.1) := by rw [heq]; module
  obtain ⟨U, hU, hXU, hreg⟩ := hG.regularity
  have htaylor : ‖err‖ ≤ data.Lp / data.p.factorial * ‖y - x.1‖ ^ data.p := by
    have ht := taylorRemainderClaim_proof data.p data.Lp data.X U G
      data.p_ge_two data.Lp_pos.le hU hXU data.X_convex hreg
      hG.top_derivative_lipschitz x x.2 y hy
    exact ht.1
  exact (lem_correction data.X G data.p data.p_ge_two data.Lp r data.Lp_pos
    x.1 y zStar n err hy hz.1 hz.2 hG.monotone_on hradius hn hmodel htaylor).2

theorem correctionProgram_succeeds_of_radius
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (x : data.X) (r delta : ℝ)
    (zStar : E) (hz : IsVISolution data G zStar)
    (hradius : ‖x.1 - zStar‖ ≤ r)
    (hthreshold : correctionConstant data.p * data.Lp * r ^ data.p ≤ delta)
    (hspec : IsKnownModelStep data x (oracle.answer x)
      (knownModelStep data x (oracle.answer x))) :
    ∃ cert, ExactJetProgram.Evaluates oracle.answer
      (correctionProgram data x delta) 2 (some cert) ∧
      cert.IsVerifiedFor data G delta := by
  classical
  let yn := knownModelStep data x (oracle.answer x)
  let cert : EvaluatedNormalCertificate data := {
    point := yn.1
    normal := yn.2
    value := symmetricJetValue data (oracle.answer yn.1) }
  have hn : cert.normal ∈ normalCone data.X cert.point.1 := hspec.1
  have hbound := knownModelStep_correction_bound data G oracle hG x r zStar hz
    hradius hspec
  have hres : ‖cert.value + cert.normal‖ ≤ delta := by
    change ‖symmetricJetValue data (oracle.answer yn.1) + yn.2‖ ≤ delta
    rw [symmetricJetValue_feasible_exact data G oracle yn.1]
    exact hbound.trans hthreshold
  have heval : ExactJetProgram.Evaluates oracle.answer
      (correctionProgram data x delta) 2 (some cert) := by
    simp only [correctionProgram]
    apply ExactJetProgram.Evaluates.query
    change ExactJetProgram.Evaluates oracle.answer
      (.query yn.1 fun jety =>
        let cert' : EvaluatedNormalCertificate data := {
          point := yn.1, normal := yn.2, value := symmetricJetValue data jety }
        if hn' : cert'.normal ∈ normalCone data.X cert'.point.1 then
          if hres' : ‖cert'.value + cert'.normal‖ ≤ delta then .halt (some cert')
          else .halt none
        else .halt none) 1 (some cert)
    apply ExactJetProgram.Evaluates.query
    dsimp only
    split
    · exact .halt _
    · contradiction
  exact ⟨cert, heval, hn, symmetricJetValue_feasible_exact data G oracle yn.1, hres⟩

/-- Source-facing executable `prop:halving`: the genuine stabilized Taylor
model selector discharges the remaining per-query model premise. -/
theorem prop_halving
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu r : ℝ) (hmu : 0 < mu) (hr : 0 < r)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (hcenter : ‖center.1 - zStar‖ ≤ r) :
    ∃ used out,
      ExactJetProgram.Evaluates oracle.answer (halvingProgram data center mu r)
        used (some out) ∧
      used ≤ 2 * halvingIterationCount data.p data.Lp r mu ∧
      out.point ∈ data.X ∧ ‖out.point - zStar‖ ≤ r / 2 := by
  apply halvingProgram_succeeds_and_halves_of_model_spec data G oracle hG center
    mu r hmu hr hstrong zStar hz hcenter
  intro i hi
  exact knownModelStep_genuine_spec data G hG oracle _


/-- Every genuinely executed base trial succeeds once its final scheduled
radius meets the correction threshold. -/
theorem baseTrialProgram_succeeds
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (halvings : ℕ) (center : data.X) (R : ℝ)
    (hR : 0 < R) (hcenter : ‖center.1 - zStar‖ ≤ R)
    (hthreshold : correctionConstant data.p * data.Lp *
      (R / (2 : ℝ) ^ halvings) ^ data.p ≤ delta) :
    ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (baseTrialProgram data mu delta halvings center R) used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ baseTrialCap data mu halvings R := by
  induction halvings generalizing center R with
  | zero =>
      have hthreshold' : correctionConstant data.p * data.Lp * R ^ data.p ≤ delta := by
        simpa using hthreshold
      obtain ⟨cert, heval, hcert⟩ := correctionProgram_succeeds_of_radius
        data G oracle hG center R delta zStar hz hcenter hthreshold'
          (knownModelStep_genuine_spec data G hG oracle center)
      exact ⟨2, cert, heval, hcert, by simp [baseTrialCap]⟩
  | succ n ih =>
      obtain ⟨used₁, out, hhalve, hused₁, houtmem, houtclose⟩ :=
        prop_halving data G oracle hG center mu R hmu hR hstrong zStar hz hcenter
      let nextCenter : data.X := ⟨out.point, houtmem⟩
      have hRhalf : 0 < R / 2 := by positivity
      have hthreshold' : correctionConstant data.p * data.Lp *
          ((R / 2) / (2 : ℝ) ^ n) ^ data.p ≤ delta := by
        convert hthreshold using 1 <;> rw [pow_succ] <;> ring
      obtain ⟨used₂, cert, hrec, hcert, hused₂⟩ := ih nextCenter (R / 2)
        hRhalf (by simpa [nextCenter] using houtclose) hthreshold'
      have heval : ExactJetProgram.Evaluates oracle.answer
          (baseTrialProgram data mu delta (n + 1) center R)
          (used₁ + used₂) (some cert) := by
        rw [baseTrialProgram]
        apply ExactJetProgram.Evaluates.bind hhalve
        simpa [houtmem, nextCenter] using hrec
      refine ⟨used₁ + used₂, cert, heval, hcert, ?_⟩
      rw [baseTrialCap]
      omega


theorem ExactJetProgram.locallyCapped_total
    {X Answer Output : Type*} (oracle : X → Answer)
    (program : ExactJetProgram X Answer Output) (cap : ℕ) :
    ∃ used result, ExactJetProgram.Evaluates oracle
      (program.locallyCapped cap) used result ∧ used ≤ cap := by
  induction cap generalizing program with
  | zero =>
      cases program with
      | halt result => exact ⟨0, result, .halt _, le_rfl⟩
      | query point next => exact ⟨0, none, .halt _, le_rfl⟩
  | succ cap ih =>
      cases program with
      | halt result => exact ⟨0, result, .halt _, Nat.zero_le _⟩
      | query point next =>
          obtain ⟨used, result, heval, hused⟩ := ih (next (oracle point))
          exact ⟨used + 1, result, .query point _ used result heval, by omega⟩

theorem ExactJetProgram.evaluates_orElse_of_none
    {X Answer Output : Type*} {oracle : X → Answer}
    {first fallback : ExactJetProgram X Answer Output}
    {used₁ used₂ : ℕ} {result : Option Output}
    (hfirst : ExactJetProgram.Evaluates oracle first used₁ none)
    (hfallback : ExactJetProgram.Evaluates oracle fallback used₂ result) :
    ExactJetProgram.Evaluates oracle (first.orElse fallback)
      (used₁ + used₂) result := by
  induction first generalizing used₁ with
  | halt outcome =>
      cases outcome <;> cases hfirst
      simpa [ExactJetProgram.orElse] using hfallback
  | query point next ih =>
      cases hfirst with
      | query _ _ used _ hnext =>
          simp only [ExactJetProgram.orElse]
          convert ExactJetProgram.Evaluates.query point
            (fun answer => (next answer).orElse fallback)
            (used + used₂) result (ih _ hnext) using 1 <;> omega

theorem ExactJetProgram.evaluates_orElse_of_some
    {X Answer Output : Type*} {oracle : X → Answer}
    {first fallback : ExactJetProgram X Answer Output}
    {used : ℕ} {value : Output}
    (hfirst : ExactJetProgram.Evaluates oracle first used (some value)) :
    ExactJetProgram.Evaluates oracle (first.orElse fallback) used (some value) := by
  induction first generalizing used with
  | halt outcome =>
      cases outcome <;> cases hfirst
      exact .halt _
  | query point next ih =>
      cases hfirst with
      | query _ _ childUsed _ hnext =>
          exact .query point _ childUsed _ (ih _ hnext)

/-- If the trial at offset `target` succeeds within its local cap, the public
adaptive wrapper succeeds no later than that trial. -/
theorem adaptiveBaseProgramFrom_succeeds_at_offset
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) (center : data.X)
    (remaining j target : ℕ) (htarget : target ≤ remaining)
    (htrial : ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (scheduledBaseTrialCall data mu delta center
          (adaptiveGuessRadius data mu (j + target))).program used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ (scheduledBaseTrialCall data mu delta center
        (adaptiveGuessRadius data mu (j + target))).cap) :
    ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (adaptiveBaseProgramFrom data mu delta center remaining j)
        used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ adaptiveBaseCapFrom data mu delta center target j := by
  induction remaining generalizing j target with
  | zero =>
      have ht : target = 0 := by omega
      subst target
      obtain ⟨used, cert, heval, hcert, hused⟩ := htrial
      refine ⟨used, cert, ?_, hcert, ?_⟩
      · simpa [adaptiveBaseProgramFrom] using heval.locallyCapped hused
      · simpa [adaptiveBaseCapFrom] using hused
  | succ remaining ih =>
      cases target with
      | zero =>
        obtain ⟨used, cert, heval, hcert, hused⟩ := htrial
        have hlocal := heval.locallyCapped hused
        refine ⟨used, cert, ?_, hcert, ?_⟩
        · simp only [adaptiveBaseProgramFrom]
          exact ExactJetProgram.evaluates_orElse_of_some hlocal
        · simpa [adaptiveBaseCapFrom] using hused
      | succ target =>
        let call := scheduledBaseTrialCall data mu delta center
          (adaptiveGuessRadius data mu j)
        obtain ⟨used₁, result₁, hfirst, hused₁⟩ :=
          ExactJetProgram.locallyCapped_total oracle.answer call.program call.cap
        cases result₁ with
        | some cert₁ =>
            have hcert₁ : cert₁.IsVerifiedFor data G delta :=
              scheduledBaseTrialCall_no_false_success data G oracle mu delta center _
                ((ExactJetProgram.evaluation_of_locallyCapped_success'
                  oracle.answer call.program call.cap used₁ cert₁ hfirst).1.runWithFuel_eq
                  (ExactJetProgram.evaluation_of_locallyCapped_success'
                    oracle.answer call.program call.cap used₁ cert₁ hfirst).2)
            refine ⟨used₁, cert₁, ExactJetProgram.evaluates_orElse_of_some hfirst,
              hcert₁, ?_⟩
            simpa [adaptiveBaseCapFrom, call] using
              hused₁.trans (Nat.le_add_right _ _)
        | none =>
            have htrial' : ∃ used cert,
                ExactJetProgram.Evaluates oracle.answer
                  (scheduledBaseTrialCall data mu delta center
                    (adaptiveGuessRadius data mu ((j + 1) + target))).program
                  used (some cert) ∧ cert.IsVerifiedFor data G delta ∧
                used ≤ (scheduledBaseTrialCall data mu delta center
                  (adaptiveGuessRadius data mu ((j + 1) + target))).cap := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrial
            obtain ⟨used₂, cert, htail, hcert, hused₂⟩ :=
              ih (j + 1) target (by omega) htrial'
            refine ⟨used₁ + used₂, cert,
              ?_, hcert, ?_⟩
            · simp only [adaptiveBaseProgramFrom]
              exact ExactJetProgram.evaluates_orElse_of_none hfirst htail
            · simp only [adaptiveBaseCapFrom]
              change used₁ + used₂ ≤ call.cap +
                adaptiveBaseCapFrom data mu delta center target (j + 1)
              omega

theorem scheduledBaseTrialProgram_succeeds
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu delta : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (center : data.X) (R : ℝ) (hR : 0 < R)
    (hcenter : ‖center.1 - zStar‖ ≤ R) :
    ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (scheduledBaseTrialCall data mu delta center R).program used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ (scheduledBaseTrialCall data mu delta center R).cap := by
  unfold scheduledBaseTrialCall baseTrialCall
  exact baseTrialProgram_succeeds data G oracle hG mu delta hmu hdelta hstrong
    zStar hz (baseHalvingCount data R delta) center R hR hcenter
      (baseHalvingCount_threshold data R delta hR.le hdelta)

/-- The concrete adaptive base solver always reaches the last public radius
`D`; therefore it succeeds without receiving the unknown solution distance. -/
theorem adaptiveBaseCall_succeeds
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar) :
    ∃ used cert,
      (adaptiveBaseCall data center mu delta).execute data G oracle =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ (adaptiveBaseCall data center mu delta).cap := by
  have hcenterD : ‖center.1 - zStar‖ ≤ data.D := by
    simpa [dist_eq_norm] using data.diameter_le center.1 center.2 zStar hz.1
  have hlast := scheduledBaseTrialProgram_succeeds data G oracle hG mu delta
    hmu hdelta hstrong zStar hz center data.D data.D_pos hcenterD
  have hlast' : ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (scheduledBaseTrialCall data mu delta center
          (adaptiveGuessRadius data mu (0 + adaptiveGuessCount data mu))).program
        used (some cert) ∧ cert.IsVerifiedFor data G delta ∧
      used ≤ (scheduledBaseTrialCall data mu delta center
        (adaptiveGuessRadius data mu (0 + adaptiveGuessCount data mu))).cap := by
    simpa [adaptiveGuessRadius_last data mu hmu] using hlast
  obtain ⟨used, cert, heval, hcert, hused⟩ :=
    adaptiveBaseProgramFrom_succeeds_at_offset data G oracle mu delta center
      (adaptiveGuessCount data mu) 0 (adaptiveGuessCount data mu) le_rfl hlast'
  refine ⟨used, cert, ?_, hcert, ?_⟩
  · exact heval.runWithFuel_eq hused
  · exact hused

theorem baseStrongSolver_succeeds
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar) :
    ∃ used cert,
      ((baseStrongSolver data).solve center mu delta).execute data G oracle =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ ((baseStrongSolver data).solve center mu delta).cap := by
  exact adaptiveBaseCall_succeeds data G oracle hG center mu delta hmu hdelta
    hstrong zStar hz


theorem adaptiveBaseCapFrom_mono_remaining (data : VIPublicData E)
    (mu delta : ℝ) (center : data.X) (j small large : ℕ)
    (h : small ≤ large) :
    adaptiveBaseCapFrom data mu delta center small j ≤
      adaptiveBaseCapFrom data mu delta center large j := by
  induction large generalizing small j with
  | zero =>
      have : small = 0 := by omega
      subst small
      exact le_rfl
  | succ large ih =>
      cases small with
      | zero =>
          simp only [adaptiveBaseCapFrom]
          exact Nat.le_add_right _ _
      | succ small =>
          simp only [adaptiveBaseCapFrom]
          exact Nat.add_le_add_left (ih (j + 1) small (by omega)) _

theorem adaptiveGuessRadius_pos (data : VIPublicData E) (mu : ℝ)
    (hmu : 0 < mu) (j : ℕ) :
    0 < adaptiveGuessRadius data mu j := by
  unfold adaptiveGuessRadius
  exact lt_min data.D_pos (mul_pos (by positivity) (baseStrongScale_pos data mu hmu))

/-- Sharp executable bridge: if any installed guess covers the unknown true
distance, the actual solver stops by that guess and pays only the prefix cap. -/
theorem baseStrongSolver_succeeds_at_guess
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (j : ℕ) (hj : j ≤ adaptiveGuessCount data mu)
    (hcover : ‖center.1 - zStar‖ ≤ adaptiveGuessRadius data mu j) :
    ∃ used cert,
      ((baseStrongSolver data).solve center mu delta).execute data G oracle =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ adaptiveBaseCapFrom data mu delta center j 0 := by
  have htrial := scheduledBaseTrialProgram_succeeds data G oracle hG mu delta
    hmu hdelta hstrong zStar hz center (adaptiveGuessRadius data mu j)
      (adaptiveGuessRadius_pos data mu hmu j) hcover
  obtain ⟨used, cert, heval, hcert, hused⟩ :=
    adaptiveBaseProgramFrom_succeeds_at_offset data G oracle mu delta center
      (adaptiveGuessCount data mu) 0 j hj (by simpa using htrial)
  have hprefix := adaptiveBaseCapFrom_mono_remaining data mu delta center 0 j
    (adaptiveGuessCount data mu) hj
  refine ⟨used, cert, ?_, hcert, hused⟩
  exact heval.runWithFuel_eq (hused.trans hprefix)


end
end LeanArticleAudit.Pilot
