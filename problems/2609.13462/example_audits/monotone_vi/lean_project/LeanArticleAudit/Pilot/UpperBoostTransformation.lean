import LeanArticleAudit.Pilot.UpperBoostStrongLog

/-!
# Complete boost transformation

This file combines the executable Extrapolated--Halpern call with the scalar
cap bounds.  The resulting residual solver is fixed by public data and a
strong-solver family; neither the unknown operator nor a solution enters its
program or cap.
-/

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

def boostLeadingConstant (p : ℕ) (C : ℝ) (b : ℕ) : ℝ :=
  C * (20 * (p + 1 : ℝ)) ^ b * 2656003 + 2

theorem boostLeadingConstant_pos (p : ℕ) {C : ℝ} (hC : 0 < C) (b : ℕ) :
    0 < boostLeadingConstant p C b := by
  unfold boostLeadingConstant
  positivity

section ScalarCap

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual natural shared cap is bounded by the residual-interface cost,
including both ceiling units. -/
theorem boostSharedCap_le_residualInterfaceCost
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (R epsilon : ℝ) (hR : 0 < R) (hRD : R ≤ data.D)
    (hepsilon : 0 < epsilon)
    (ha23 : 2 / 3 ≤ ((data.p - 1 : ℕ) : ℝ) * gamma)
    (ha2 : ((data.p - 1 : ℕ) : ℝ) * gamma ≤ 2) :
    ((boostedResidualCall data S gamma b R epsilon).cap : ℝ) ≤
      residualInterfaceCost data
        (boostLeadingConstant data.p S.leadingConstant b)
        (boostAlpha gamma) (b + 4) R epsilon := by
  let K := boostHorizon data gamma R epsilon
  let eta := boostStepsize R epsilon K
  let e := boostOuterError R K
  let LA := residualLog data R epsilon
  let qa := Real.rpow (residualCondition data R epsilon) (boostAlpha gamma)
  let Cp := 20 * (data.p + 1 : ℝ)
  let work := K + 1 + Real.rpow (eta * data.Lp) gamma *
    Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) *
      boostUa (((data.p - 1 : ℕ) : ℝ) * gamma) K
  let core := S.leadingConstant * (strongLog data (1 / eta) (e / eta)) ^ b * work
  have hLA1 : 1 ≤ LA := by
    simpa [LA] using residualLog_one_le data R epsilon hR hepsilon
  have hLS := boost_strongLog_le_residualLog data gamma R epsilon hgamma hgamma1
    hR hRD hepsilon
  have hLS' : strongLog data (1 / eta) (e / eta) ≤ Cp * LA := by
    simpa [K, eta, e, Cp, LA] using hLS
  have hLS0 : 0 ≤ strongLog data (1 / eta) (e / eta) := by
    have heta : 0 < eta := by
      dsimp [eta]
      exact boostStepsize_pos hR hepsilon K
    have he : 0 < e := by
      dsimp [e]
      exact boostOuterError_pos hR K
    linarith [strongLog_one_le data (1 / eta) (e / eta) (by positivity)
      (div_pos he heta)]
  have hCpLA0 : 0 ≤ Cp * LA := by
    dsimp [Cp]
    positivity
  have hLSpow : (strongLog data (1 / eta) (e / eta)) ^ b ≤
      (Cp * LA) ^ b := pow_le_pow_left₀ hLS0 hLS' b
  have hwork := boost_work_factor_le data gamma R epsilon hgamma hgamma1 hR
    hepsilon ha23 ha2
  have hwork' : work ≤ 2656003 * (1 + qa) * LA ^ 4 := by
    simpa [K, eta, LA, qa, work] using hwork
  have hwork0 : 0 ≤ work := by
    dsimp [work]
    have hUa0 : 0 ≤ boostUa (((data.p - 1 : ℕ) : ℝ) * gamma) K := by
      unfold boostUa
      apply add_nonneg
      · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      · apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        apply Finset.sum_nonneg
        intro j hj
        exact mul_nonneg
          (Real.rpow_nonneg (by linarith [harmonicR_nonneg (2 ^ (j + 1))]) _)
          (Real.rpow_nonneg (by norm_num) _)
    apply add_nonneg
    · positivity
    · exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by
          exact mul_nonneg (boostStepsize_pos hR hepsilon K).le data.Lp_pos.le) _)
          (Real.rpow_nonneg hR.le _)) hUa0
  have hcore0 : 0 ≤ core := by
    dsimp [core]
    exact mul_nonneg
      (mul_nonneg S.leadingConstant_pos.le (pow_nonneg hLS0 b)) hwork0
  have hcore : core ≤
      S.leadingConstant * Cp ^ b * 2656003 * (1 + qa) * LA ^ (b + 4) := by
    calc
      core ≤ S.leadingConstant * (Cp * LA) ^ b *
          (2656003 * (1 + qa) * LA ^ 4) := by
        dsimp [core]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hLSpow S.leadingConstant_pos.le)
          hwork' hwork0
          (mul_nonneg S.leadingConstant_pos.le (pow_nonneg hCpLA0 b))
      _ = S.leadingConstant * Cp ^ b * 2656003 *
          (1 + qa) * LA ^ (b + 4) := by
        rw [mul_pow, pow_add]
        ring
  have htarget0 : 1 ≤ (1 + qa) * LA ^ (b + 4) := by
    have hqa0 : 0 ≤ qa := Real.rpow_nonneg (by
      unfold residualCondition
      exact (div_pos (mul_pos data.Lp_pos (pow_pos hR _)) hepsilon).le) _
    have hpow1 : 1 ≤ LA ^ (b + 4) := one_le_pow₀ hLA1
    calc
      1 = 1 * 1 := by ring
      _ ≤ (1 + qa) * LA ^ (b + 4) :=
        mul_le_mul (by linarith) hpow1 (by norm_num) (by linarith)
  have hceil : ((Nat.ceil core : ℕ) : ℝ) < core + 1 := Nat.ceil_lt_add_one hcore0
  change ((Nat.ceil core + 1 : ℕ) : ℝ) ≤
    boostLeadingConstant data.p S.leadingConstant b * (1 + qa) * LA ^ (b + 4)
  push_cast
  unfold boostLeadingConstant
  calc
    (Nat.ceil core : ℝ) + 1 ≤ core + 2 := by linarith
    _ ≤ (S.leadingConstant * Cp ^ b * 2656003 + 2) *
        ((1 + qa) * LA ^ (b + 4)) := by
      calc
        core + 2 ≤ S.leadingConstant * Cp ^ b * 2656003 *
            (1 + qa) * LA ^ (b + 4) + 2 := by linarith
        _ ≤ (S.leadingConstant * Cp ^ b * 2656003 + 2) *
            ((1 + qa) * LA ^ (b + 4)) := by
          nlinarith
    _ = _ := by ring

end ScalarCap

section Family

def boostedStrongAt {p : ℕ} (S : StrongSolverFamily.{u} p)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
    (center : data.X) : StrongSolver (data.withStart center) :=
  S.atData (data.withStart center) (by
    simpa [VIPublicData.withStart] using hp)

def boostedResidualSolve {p : ℕ} (S : StrongSolverFamily.{u} p)
    (gamma : ℝ) (b : ℕ)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
    (center : data.X) (R epsilon : ℝ) : CappedExactJetCall data :=
  (boostedResidualCall (data.withStart center)
    (boostedStrongAt S data hp center) gamma b R epsilon).fromWithStart data center

/-- The executable residual family produced by the boost. -/
def boostedResidualFamily (p : ℕ) (S : StrongSolverFamily.{u} p)
    (gamma : ℝ) (b : ℕ) : ResidualSolverFamily.{u} p where
  leadingConstant := boostLeadingConstant p S.leadingConstant b
  leadingConstant_pos := boostLeadingConstant_pos p S.leadingConstant_pos b
  solve _ _ _ _ data hp center R epsilon :=
    boostedResidualSolve S gamma b data hp center R epsilon

@[simp] theorem boostedResidualFamily_atData_leadingConstant
    (p : ℕ) (S : StrongSolverFamily.{u} p) (gamma : ℝ) (b : ℕ)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p) :
    ((boostedResidualFamily p S gamma b).atData data hp).leadingConstant =
      boostLeadingConstant p S.leadingConstant b := rfl

@[simp] theorem boostedResidualFamily_atData_solve
    (p : ℕ) (S : StrongSolverFamily.{u} p) (gamma : ℝ) (b : ℕ)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
    (center : data.X) (R epsilon : ℝ) :
    ((boostedResidualFamily p S gamma b).atData data hp).solve center R epsilon =
      boostedResidualSolve S gamma b data hp center R epsilon := rfl

/-- Full interface transformation of `thm:boost`: the executable family,
no-false-success guarantee, true-radius completion, and `b+4` cap bound. -/
theorem boostedResidualFamily_satisfies
    (p : ℕ) (S : StrongSolverFamily.{u} p) (gamma : ℝ) (b : ℕ)
    (hS : S.SatisfiesInterface gamma b)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (ha23 : 2 / 3 ≤ ((p - 1 : ℕ) : ℝ) * gamma)
    (ha2 : ((p - 1 : ℕ) : ℝ) * gamma ≤ 2) :
    (boostedResidualFamily p S gamma b).SatisfiesInterface
      (boostAlpha gamma) (b + 4) := by
  intro E _ _ _ data hp
  have ha23data : 2 / 3 ≤ ((data.p - 1 : ℕ) : ℝ) * gamma := by
    simpa [hp] using ha23
  have ha2data : ((data.p - 1 : ℕ) : ℝ) * gamma ≤ 2 := by
    simpa [hp] using ha2
  refine ⟨?_, ?_, ?_⟩
  · intro center R epsilon hR hRD hepsilon
    let shifted := data.withStart center
    let strong := boostedStrongAt S data hp center
    have hcap := boostSharedCap_le_residualInterfaceCost shifted strong gamma b
      hgamma hgamma1 R epsilon hR (by simpa [shifted, VIPublicData.withStart] using hRD)
      hepsilon (by simpa [shifted, VIPublicData.withStart] using ha23data)
      (by simpa [shifted, VIPublicData.withStart] using ha2data)
    have hstrongC : strong.leadingConstant = S.leadingConstant := by
      rfl
    rw [hstrongC] at hcap
    change ((boostedResidualSolve S gamma b data hp center R epsilon).cap : ℝ) ≤
      residualInterfaceCost data (boostLeadingConstant p S.leadingConstant b)
        (boostAlpha gamma) (b + 4) R epsilon
    simpa [boostedResidualSolve, shifted, strong, boostedStrongAt, hp,
      CappedExactJetCall.fromWithStart, residualInterfaceCost,
      residualCondition, residualLog, VIPublicData.withStart,
      boostLeadingConstant] using hcap
  · intro F oracle center R epsilon used cert hF hR hepsilon hrun
    let shifted := data.withStart center
    let strong := boostedStrongAt S data hp center
    have hps : shifted.p = p := by simpa [shifted, VIPublicData.withStart] using hp
    have hSshift : strong.SatisfiesInterface shifted gamma b := by
      simpa [strong, boostedStrongAt, shifted] using hS E shifted hps
    let sourceCall := boostedResidualCall shifted strong gamma b R epsilon
    rw [boostedResidualFamily_atData_solve] at hrun
    have hrun' : (sourceCall.fromWithStart data center).execute data F oracle =
        .finished used (some cert) := by
      simpa [boostedResidualSolve, shifted, strong,
        sourceCall] using hrun
    obtain ⟨inner, hinnerRun, hcertEq⟩ :=
      CappedExactJetCall.fromWithStart_success data center F oracle sourceCall
        used cert hrun'
    let K := boostHorizon shifted gamma R epsilon
    let eta := boostStepsize R epsilon K
    let e := boostOuterError R K
    have heta : 0 < eta := by
      dsimp [eta]
      exact boostStepsize_pos hR hepsilon K
    have he : 0 < e := by
      dsimp [e]
      exact boostOuterError_pos hR K
    have hsafe := extrapolatedHalpernCall_noFalseSuccess shifted strong gamma b
      hSshift F (oracle.withStart data F center) (hF.withStart data F center)
      K R epsilon e eta heta he used inner (by
        simpa [sourceCall, boostedResidualCall, K, eta, e] using hinnerRun)
    subst cert
    exact (EvaluatedNormalCertificate.fromWithStart_verified_iff
      data center F epsilon inner).2 hsafe.1
  · intro F oracle center R epsilon hF hR hRD hepsilon zStar hzStar hdistance
    let shifted := data.withStart center
    let strong := boostedStrongAt S data hp center
    have hps : shifted.p = p := by simpa [shifted, VIPublicData.withStart] using hp
    have hSshift : strong.SatisfiesInterface shifted gamma b := by
      simpa [strong, boostedStrongAt, shifted] using hS E shifted hps
    let K := boostHorizon shifted gamma R epsilon
    let eta := boostStepsize R epsilon K
    let e := boostOuterError R K
    have hK : 2 ≤ K := boostHorizon_ge_two shifted gamma R epsilon
    have hFshift := hF.withStart data F center
    have hzShift : IsVISolution shifted F zStar := by
      exact hzStar
    have hdistShift : ‖shifted.x0 - zStar‖ ≤ R := by
      simpa [shifted, VIPublicData.withStart] using hdistance
    obtain ⟨used, inner, hrunInner, hverifiedInner, husedCap⟩ :=
      extrapolatedHalpernCall_completes shifted strong gamma b hSshift hgamma
        (by simpa [shifted, VIPublicData.withStart] using ha2data)
        F (oracle.withStart data F center) hFshift K hK R epsilon hR hepsilon
        zStar hzShift hdistShift
    let sourceCall := boostedResidualCall shifted strong gamma b R epsilon
    have hsourceRun : sourceCall.execute shifted F
        (oracle.withStart data F center) = .finished used (some inner) := by
      simpa [sourceCall, boostedResidualCall, K, eta, e] using hrunInner
    have hrunOut := CappedExactJetCall.fromWithStart_completes data center F oracle
      sourceCall used inner hsourceRun
    let cert := inner.fromWithStart data center
    have hcert : cert.IsVerifiedFor data F epsilon :=
      (EvaluatedNormalCertificate.fromWithStart_verified_iff
        data center F epsilon inner).2 hverifiedInner
    have hcap := boostSharedCap_le_residualInterfaceCost shifted strong gamma b
      hgamma hgamma1 R epsilon hR (by simpa [shifted, VIPublicData.withStart] using hRD)
      hepsilon (by simpa [shifted, VIPublicData.withStart] using ha23data)
      (by simpa [shifted, VIPublicData.withStart] using ha2data)
    have hstrongC : strong.leadingConstant = S.leadingConstant := by rfl
    rw [hstrongC] at hcap
    refine ⟨used, cert, ?_, hcert, ?_⟩
    · rw [boostedResidualFamily_atData_solve]
      simpa [boostedResidualSolve, shifted, strong,
        sourceCall, cert]
        using hrunOut
    · calc
        (used : ℝ) ≤ (sourceCall.cap : ℝ) := by exact_mod_cast husedCap
        _ ≤ residualInterfaceCost data
            ((boostedResidualFamily p S gamma b).atData data hp).leadingConstant
            (boostAlpha gamma)
            (b + 4) R epsilon := by
          rw [boostedResidualFamily_atData_leadingConstant]
          simpa [boostedResidualFamily, shifted, strong,
            boostedStrongAt, hp, sourceCall,
            residualInterfaceCost, residualCondition, residualLog,
            VIPublicData.withStart, boostLeadingConstant] using hcap

/-- Source-facing proposition for `thm:boost`. -/
def BoostClaim : Prop :=
  ∀ (p : ℕ) (S : StrongSolverFamily.{u} p) (gamma : ℝ) (b : ℕ),
    S.SatisfiesInterface gamma b →
    0 < gamma → gamma ≤ 1 →
    2 / 3 ≤ ((p - 1 : ℕ) : ℝ) * gamma →
    ((p - 1 : ℕ) : ℝ) * gamma ≤ 2 →
    ∃ A : ResidualSolverFamily.{u} p,
      A.SatisfiesInterface (boostAlpha gamma) (b + 4)

theorem boostClaim_proof : BoostClaim := by
  intro p S gamma b hS hgamma hgamma1 ha23 ha2
  exact ⟨boostedResidualFamily p S gamma b,
    boostedResidualFamily_satisfies p S gamma b hS hgamma hgamma1 ha23 ha2⟩

end Family

end

end LeanArticleAudit.Pilot
