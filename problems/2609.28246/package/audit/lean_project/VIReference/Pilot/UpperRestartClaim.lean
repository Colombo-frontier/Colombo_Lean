import VIReference.Pilot.UpperRestartCost

/-!
# Fixed-order restart family and source-facing claim

The execution layer is in `UpperRestartTransformation`; the scalar schedule
accounting is in `UpperRestartCost`.  This final module attaches one constant
chosen at fixed order `p` before any dimension or instance is known.
-/

namespace VIReference.Pilot

noncomputable section

universe u

theorem restartLeadingConstant_positive
    (p : ℕ) {C alpha : ℝ} (hC : 0 < C) (b : ℕ) :
    0 < restartLeadingConstant p C alpha b := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ restartCallLeadingConstant p C alpha b :=
    restartCallLeadingConstant_nonneg p C alpha b hC.le
  unfold restartLeadingConstant
  exact mul_pos (mul_pos (by norm_num) (by positivity)) (by linarith)

/-- Turn a residual family into the concrete certified restart family once a
fixed-order leading constant has been selected. -/
noncomputable def restartedStrongFamily (p : ℕ)
    (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ)
    (C : ℝ) (hC : 0 < C) : StrongSolverFamily.{u} p where
  leadingConstant := C
  leadingConstant_pos := hC
  solve := fun _ _ _ _ data hp center mu delta =>
    adaptiveRestartCall data (A.atData data hp) alpha b center mu delta

@[simp] theorem restartedStrongFamily_atData_leadingConstant
    (p : ℕ) (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ)
    (C : ℝ) (hC : 0 < C)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p) :
    ((restartedStrongFamily p A alpha b C hC).atData data hp).leadingConstant = C :=
  rfl

@[simp] theorem restartedStrongFamily_atData_solve
    (p : ℕ) (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ)
    (C : ℝ) (hC : 0 < C)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
    (center : data.X) (mu delta : ℝ) :
    ((restartedStrongFamily p A alpha b C hC).atData data hp).solve
        center mu delta =
      adaptiveRestartCall data (A.atData data hp) alpha b center mu delta :=
  rfl

/-- The fixed-order family with the explicit two-schedule leading constant. -/
noncomputable def certifiedRestartFamily (p : ℕ)
    (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ) :
    StrongSolverFamily.{u} p :=
  restartedStrongFamily p A alpha b
    (restartLeadingConstant p A.leadingConstant alpha b)
    (restartLeadingConstant_positive p A.leadingConstant_pos b)

@[simp] theorem certifiedRestartFamily_atData_solve
    (p : ℕ) (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
    (center : data.X) (mu delta : ℝ) :
    ((certifiedRestartFamily p A alpha b).atData data hp).solve center mu delta =
      adaptiveRestartCall data (A.atData data hp) alpha b center mu delta :=
  rfl

/-- The executable two-schedule restart transformation raises only the
logarithmic exponent by two.  The leading constant is fixed before the
ambient space and public problem instance are chosen. -/
theorem certifiedRestartFamily_satisfies
    (p : ℕ) (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ)
    (hA : A.SatisfiesInterface alpha b)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    (certifiedRestartFamily p A alpha b).SatisfiesInterface alpha (b + 2) := by
  intro E instNorm instInner instFinite data hp
  let localA := A.atData data hp
  have hAlocal : localA.SatisfiesInterface data alpha b :=
    hA E data hp
  constructor
  · intro G oracle center mu delta used cert hG hmu hdelta hrun
    exact adaptiveRestartCall_no_false_success data localA alpha b hAlocal
      G oracle hG center mu delta hmu hdelta
      (by
        simpa [certifiedRestartFamily, restartedStrongFamily,
          StrongSolverFamily.atData, localA] using hrun)
  · intro G oracle center mu delta hG hmu hdelta hstrong zStar hz
    let r := ‖center.1 - zStar‖
    have hr : 0 ≤ r := norm_nonneg _
    have hrD : r ≤ data.D := by
      dsimp [r]
      simpa [dist_eq_norm] using
        data.diameter_le center.1 center.2 zStar hz.1
    have hcover : r ≤
        adaptiveGuessRadius data mu (adaptiveCoverCount data mu r) :=
      adaptiveCoverCount_covers data mu r hmu hr hrD
    obtain ⟨used, cert, hrun, hcert, hused⟩ :=
      adaptiveRestartCall_succeeds_at_guess data localA alpha b hAlocal
        G oracle hG center mu delta hmu hdelta hstrong zStar hz
        (adaptiveCoverCount data mu r)
        (adaptiveCoverCount_le data mu r hmu hr hrD)
        (by simpa [r] using hcover)
    have husedReal : (used : ℝ) ≤
        (adaptiveRestartCapFrom data localA alpha b mu delta center
          (adaptiveCoverCount data mu r) 0 : ℝ) := by
      exact_mod_cast hused
    have hcost := adaptiveRestartPrefixCap_le data localA alpha b mu delta r
      center hmu hdelta hr hrD halpha0.le halpha1
    refine ⟨used, cert, ?_, hcert, ?_⟩
    · simpa [certifiedRestartFamily, restartedStrongFamily,
        StrongSolverFamily.atData, localA] using hrun
    · change (used : ℝ) ≤ strongInterfaceCost data
        (restartLeadingConstant p A.leadingConstant alpha b) alpha (b + 2)
          ‖center.1 - zStar‖ mu delta
      calc
        (used : ℝ) ≤
            (adaptiveRestartCapFrom data localA alpha b mu delta center
              (adaptiveCoverCount data mu r) 0 : ℝ) := husedReal
        _ ≤ restartLeadingConstant data.p localA.leadingConstant alpha b *
              (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha) *
              (strongLog data mu delta) ^ (b + 2) := hcost
        _ = strongInterfaceCost data
              (restartLeadingConstant p A.leadingConstant alpha b) alpha (b + 2)
              ‖center.1 - zStar‖ mu delta := by
          simp only [strongInterfaceCost]
          simp [localA, ResidualSolverFamily.atData, hp, r]

/-- Source-facing `lem:restart`: from any fixed-order residual family with
exponents `(alpha,b)`, construct an executable strong family with exponents
`(alpha,b+2)`. -/
theorem restartClaim_proof
    (p : ℕ) (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ)
    (hA : A.SatisfiesInterface alpha b)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ S : StrongSolverFamily.{u} p,
      S.SatisfiesInterface alpha (b + 2) := by
  exact ⟨certifiedRestartFamily p A alpha b,
    certifiedRestartFamily_satisfies p A alpha b hA halpha0 halpha1⟩

end

end VIReference.Pilot
