import LeanArticleAudit.Pilot.LowerClosure

/-!
# Uniform lower-budget closure for the main theorem

This file performs the last normalization step in the source proof.  It keeps
the zero-query and positive-query adversaries operationally separate (their
public instances have different dimensions), but joins them under one budget
quantifier and one positive constant depending only on `p`.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

/-- The residual constant called `c_p^{res}` in the completion proof. -/
def sourceResidualConstant (p : ℕ) : ℝ :=
  1 / deterministicResidualDenominator p standardGateProfile

/-- The single multiplicative constant in the final randomized lower bound. -/
def sourceMainLowerConstant (p : ℕ) : ℝ :=
  sourceResidualConstant p ^ deterministicRateExponent p / 2

theorem sourceResidualConstant_pos (p : ℕ) :
    0 < sourceResidualConstant p := by
  exact div_pos zero_lt_one
    (deterministicResidualDenominator_pos p standardGateProfile)

theorem sourceMainLowerConstant_pos (p : ℕ) (hp : 2 ≤ p) :
    0 < sourceMainLowerConstant p := by
  exact div_pos (Real.rpow_pos_of_pos (sourceResidualConstant_pos p) _) (by norm_num)

theorem sourceMainLowerConstant_eq_omega (p : ℕ) :
    sourceMainLowerConstant p =
      deterministicOmegaConstant p standardGateProfile := by
  rfl

/-- Elementary `N=0`/`N≥1` splice used verbatim in the paper: the maximum
of the zero-query lower bound and the inverted positive-budget bound absorbs
the additive `-1` at a factor of two. -/
theorem half_le_max_one_sub_one (x : ℝ) (hx : 0 ≤ x) :
    x / 2 ≤ max 1 (x - 1) := by
  by_cases htwo : x ≤ 2
  · exact le_max_of_le_left (by linarith)
  · exact le_max_of_le_right (by linarith)

theorem source_lower_constant_splice (p : ℕ) (hp : 2 ≤ p)
    (Q : ℝ) (hQ : 2 ≤ Q) :
    sourceMainLowerConstant p * Q ^ deterministicRateExponent p ≤
      max 1
        ((sourceResidualConstant p * Q) ^ deterministicRateExponent p - 1) := by
  have hres : 0 ≤ sourceResidualConstant p := (sourceResidualConstant_pos p).le
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ
  have hx : 0 ≤
      (sourceResidualConstant p * Q) ^ deterministicRateExponent p :=
    Real.rpow_nonneg (mul_nonneg hres hQ0) _
  calc
    sourceMainLowerConstant p * Q ^ deterministicRateExponent p =
        (sourceResidualConstant p * Q) ^ deterministicRateExponent p / 2 := by
      rw [Real.mul_rpow hres hQ0]
      simp only [sourceMainLowerConstant]
      ring
    _ ≤ max 1
        ((sourceResidualConstant p * Q) ^ deterministicRateExponent p - 1) :=
      half_le_max_one_sub_one _ hx

/-- Pure arithmetic endpoint of the completion proof.  `hzero` is exactly the
zero-query lemma's consequence `T≥1`; `hpositive` is exactly the inversion of
the positive-budget obstruction. -/
theorem source_successful_budget_lower (p : ℕ) (hp : 2 ≤ p)
    (Q : ℝ) (hQ : 2 ≤ Q) (T : ℕ) (hzero : 1 ≤ T)
    (hpositive :
      (sourceResidualConstant p * Q) ^ deterministicRateExponent p - 1 ≤
        (T : ℝ)) :
    sourceMainLowerConstant p * Q ^ deterministicRateExponent p ≤ T := by
  apply (source_lower_constant_splice p hp Q hQ).trans
  exact max_le (by exact_mod_cast hzero) hpositive

/-- The positive-budget randomized obstruction, specialized to the one final
constant and to failure probability `1/4`. -/
def PositiveRandomBudgetObstruction (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon) (N : ℕ) : Prop :=
  ∀ (d : ℕ) [NeZero d]
    (policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) N)
    (fill : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
    (dummy : SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
    (hdim : RandomDimensionCondition N d (1 / 4 : ℝ)),
    let hmdlt : hiddenM N < d :=
      hiddenM_lt_of_randomDimensionCondition (by norm_num) (by norm_num) hdim
    let prior := canonicalHaarPrior hmdlt hR
    let exec := canonicalHaarExecution p hp standardGateProfile Lp hLp R hR
      N d hmdlt policy fill dummy
    ∃ Q : RealOrthogonalGroup d,
      IsAdmissibleOperator
          (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
          (hiddenOperator p standardGateProfile Lp R N (prior.frame Q)) ∧
      ENNReal.ofReal (3 / 4 : ℝ) ≤ policy.seedMeasure {seed |
        epsilon < tangentResidual
          (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
          (hiddenOperator p standardGateProfile Lp R N (prior.frame Q))
          (exec.actualOutput Q seed).1}

/-- At budget zero a single interval public instance already blocks every
randomized policy. -/
def ZeroRandomBudgetObstruction (p : ℕ) (hp : 2 ≤ p)
    (Lp D epsilon : ℝ) (hLp : 0 < Lp) (hD : 0 < D) : Prop :=
  ∀ policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := ZeroQueryAnswer p)
      (intervalVIData p hp Lp D hLp hD).X 0,
    ¬ ZeroQueryUniformSuccess p hp Lp D epsilon hLp hD policy

/-- One operational obstruction for every natural query budget.  The left
branch is `N=0`; the right branch is `N≥1` in a dimension satisfying the
paper's explicit random-frame condition. -/
def UnifiedRandomBudgetObstruction (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon) (N : ℕ) : Prop :=
  (N = 0 ∧ ZeroRandomBudgetObstruction p hp Lp D epsilon hLp
    (hD.symm ▸ by positivity)) ∨
  (1 ≤ N ∧ PositiveRandomBudgetObstruction p hp Lp R D epsilon
    hLp hR hD hepsilon N)

theorem unifiedRandomBudgetObstruction
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon) (N : ℕ)
    (hbudget : (N : ℝ) < sourceMainLowerConstant p *
      deterministicConditionNumber p Lp D epsilon ^
        deterministicRateExponent p) :
    UnifiedRandomBudgetObstruction p hp Lp R D epsilon hLp hR hD
      hepsilon N := by
  by_cases hN : N = 0
  · left
    refine ⟨hN, ?_⟩
    subst N
    intro policy
    obtain ⟨M, _hM, _hplus, _hminus, _hmeas, _hrun, _hiffPlus,
      _hiffMinus, _hmeasPlus, _hmeasMinus, _hnotBoth, hnotUniform⟩ :=
      zeroQueryLowerClaim_proof p hp Lp D epsilon hLp
        (hD.symm ▸ by positivity) hepsilon policy
    exact hnotUniform
  · right
    have hNpos : 1 ≤ N := by omega
    refine ⟨hNpos, ?_⟩
    intro d _instD policy fill dummy hdim
    obtain ⟨c, hc, _hcpos, hoper⟩ := randomOmegaOperationalClaim_proof p hp
    have hc' : c = sourceMainLowerConstant p := by
      rw [hc, sourceMainLowerConstant_eq_omega]
    subst c
    have hbudget' : (N : ℝ) < sourceMainLowerConstant p *
        deterministicConditionNumber p Lp D epsilon ^
          (2 / (3 * (p : ℝ) - 1)) := by
      simpa only [deterministicRateExponent] using hbudget
    obtain ⟨Q, hQadm, hQfail, _hQexpected⟩ :=
      hoper Lp R D epsilon hLp hR hD hepsilon N d hNpos policy fill
        dummy hbudget' hdim
    exact ⟨Q, hQadm, hQfail⟩

/-- Operational meaning of a uniformly viable randomized budget: neither the
zero-query interval adversary nor the positive-query random-frame adversary
blocks it.  This is the exact property of a candidate universal algorithm
family needed for the lower half of the complexity theorem. -/
def RandomUniformBudgetSurvives
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon) (N : ℕ) : Prop :=
  ¬ UnifiedRandomBudgetObstruction p hp Lp R D epsilon hLp hR hD
    hepsilon N

/-- Literal pure-power randomized query lower bound for every surviving
natural budget, including `N=0`.  The `Q≥2` premise is retained exactly as in
`thm:main`, although the explicit operational constant proves the inequality
without needing to weaken at that point. -/
theorem randomUniformSuccessfulBudget_lower
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon)
    (hQ : 2 ≤ deterministicConditionNumber p Lp D epsilon)
    (N : ℕ)
    (hsurvives : RandomUniformBudgetSurvives p hp Lp R D epsilon hLp hR
      hD hepsilon N) :
    sourceMainLowerConstant p *
        deterministicConditionNumber p Lp D epsilon ^
          deterministicRateExponent p ≤ (N : ℝ) := by
  apply le_of_not_gt
  intro hbudget
  exact hsurvives (unifiedRandomBudgetObstruction p hp Lp R D epsilon
    hLp hR hD hepsilon N hbudget)

/-- Strengthened lower half used by `thm:main`: one positive constant, the
all-budget operational obstruction, and the exact arithmetic splice yielding
the displayed pure-power lower bound when `Q≥2`. -/
def MainRandomLowerClosureClaim : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p),
    0 < sourceMainLowerConstant p ∧
    (∀ (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
      (hD : D = 2 * R) (hepsilon : 0 < epsilon) (N : ℕ),
      (N : ℝ) < sourceMainLowerConstant p *
        deterministicConditionNumber p Lp D epsilon ^
          deterministicRateExponent p →
      UnifiedRandomBudgetObstruction p hp Lp R D epsilon hLp hR hD
        hepsilon N) ∧
    (∀ (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
      (hD : D = 2 * R) (hepsilon : 0 < epsilon),
      2 ≤ deterministicConditionNumber p Lp D epsilon →
      ∀ (N : ℕ),
      RandomUniformBudgetSurvives p hp Lp R D epsilon hLp hR hD hepsilon N →
      sourceMainLowerConstant p *
          deterministicConditionNumber p Lp D epsilon ^
            deterministicRateExponent p ≤ (N : ℝ)) ∧
    (∀ (Q : ℝ), 2 ≤ Q → ∀ (T : ℕ), 1 ≤ T →
      (sourceResidualConstant p * Q) ^ deterministicRateExponent p - 1 ≤
        (T : ℝ) →
      sourceMainLowerConstant p * Q ^ deterministicRateExponent p ≤ T)

theorem mainRandomLowerClosureClaim_proof : MainRandomLowerClosureClaim := by
  intro p hp
  refine ⟨sourceMainLowerConstant_pos p hp, ?_, ?_, ?_⟩
  · intro Lp R D epsilon hLp hR hD hepsilon N hbudget
    exact unifiedRandomBudgetObstruction p hp Lp R D epsilon hLp hR hD
      hepsilon N hbudget
  · intro Lp R D epsilon hLp hR hD hepsilon hQ N hsurvives
    exact randomUniformSuccessfulBudget_lower p hp Lp R D epsilon hLp hR hD
      hepsilon hQ N hsurvives
  · intro Q hQ T hT hthreshold
    exact source_successful_budget_lower p hp Q hQ T hT hthreshold

end

end LeanArticleAudit.Pilot
