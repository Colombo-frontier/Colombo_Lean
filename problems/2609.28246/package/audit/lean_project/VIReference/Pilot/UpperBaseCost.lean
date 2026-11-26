import VIReference.Pilot.UpperBaseStrong

/-!
# Public cost bounds for the base strongly-monotone solver

These lemmas isolate the numerical part of the `prop:base-strong` proof from
the executable trace.  In particular, no algorithmic success assertion is
assumed in order to bound the installed finite caps.
-/

namespace VIReference.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exponent `2/(p+1)` of the base strongly-monotone method. -/
noncomputable def baseHalvingExponent (p : ℕ) : ℝ :=
  2 / ((p : ℝ) + 1)

/-- The part of a Halve-stage cost depending only on the fixed order `p`. -/
noncomputable def baseHalvingLeadingConstant (p : ℕ) : ℝ :=
  Real.rpow (2 * tensorBetaCoefficient p *
    Real.rpow (4 / 3 : ℝ) (((p : ℝ) - 1) / 2)) (baseHalvingExponent p)

/-- Exact separation of the public condition number from the order-only
constant in `halvingThreshold`. -/
theorem halvingThreshold_factor
    (p : ℕ) (Lp r mu : ℝ) (hLp : 0 ≤ Lp) (hr : 0 ≤ r) (hmu : 0 < mu) :
    halvingThreshold p Lp r mu =
      baseHalvingLeadingConstant p *
        Real.rpow (Lp * r ^ (p - 1) / mu) (baseHalvingExponent p) := by
  have hbeta : 0 ≤ tensorBetaCoefficient p := by
    unfold tensorBetaCoefficient
    positivity
  have hc : 0 ≤ 2 * tensorBetaCoefficient p *
      Real.rpow (4 / 3 : ℝ) (((p : ℝ) - 1) / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hbeta) (Real.rpow_nonneg (by norm_num) _)
  have hq : 0 ≤ Lp * r ^ (p - 1) / mu :=
    div_nonneg (mul_nonneg hLp (pow_nonneg hr _)) hmu.le
  unfold halvingThreshold baseHalvingLeadingConstant baseHalvingExponent
  rw [show 2 * tensorBetaCoefficient p *
        (4 / 3 : ℝ) ^ (((p : ℝ) - 1) / 2) * Lp * r ^ (p - 1) / mu =
      (2 * tensorBetaCoefficient p *
        (4 / 3 : ℝ) ^ (((p : ℝ) - 1) / 2)) *
        (Lp * r ^ (p - 1) / mu) by ring]
  change (_ * _) ^ (2 / ((p : ℝ) + 1)) = _
  exact Real.mul_rpow hc hq

/-- The real expression inside the Halve ceiling is monotone in the promised
radius. -/
theorem halvingThreshold_mono_radius
    (p : ℕ) (Lp mu r R : ℝ) (hLp : 0 ≤ Lp) (hmu : 0 < mu)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    halvingThreshold p Lp r mu ≤ halvingThreshold p Lp R mu := by
  unfold halvingThreshold
  have hbeta : 0 ≤ tensorBetaCoefficient p := by
    unfold tensorBetaCoefficient
    positivity
  have hcoef : 0 ≤
      2 * tensorBetaCoefficient p * (4 / 3 : ℝ) ^ (((p : ℝ) - 1) / 2) * Lp := by
    positivity
  apply Real.rpow_le_rpow
  · exact div_nonneg (mul_nonneg hcoef (pow_nonneg hr _)) hmu.le
  · apply div_le_div_of_nonneg_right _ hmu.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrR _) hcoef
  · positivity

/-- A robust cap bound requiring only radius monotonicity.  It is deliberately
slightly coarser than the geometric-series refinement: every one of the
`halvings` stages is charged at the initial radius.  This is enough for the
later `L_S^2` wrapper and is useful independently of the trace proof. -/
theorem baseTrialRealCapBound_le
    (data : VIPublicData E) (mu : ℝ) (hmu : 0 < mu)
    (halvings : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    baseTrialRealCapBound data mu halvings r ≤
      2 + 2 * (halvings : ℝ) *
        (halvingThreshold data.p data.Lp r mu + 1) := by
  induction halvings generalizing r with
  | zero => simp [baseTrialRealCapBound]
  | succ n ih =>
      rw [baseTrialRealCapBound]
      have hhalf : 0 ≤ r / 2 := by positivity
      have hmono := halvingThreshold_mono_radius data.p data.Lp mu
        (r / 2) r data.Lp_pos.le hmu hhalf (by linarith)
      have hih := ih (r / 2) hhalf
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith

/-- The integer cap inherits the same explicit real upper bound. -/
theorem baseTrialCap_cast_le_initial_radius
    (data : VIPublicData E) (mu : ℝ) (hmu : 0 < mu)
    (halvings : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (baseTrialCap data mu halvings r : ℝ) ≤
      2 + 2 * (halvings : ℝ) *
        (halvingThreshold data.p data.Lp r mu + 1) :=
  (baseTrialCap_cast_le_realBound data mu hmu.le halvings r hr).trans
    (baseTrialRealCapBound_le data mu hmu halvings r hr)

/-- Exact finite-sum unfolding of the adaptive prefix cap.  This lets the
final numerical proof bound each public radius trial independently and then
apply a card-times-maximum estimate. -/
theorem adaptiveBaseCapFrom_eq_sum_range
    (data : VIPublicData E) (mu delta : ℝ) (center : data.X)
    (remaining j : ℕ) :
    adaptiveBaseCapFrom data mu delta center remaining j =
      ∑ i ∈ Finset.range (remaining + 1),
        (scheduledBaseTrialCall data mu delta center
          (adaptiveGuessRadius data mu (j + i))).cap := by
  induction remaining generalizing j with
  | zero => simp [adaptiveBaseCapFrom]
  | succ n ih =>
      rw [adaptiveBaseCapFrom, ih]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      conv_lhs => rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      omega

end

end VIReference.Pilot
