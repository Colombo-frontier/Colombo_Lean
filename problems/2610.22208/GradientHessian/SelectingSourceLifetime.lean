import GradientHessian.SelectingFork

/-! The selection lifetime theorem at the literal source dimensions.
Residual dimensions are constructed internally, so callers retain their
original matrix, program, and seed types throughout the statement. -/

noncomputable section
namespace GradientHessian.SelectingFork
open Matrix MeasureTheory LowRank OracleComposition ForkMachineBound

variable {d n r : ℕ} {Seed PreState PostState Private : Type*}
  [MeasurableSpace Seed] [MeasurableSpace PreState] [MeasurableSpace PostState]
  [MeasurableSpace Private]

theorem source_selection_lifetime (M J κ q₀ S q₁ : ℕ)
    (hMsource : 1+4096*J^2≤M) (hJ : ForkLifetime.depthThreshold≤J)
    (hr : ForkLifetime.rankRatio*(M:ℝ)≤r) (hκ : 18874368≤κ)
    (hS : S≤M) (hq₀ : q₀≤M*ForkLifetime.lifetime J+1) (hq₁ : q₁≤ForkLifetime.lifetime J+1)
    (hd : d=κ*r*J) (hn : n+κ*r=d)
    (P : Matrix (Fin d) (Fin d) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank=r)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ*B=1) (hPB : P*B=B) (fallback : Fin d → ℝ)
    (pre : DisclosureCompiler.Program d PreState) (post : TestSelectionMachine.Program d PostState)
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool)
    (hlegal : LegalSelections (n := n) pre post preInitial postInitial enabled J P fallback q₀ S q₁ (q₁+2))
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw] :
    (experimentLaw J P (iidMatrixLaw d n ((d:NNReal)⁻¹)) seedLaw privateLaw).real
      (selectedHit pre post preInitial postInitial enabled J P B fallback ForkLifetime.gamma)≤1/256 := by
  have hQ : totalBudget J q₀ S r q₁≤n := by
    have hb := (ForkLifetime.numerical_lifetime_bound (by omega : 1≤M) hJ hr
      (by omega : 1≤κ) hS hq₀ hq₁ (pE := 1) (by norm_num)).1
    change totalBudget J q₀ S r q₁≤κ*r*J-κ*r at hb
    omega
  have hnQ : n=(n-totalBudget J q₀ S r q₁)+totalBudget J q₀ S r q₁ :=
    (Nat.sub_add_cancel hQ).symm
  have hdQ : d=(κ*r+(n-totalBudget J q₀ S r q₁))+totalBudget J q₀ S r q₁ := by omega
  generalize hb : n-totalBudget J q₀ S r q₁=b at hnQ hdQ
  have hdim : (κ*r+b)+totalBudget J q₀ S r q₁=κ*r*J := hdQ.symm.trans hd
  subst hdQ
  subst hnQ
  exact (arbitrary_selection_lifetime M r J κ q₀ S q₁ (κ*r+b) b hMsource hJ hr hκ
    hS hq₀ hq₁ rfl hdim hP hrank B hB hPB fallback pre post preInitial postInitial enabled
    hlegal seedLaw privateLaw).1

end GradientHessian.SelectingFork
