import Bilevel.PolishedHistoryUpperExecution

/-! The normalized and three-term minimax upper bounds in exactly the same
arbitrary-history paired original-SFO model as the stopped lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

/-- Actual execution, exact supplied public initial points, and arbitrary
history dependence, with both confidence and initialization logs retained. -/
theorem Instance.public_normalized_upper {ε : ℝ}
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    I.risk (publicAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤ENNReal.ofReal ε ∧
    I.cost (publicAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤
      ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  have hc := CachedUpper.normalized_upper I.primitive I.oracle
    I.truth_fx I.truth_fy I.truth_gy I.truth_gx hL hΔ hε le_rfl le_rfl le_rfl hκ
    I.upper_canonical_lower_bound I.x₀ I.yinit I.upper_canonical_gap
    I.upper_canonical_initialization I.initialHistory
  dsimp only at hc
  have he := ofReal_integral_eq_lintegral_ofReal hc.2.2.2.1
    (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))
  simp only [ENNReal.ofReal_natCast] at he
  have hfinite : (∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(CachedUpper.algorithm I.oracle μ L L L ρ
        (CachedUpper.universalCurvature L μ L L L ρ) Δ ε R₀ I.x₀ I.yinit).law ((),I.initialHistory))≠⊤ := by
    rw [←he]
    exact ENNReal.ofReal_ne_top
  constructor
  · refine (I.public_risk_le_denote ε hfinite).trans ?_
    simp_rw [I.upper_loss_eq_canonical]
    rw [←ofReal_integral_eq_lintegral_ofReal hc.1
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hc.2.1
  · exact (I.public_cost_le_denote ε).trans
      (he ▸ ENNReal.ofReal_le_ofReal hc.2.2.2.2)

theorem Instance.public_three_term_upper {ε : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hθ : 1≤ρ/μ) (hκ : 1≤L/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    I.risk (publicAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤ENNReal.ofReal ε ∧
    I.cost (publicAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤
      ENNReal.ofReal (CachedUpper.threeRateBound L μ L L L ρ σf σg Δ ε R₀) := by
  have hc := I.public_normalized_upper hL hΔ.le hε hκ
  exact ⟨hc.1,hc.2.trans (ENNReal.ofReal_le_ofReal
    (CachedUpper.normalizedBound_le_threeRateBound hL hΔ hθ hκ hε haccuracy))⟩

theorem complexity_le_of_solver (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ)
    (A : SolverAt) (hA : Accurate C ε A) (B : ℝ≥0∞)
    (hcost : ∀ G (I : Instance G μ L ρ Δ R₀ σf σg),C G I → I.cost (A G I.x₀ I.yinit)≤B) :
    Complexity C ε≤B := by
  apply iInf_le_of_le ⟨A,hA⟩
  apply iSup_le
  intro I
  exact hcost I.val.1 I.val.2 I.property

/-- One common public solver works for every instance of any subclass of
the arbitrary-history paired-kernel model, including conservative laws. -/
theorem normalized_complexity_upper (C : InstanceClass μ L ρ Δ R₀ σf σg) {ε : ℝ}
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    Complexity C ε≤ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  apply complexity_le_of_solver C ε (fun G x y => publicAlgorithmAt G μ L ρ Δ ε R₀ σf σg x y)
  · intro G I _
    exact (I.public_normalized_upper hL hΔ hε hκ).1
  · intro G I _
    exact (I.public_normalized_upper hL hΔ hε hκ).2

/-- D+U+G upper minimax comparison in the same history-dependent original
query model, with no iid realization or fixed hidden-law restriction. -/
theorem three_term_complexity_upper (C : InstanceClass μ L ρ Δ R₀ σf σg) {ε : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hθ : 1≤ρ/μ) (hκ : 1≤L/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    Complexity C ε≤ENNReal.ofReal (CachedUpper.threeRateBound L μ L L L ρ σf σg Δ ε R₀) := by
  exact (normalized_complexity_upper C hL hΔ.le hε hκ).trans
    (ENNReal.ofReal_le_ofReal
      (CachedUpper.normalizedBound_le_threeRateBound hL hΔ hθ hκ hε haccuracy))

end Bilevel.PolishedHistory
