import NCConcave16991.PersistentOutput
import NCConcave16991.InnerExecutable
import NCConcave16991.UpperProbability

/-!
# The actual persistent algorithm's mean-square stationarity

The inner solver, persistent estimator, finite independent seed trajectory and
independent uniform output are instantiated here. All local error estimates
are proved for their actual updates; no stochastic convergence certificate is
an assumption of the final theorem.
-/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def persistentConditionNumber (p : ProblemParameters) : ℝ :=
  p.L / selectedDualRegularization p

theorem persistentConditionNumber_ge_one (p : ProblemParameters) :
    1 ≤ persistentConditionNumber p := by
  apply (le_div_iff₀ (selectedDualRegularization_pos p)).2
  simpa only [one_mul] using selectedDualRegularization_le_L p

def persistentSampleOutput {b S : ℕ} (P : Problem p dx dy K)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (q k : ℕ)
    (ω : FiniteProcess.History (InnerAlgorithm.Seed p.n k × (Fin b → Fin p.n)) S × Fin S) :
    PrimalSpace dx :=
  PersistentProcess.selectedOutput (signedComponentGradient P) y0 q
    (persistentInnerSolve P y0 hy0 k) P.initialPoint ω

theorem persistent_regularized_gradient_mean {b q k S : ℕ}
    [NeZero S] [MeasurableSpace (Fin S)] [MeasurableSingletonClass (Fin S)]
    (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (hb : 0 < b) (hq : 0 < q)
    (hbatch : persistentConditionNumber p * q / b ≤ 1 / 4096)
    (hk : 4294967296 * persistentConditionNumber p ^ 2 ≤ (k : ℝ))
    (hS : 4096 * (1 + p.L * p.gap / p.epsilon ^ 2) ≤ (S : ℝ)) :
    (∫ ω, ‖gradient (dualRegularizedEnvelope P (selectedDualRegularization p) y0)
      (persistentSampleOutput (b := b) (S := S) P y0 hy0 q k ω)‖ ^ 2
      ∂PersistentProcess.outputLaw (n := p.n) (b := b) (InnerAlgorithm.seedLaw k) S) ≤
        p.epsilon ^ 2 / 512 := by
  let μ := selectedDualRegularization p
  let r := μ * p.diameter ^ 2 / 2
  let Ψ := dualRegularizedValue P μ y0
  have hμ : 0 < μ := selectedDualRegularization_pos p
  have hΨb : BddBelow (range Ψ) := dualRegularizedValue_bddBelow P hμ.le y0 hy0
  let prox := proximalMap p.L_pos (dualRegularizedValue_continuous P hAS μ y0) hΨb
  have hgap : Ψ P.initialPoint - sInf (range Ψ) ≤ p.gap + r := by
    apply infimum_gap_of_uniform_comparison P.value_bddBelow hΨb _ P.initial_gap
    intro x
    have hc := dualRegularizedValue_comparison P hμ.le y0 hy0 x
    constructor <;> dsimp [Ψ, r] <;> linarith only [hc.1, hc.2]
  have hsolve (z : PersistentProcess.State dx dy) :
      (∫ j, ‖persistentInnerSolve P y0 hy0 k z j - prox z.center‖ ^ 2
        ∂InnerAlgorithm.seedLaw k) ≤
      (1 / 1024 : ℝ) * ‖prox z.center - z.center‖ ^ 2 +
        3 * weightedErrorSq (persistentConditionNumber p)
          (PersistentProcess.error (signedComponentGradient P) y0 z) / p.L ^ 2 +
        p.epsilon ^ 2 / (4294967296 * p.L ^ 2) := by
    have hh := persistentInnerSolve_error P hAS y0 hy0 hk z
    dsimp [prox, μ, persistentConditionNumber]
    convert hh using 1 <;> ring
  have hh := PersistentProcess.selected_gradient_mean_bound p.L_pos
    (signedComponentGradient_averagedSmooth P hAS) (persistentConditionNumber_ge_one p)
    hb (show 0 ≤ p.epsilon ^ 2 / (4294967296 * p.L ^ 2) by positivity) hΨb
    (dualRegularizedValue_weaklyConvex P hAS μ y0) y0 (fun _ ↦ hy0)
    hq hbatch (persistentInnerSolve P y0 hy0 k) (InnerAlgorithm.seedLaw k) P.initialPoint
    hgap prox (proximalMap_spec p.L_pos (dualRegularizedValue_continuous P hAS μ y0) hΨb) hsolve
    (S := S)
  have hnoise : 2 * (p.epsilon ^ 2 / (4294967296 * p.L ^ 2)) =
      p.epsilon ^ 2 / ((2 : ℝ) ^ 31 * p.L ^ 2) := by norm_num; ring
  rw [hnoise] at hh
  have hr : r ≤ p.epsilon ^ 2 / p.L := by
    have hc := selectedDualRegularization_value_error p
    have hd := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2 ^ 21) p.L_pos)).mp hc
    apply (le_div_iff₀ p.L_pos).2
    dsimp [r, μ] at hd ⊢
    norm_num at hd
    nlinarith [mul_nonneg (show 0 ≤ selectedDualRegularization p * p.diameter ^ 2 / 2 by positivity)
      p.L_pos.le]
  have hn := persistent_parameter_stationarity (Δ := p.gap) (r := r) p.L_pos p.epsilon_pos
    (Nat.pos_of_ne_zero (NeZero.ne S)) hr hS (le_refl _)
  exact hh.trans hn

theorem persistent_original_gradient_mean {b q k S : ℕ}
    [NeZero S] [MeasurableSpace (Fin S)] [MeasurableSingletonClass (Fin S)]
    (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (hb : 0 < b) (hq : 0 < q)
    (hbatch : persistentConditionNumber p * q / b ≤ 1 / 4096)
    (hk : 4294967296 * persistentConditionNumber p ^ 2 ≤ (k : ℝ))
    (hS : 4096 * (1 + p.L * p.gap / p.epsilon ^ 2) ≤ (S : ℝ)) :
    (∫ ω, ‖gradient (problemMoreauEnvelope P)
      (persistentSampleOutput (b := b) (S := S) P y0 hy0 q k ω)‖ ^ 2
      ∂PersistentProcess.outputLaw (n := p.n) (b := b) (InnerAlgorithm.seedLaw k) S) <
        p.epsilon ^ 2 / 200 := by
  let ν := PersistentProcess.outputLaw (n := p.n) (b := b) (InnerAlgorithm.seedLaw (n := p.n) k) S
  have hpoint (x : PrimalSpace dx) : ‖gradient (problemMoreauEnvelope P) x‖ ^ 2 ≤
      2 * ‖gradient (dualRegularizedEnvelope P (selectedDualRegularization p) y0) x‖ ^ 2 +
        p.epsilon ^ 2 / (2 : ℝ) ^ 18 := by
    have hh := norm_sub_sq_le_two (gradient (problemMoreauEnvelope P) x)
      (gradient (dualRegularizedEnvelope P (selectedDualRegularization p) y0) x) 0
    simp only [sub_zero, norm_sub_rev] at hh
    have ht := (selectedDualRegularization_transfer P hAS y0 hy0 x).2
    norm_num at ht ⊢
    nlinarith only [hh, ht]
  have hh := integral_mono (μ := ν) Integrable.of_finite Integrable.of_finite
    (fun ω ↦ hpoint (persistentSampleOutput (b := b) (S := S) P y0 hy0 q k ω))
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_const, probReal_univ, one_smul] at hh
  have hreg := persistent_regularized_gradient_mean P hAS y0 hy0 hb hq hbatch hk hS
  have hn := persistent_transfer_numerics p.epsilon_pos
  dsimp [ν] at hh
  linarith only [hh, hreg, hn]

/-- The actual Moreau-stationarity event has the advertised probability under
the explicitly constructed finite independent law. -/
theorem persistent_original_stationarity_probability {b q k S : ℕ}
    [NeZero S] [MeasurableSpace (Fin S)] [MeasurableSingletonClass (Fin S)]
    (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (hb : 0 < b) (hq : 0 < q)
    (hbatch : persistentConditionNumber p * q / b ≤ 1 / 4096)
    (hk : 4294967296 * persistentConditionNumber p ^ 2 ≤ (k : ℝ))
    (hS : 4096 * (1 + p.L * p.gap / p.epsilon ^ 2) ≤ (S : ℝ)) :
    (199 / 200 : ℝ) <
      (PersistentProcess.outputLaw (n := p.n) (b := b) (InnerAlgorithm.seedLaw k) S).real
        {ω | StationaryOutput P (persistentSampleOutput (b := b) (S := S) P y0 hy0 q k ω)} := by
  have hmean := persistent_original_gradient_mean P hAS y0 hy0 hb hq hbatch hk hS
  have hs := gradient_stationarity_probability
    (PersistentProcess.outputLaw (n := p.n) (b := b) (InnerAlgorithm.seedLaw (n := p.n) k) S)
    (measurable_of_countable (fun ω ↦ gradient (problemMoreauEnvelope P)
      (persistentSampleOutput (b := b) (S := S) P y0 hy0 q k ω)))
    Integrable.of_finite p.epsilon_pos hmean
  apply lt_of_lt_of_le hs
  apply measureReal_mono
  · intro ω hω
    have hg := P.moreau_hasGradientAt hAS (persistentSampleOutput (b := b) (S := S) P y0 hy0 q k ω)
    refine ⟨_, hg, ?_⟩
    rw [← hg.gradient]
    exact le_of_lt hω
  · exact measure_ne_top _ _

end

end NCConcave16991
