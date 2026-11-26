import NCConcave16991.SaddleProx
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual center-gradient bound from vanishing dual regularization

The proof uses the constructed regularized saddle for every positive μ≤L,
then lets μ→0. No convex maximum rule or subgradient selection is assumed.
-/

noncomputable section

open Set Filter
open scoped InnerProductSpace Topology

namespace NCConcave16991.Accelerated

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

/-- The actual primal partial derivative of the actual finite-sum objective. -/
def primalMeanGradient (P : Problem p dx dy K) (x : PrimalSpace dx) (y : DualSpace dy) : PrimalSpace dx :=
  (averageMap P.componentGradient (jointPoint x y)).fst

/-- Since the primal domain is the whole space, its component of the VI is an actual zero. -/
theorem saddle_primal_gradient_zero (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (c : PrimalSpace dx) (z : JointSpace dx dy)
    (hz : VariationalInequality.IsSolution (productDomain dx K) (tiltedSaddleOperator P μ y0 c 0) z) :
    saddlePrimalGradient P c z = 0 := by
  let g := saddlePrimalGradient P c z
  have hv := hz.2 (jointPoint (z.fst - g) z.snd) hz.1
  simp only [tiltedSaddleOperator, add_zero] at hv
  change 0 ≤ ⟪g, z.fst - g - z.fst⟫_ℝ + ⟪-saddleDualGradient P μ y0 z, z.snd - z.snd⟫_ℝ at hv
  have hid : z.fst - g - z.fst = -g := by abel
  rw [hid, inner_neg_right, real_inner_self_eq_norm_sq] at hv
  simp only [sub_self, inner_zero_right, add_zero] at hv
  have hn : ‖g‖ = 0 := by nlinarith [norm_nonneg g]
  exact norm_eq_zero.mp hn

 theorem primalMeanGradient_at_saddle (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (c : PrimalSpace dx) (z : JointSpace dx dy)
    (hz : VariationalInequality.IsSolution (productDomain dx K) (tiltedSaddleOperator P μ y0 c 0) z) :
    primalMeanGradient P z.fst z.snd = (2 * p.L) • (c - z.fst) := by
  have hg := saddle_primal_gradient_zero P μ y0 c z hz
  change (averageMap P.componentGradient z).fst + (2 * p.L) • (z.fst - c) = 0 at hg
  have he := eq_neg_of_add_eq_zero_left hg
  change (averageMap P.componentGradient z).fst = _
  rw [he]
  module

 theorem primalMeanGradient_joint_lipschitz (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (x u : PrimalSpace dx) (y v : DualSpace dy) (hy : y ∈ K.carrier) (hv : v ∈ K.carrier) :
    ‖primalMeanGradient P x y - primalMeanGradient P u v‖ ≤
      p.L * ‖jointPoint x y - jointPoint u v‖ := by
  have hp := WithLp.norm_fst_le (PrimalSpace dx)
    (averageMap P.componentGradient (jointPoint x y) - averageMap P.componentGradient (jointPoint u v))
  exact hp.trans (P.average_gradient_lipschitz hAS _ hy _ hv)

/-- The actual regularized saddle controls all actual original primal gradients at the center. -/
theorem center_gradient_from_saddle (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (μ : ℝ) (y0 : DualSpace dy) (c : PrimalSpace dx) (z : JointSpace dx dy)
    (hz : VariationalInequality.IsSolution (productDomain dx K) (tiltedSaddleOperator P μ y0 c 0) z)
    (y : DualSpace dy) (hy : y ∈ K.carrier) :
    ‖primalMeanGradient P c y‖ ≤ 3 * p.L * ‖c - z.fst‖ + p.L * p.diameter := by
  have hY := primalMeanGradient_joint_lipschitz P hAS c c y z.snd hy hz.1
  have hX := primalMeanGradient_joint_lipschitz P hAS c z.fst z.snd z.snd hz.1 hz.1
  have hdY : ‖jointPoint c y - jointPoint c z.snd‖ = ‖y - z.snd‖ := by
    change ‖WithLp.toLp 2 (c - c, y - z.snd)‖ = _
    rw [sub_self, WithLp.norm_toLp_snd]
  have hdX : ‖jointPoint c z.snd - jointPoint z.fst z.snd‖ = ‖c - z.fst‖ := by
    change ‖WithLp.toLp 2 (c - z.fst, z.snd - z.snd)‖ = _
    rw [sub_self, WithLp.norm_toLp_fst]
  rw [hdY] at hY
  rw [hdX] at hX
  have hbY := mul_le_mul_of_nonneg_left (K.diameter_bound y hy z.snd hz.1) p.L_pos.le
  have htri := norm_add_le (primalMeanGradient P c y - primalMeanGradient P c z.snd)
    (primalMeanGradient P c z.snd - primalMeanGradient P z.fst z.snd)
  rw [sub_add_sub_cancel] at htri
  have hnorm := norm_add_le (primalMeanGradient P c y - primalMeanGradient P z.fst z.snd)
    (primalMeanGradient P z.fst z.snd)
  rw [sub_add_cancel] at hnorm
  have hL := p.L_pos
  have hs : ‖primalMeanGradient P z.fst z.snd‖ = 2 * p.L * ‖c - z.fst‖ := by
    rw [primalMeanGradient_at_saddle P μ y0 c z hz, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * p.L)]
  nlinarith

/-- The original gap gives the required Ψ gap with the explicit dual-regularization loss. -/
theorem regularized_saddle_distance_gap (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ Δ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ) :
    p.L * ‖(tiltedSaddleSolution P hAS hμ hμL y0 c 0).fst - c‖ ^ 2 ≤ Δ + μ * p.diameter ^ 2 / 2 := by
  let z := tiltedSaddleSolution P hAS hμ hμL y0 c 0
  have hs := tiltedSaddleSolution_spec P hAS hμ hμL y0 c 0
  have hp := saddleVI_primal_isProxPoint P hAS hμ.le y0 c z hs
  have hc := dualRegularizedValue_comparison P hμ.le y0 hy0 c
  have hz := dualRegularizedValue_comparison P hμ.le y0 hy0 z.fst
  have hmin := csInf_le P.value_bddBelow (mem_range_self z.fst)
  have hΨ : dualRegularizedValue P μ y0 c - dualRegularizedValue P μ y0 z.fst ≤
      Δ + μ * p.diameter ^ 2 / 2 := by linarith
  exact proxPoint_gap_bound hp hΨ

/-- Before taking μ→0, every gradient has a uniform explicit regularized bound. -/
theorem center_gradient_regularized_bound (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ Δ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ)
    (y : DualSpace dy) (hy : y ∈ K.carrier) :
    ‖primalMeanGradient P c y‖ ≤ 3 * Real.sqrt (p.L * (Δ + μ * p.diameter ^ 2 / 2)) + p.L * p.diameter := by
  let z := tiltedSaddleSolution P hAS hμ hμL y0 c 0
  have hd := regularized_saddle_distance_gap P hAS hμ hμL y0 hy0 c hgap
  have hg := center_gradient_from_saddle P hAS μ y0 c z
    (tiltedSaddleSolution_spec P hAS hμ hμL y0 c 0) y hy
  have hmin := csInf_le P.value_bddBelow (mem_range_self c)
  have hΔ : 0 ≤ Δ := by linarith
  have hL := p.L_pos
  have hrad : 0 ≤ p.L * (Δ + μ * p.diameter ^ 2 / 2) := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (p.L * (Δ + μ * p.diameter ^ 2 / 2))
  have hscaled := mul_le_mul_of_nonneg_left hd p.L_pos.le
  rw [norm_sub_rev] at hscaled
  have hb : p.L * ‖c - z.fst‖ ≤ Real.sqrt (p.L * (Δ + μ * p.diameter ^ 2 / 2)) := by
    nlinarith [norm_nonneg (c - z.fst), mul_nonneg p.L_pos.le (norm_nonneg (c - z.fst))]
  linarith

/-- Lemma C.3's exact center-gradient bound, using actual regularized saddle solutions and a limit. -/
theorem center_gradient_bound (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {Δ : ℝ} (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ)
    (y : DualSpace dy) (hy : y ∈ K.carrier) :
    ‖primalMeanGradient P c y‖ ≤ 3 * Real.sqrt (p.L * Δ) + p.L * p.diameter := by
  have hμ (j : ℕ) : 0 < p.L / ((j : ℝ) + 1) := div_pos p.L_pos (by positivity)
  have hμL (j : ℕ) : p.L / ((j : ℝ) + 1) ≤ p.L := by
    apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
    nlinarith [mul_nonneg p.L_pos.le (Nat.cast_nonneg j)]
  have hb (j : ℕ) := center_gradient_regularized_bound P hAS (hμ j) (hμL j) y0 hy0 c hgap y hy
  have hm : Tendsto (fun j : ℕ ↦ p.L / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ ↦ p.L * (1 / ((j : ℝ) + 1))) atTop (𝓝 (p.L * 0)))
  have hc : Continuous (fun t : ℝ ↦ 3 * Real.sqrt (p.L * (Δ + t * p.diameter ^ 2 / 2)) + p.L * p.diameter) := by fun_prop
  have hl := hc.continuousAt.tendsto.comp hm
  have hl' : Tendsto (fun j : ℕ ↦ 3 * Real.sqrt (p.L * (Δ + (p.L / ((j : ℝ) + 1)) * p.diameter ^ 2 / 2)) + p.L * p.diameter)
      atTop (𝓝 (3 * Real.sqrt (p.L * Δ) + p.L * p.diameter)) := by simpa [Function.comp_def] using hl
  exact ge_of_tendsto' hl' hb

end NCConcave16991.Accelerated

