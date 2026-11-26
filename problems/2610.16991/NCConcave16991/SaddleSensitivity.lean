import NCConcave16991.SaddleOperator
import NCConcave16991.VariationalInequality

/-! # Existence, uniqueness, and sharp primal sensitivity of the biased saddle -/

open Set InnerProductSpace
open scoped InnerProductSpace NNReal

namespace NCConcave16991

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

theorem productDomain_nonempty (dx : ℕ) (K : KnownDualDomain dy p.diameter) :
    (productDomain dx K).Nonempty := by
  obtain ⟨y, hy⟩ := K.nonempty
  exact ⟨jointPoint 0 y, hy⟩

theorem productDomain_closed (dx : ℕ) (K : KnownDualDomain dy p.diameter) :
    IsClosed (productDomain dx K) :=
  K.compact.isClosed.preimage (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous

theorem productDomain_convex (dx : ℕ) (K : KnownDualDomain dy p.diameter) :
    Convex ℝ (productDomain dx K) :=
  K.convex.linear_preimage (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).toLinearMap

def tiltedSaddleOperator (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (c : PrimalSpace dx) (ξ z : JointSpace dx dy) : JointSpace dx dy :=
  saddleOperator P μ y0 c z + ξ

/-- The actual tilted problem has a unique VI solution, constructed using the
closed-convex projection and Banach contraction theorem. -/
theorem existsUnique_tiltedSaddle (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (ξ : JointSpace dx dy) :
    ∃! z : JointSpace dx dy, VariationalInequality.IsSolution (productDomain dx K)
      (tiltedSaddleOperator P μ y0 c ξ) z := by
  have hL := p.L_pos
  let C : ℝ≥0 := NNReal.mk (3 * p.L) (by positivity)
  apply VariationalInequality.existsUnique_solution (productDomain dx K)
    (productDomain_nonempty dx K) (productDomain_closed dx K) (productDomain_convex dx K)
    (tiltedSaddleOperator P μ y0 c ξ) C hμ
  · apply LipschitzOnWith.of_dist_le_mul
    intro z hz z' hz'
    have he : tiltedSaddleOperator P μ y0 c ξ z - tiltedSaddleOperator P μ y0 c ξ z' =
        saddleOperator P μ y0 c z - saddleOperator P μ y0 c z' := by
      dsimp [tiltedSaddleOperator]
      abel
    simpa only [dist_eq_norm, he, C, NNReal.coe_mk] using
      saddleOperator_lipschitz P hAS hμ.le hμL y0 c z z' hz hz'
  · intro z hz z' hz'
    have hm := saddleOperator_anisotropic_monotone P hAS μ y0 c z z' hz hz'
    have hdiff : tiltedSaddleOperator P μ y0 c ξ z - tiltedSaddleOperator P μ y0 c ξ z' =
        saddleOperator P μ y0 c z - saddleOperator P μ y0 c z' := by
      dsimp [tiltedSaddleOperator]
      abel
    rw [hdiff]
    apply le_trans _ hm
    rw [joint_difference_norm_sq]
    nlinarith only [mul_le_mul_of_nonneg_right hμL (sq_nonneg ‖z.fst - z'.fst‖)]

def tiltedSaddleSolution (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (ξ : JointSpace dx dy) : JointSpace dx dy :=
  Classical.choose (existsUnique_tiltedSaddle P hAS hμ hμL y0 c ξ)

theorem tiltedSaddleSolution_spec (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (ξ : JointSpace dx dy) :
    VariationalInequality.IsSolution (productDomain dx K) (tiltedSaddleOperator P μ y0 c ξ)
      (tiltedSaddleSolution P hAS hμ hμL y0 c ξ) :=
  (Classical.choose_spec (existsUnique_tiltedSaddle P hAS hμ hμL y0 c ξ)).1

private theorem weighted_young (a u L : ℝ) (hL : 0 < L) :
    2 * a * u ≤ L * u ^ 2 + a ^ 2 / L := by
  apply (mul_le_mul_iff_right₀ hL).mp
  have hc : a ^ 2 / L * L = a ^ 2 := div_mul_cancel₀ _ hL.ne'
  nlinarith only [sq_nonneg (L * u - a), hc]

/-- Testing the two actual variational inequalities against each other yields
the sharp anisotropic bias sensitivity in Lemma B.1. -/
theorem saddleVI_primal_sensitivity (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (ξ z0 zξ : JointSpace dx dy)
    (h0 : VariationalInequality.IsSolution (productDomain dx K) (tiltedSaddleOperator P μ y0 c 0) z0)
    (hξ : VariationalInequality.IsSolution (productDomain dx K) (tiltedSaddleOperator P μ y0 c ξ) zξ) :
    ‖zξ.fst - z0.fst‖ ^ 2 ≤ ‖ξ.fst‖ ^ 2 / p.L ^ 2 + ‖ξ.snd‖ ^ 2 / (p.L * μ) := by
  have ht0 := h0.2 zξ hξ.1
  have htξ := hξ.2 z0 h0.1
  have hm := saddleOperator_anisotropic_monotone P hAS μ y0 c zξ z0 hξ.1 h0.1
  have he : z0 - zξ = -(zξ - z0) := by abel
  simp only [tiltedSaddleOperator, add_zero] at ht0
  rw [he, inner_neg_right] at htξ
  simp only [tiltedSaddleOperator, inner_add_left] at htξ
  rw [inner_sub_left] at hm
  have hW : p.L * ‖zξ.fst - z0.fst‖ ^ 2 + μ * ‖zξ.snd - z0.snd‖ ^ 2 ≤
      -⟪ξ, zξ - z0⟫_ℝ := by linarith only [ht0, htξ, hm]
  have hx := real_inner_le_norm (-ξ.fst) (zξ.fst - z0.fst)
  have hy := real_inner_le_norm (-ξ.snd) (zξ.snd - z0.snd)
  simp only [inner_neg_left, norm_neg] at hx hy
  have hXi : -⟪ξ, zξ - z0⟫_ℝ ≤
      ‖ξ.fst‖ * ‖zξ.fst - z0.fst‖ + ‖ξ.snd‖ * ‖zξ.snd - z0.snd‖ := by
    change -(⟪ξ.fst, zξ.fst - z0.fst⟫_ℝ + ⟪ξ.snd, zξ.snd - z0.snd⟫_ℝ) ≤ _
    linarith only [hx, hy]
  have hxy := hW.trans hXi
  have hYoungx := weighted_young ‖ξ.fst‖ ‖zξ.fst - z0.fst‖ p.L p.L_pos
  have hYoungy := weighted_young ‖ξ.snd‖ ‖zξ.snd - z0.snd‖ μ hμ
  have hWbound : p.L * ‖zξ.fst - z0.fst‖ ^ 2 + μ * ‖zξ.snd - z0.snd‖ ^ 2 ≤
      ‖ξ.fst‖ ^ 2 / p.L + ‖ξ.snd‖ ^ 2 / μ := by linarith only [hxy, hYoungx, hYoungy]
  have hprimal : p.L * ‖zξ.fst - z0.fst‖ ^ 2 ≤ ‖ξ.fst‖ ^ 2 / p.L + ‖ξ.snd‖ ^ 2 / μ := by
    linarith only [hWbound, mul_nonneg hμ.le (sq_nonneg ‖zξ.snd - z0.snd‖)]
  have hid : ‖ξ.fst‖ ^ 2 / p.L ^ 2 + ‖ξ.snd‖ ^ 2 / (p.L * μ) =
      (‖ξ.fst‖ ^ 2 / p.L + ‖ξ.snd‖ ^ 2 / μ) / p.L := by
    field_simp [p.L_pos.ne', hμ.ne'] <;> ring
  rw [hid]
  apply (le_div_iff₀ p.L_pos).2
  nlinarith only [hprimal]

/-- The existence theorem supplies both VI hypotheses, giving the sensitivity
bound directly for the canonically constructed unbiased and biased solutions. -/
theorem tiltedSaddleSolution_primal_sensitivity (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (ξ : JointSpace dx dy) :
    ‖(tiltedSaddleSolution P hAS hμ hμL y0 c ξ).fst -
        (tiltedSaddleSolution P hAS hμ hμL y0 c 0).fst‖ ^ 2 ≤
      ‖ξ.fst‖ ^ 2 / p.L ^ 2 + ‖ξ.snd‖ ^ 2 / (p.L * μ) :=
  saddleVI_primal_sensitivity P hAS hμ y0 c ξ _ _
    (tiltedSaddleSolution_spec P hAS hμ hμL y0 c 0)
    (tiltedSaddleSolution_spec P hAS hμ hμL y0 c ξ)

end

end NCConcave16991
