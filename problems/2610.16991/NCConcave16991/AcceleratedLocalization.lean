import NCConcave16991.AcceleratedCenterGradient
import NCConcave16991.AcceleratedProblem

/-! # A genuine compact primal ball for the original proximal subproblem -/

noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace NCConcave16991.Accelerated

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Radial projection onto the sphere of radius R, used only outside that ball. -/
def radialPoint (R : ℝ) (c x : E) : E := c + (R / ‖x - c‖) • (x - c)

 theorem radialPoint_distance {R : ℝ} (hR : 0 < R) {c x : E} (hx : R < ‖x - c‖) :
    ‖radialPoint R c x - c‖ = R := by
  have hd : 0 < ‖x - c‖ := hR.trans hx
  have he : radialPoint R c x - c = (R / ‖x - c‖) • (x - c) := by dsimp [radialPoint]; abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hd), div_mul_cancel₀ _ hd.ne']

/-- Strong convexity and the actual center gradient prove strict radial decrease.
This is a deterministic first-order comparison, rather than a localization assumption. -/
theorem strongConvex_radial_decrease {f : E → ℝ} {L M R : ℝ} {c x g : E}
    (hL : 0 < L) (hR : 0 < R) (hMR : M < L * R)
    (hf : StrongConvexOn univ L f) (hg : HasGradientAt f g c) (hgrad : ‖g‖ ≤ M)
    (hx : R < ‖x - c‖) : f (radialPoint R c x) < f x := by
  let t := ‖x - c‖
  let θ := R / t
  have ht : 0 < t := hR.trans hx
  have hθpos : 0 < θ := div_pos hR ht
  have hθlt : θ < 1 := (div_lt_one ht).mpr hx
  have hθt : θ * t = R := div_mul_cancel₀ _ ht.ne'
  have hcomb : (1 - θ) • c + θ • x = radialPoint R c x := by dsimp [radialPoint, θ, t]; module
  have hc := hf.2 (mem_univ c) (mem_univ x) (sub_nonneg.mpr hθlt.le) hθpos.le
    (show 1 - θ + θ = 1 by ring)
  rw [hcomb, norm_sub_rev c x] at hc
  have hs := strongConvex_gradient_support hf (mem_univ c) (mem_univ x) hg
  have hi := real_inner_le_norm (-g) (x - c)
  simp only [inner_neg_left, norm_neg] at hi
  have hm := mul_le_mul_of_nonneg_right hgrad (norm_nonneg (x - c))
  have hlow : -M * t + L / 2 * t ^ 2 ≤ f x - f c := by nlinarith
  have hlow' := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr hθlt.le)
  have htR : L * R < L * t := mul_lt_mul_of_pos_left hx hL
  have hinside : 0 < L / 2 * (1 + θ) * t ^ 2 - M * t := by
    have htθ := congrArg (fun u : ℝ ↦ u * t) hθt
    have he : L / 2 * (1 + θ) * t ^ 2 - M * t = t * (L / 2 * (t + R) - M) := by nlinarith
    rw [he]
    exact mul_pos ht (by nlinarith)
  have hpositive := mul_pos (sub_pos.mpr hθlt) hinside
  change f (radialPoint R c x) ≤ (1 - θ) * f c + θ * f x - (1 - θ) * θ * (L / 2 * t ^ 2) at hc
  nlinarith

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

/-- Beyond the explicit center-gradient radius, radial projection decreases every actual saddle section. -/
theorem actual_proximal_radial_decrease (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {Δ R : ℝ} (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ)
    (hR : 0 < R) (hMR : 3 * Real.sqrt (p.L * Δ) + p.L * p.diameter < p.L * R)
    (x : PrimalSpace dx) (hx : R < ‖x - c‖) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    saddleObjective P 0 y0 c (radialPoint R c x) y < saddleObjective P 0 y0 c x y := by
  apply strongConvex_radial_decrease p.L_pos hR hMR (saddle_primal_stronglyConvex P hAS 0 y0 c y hy)
  · simpa [saddlePrimalGradient, primalMeanGradient] using saddle_primal_hasGradientAt P 0 y0 c c y hy
  · simpa [saddlePrimalGradient, primalMeanGradient, jointPoint] using center_gradient_bound P hAS y0 hy0 c hgap y hy
  · exact hx

/-- The actual unrestricted proximal minimizer is contained in the known compact ball. -/
theorem actual_proximalMap_mem_ball (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {Δ R : ℝ} (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ)
    (hR : 0 < R) (hMR : 3 * Real.sqrt (p.L * Δ) + p.L * p.diameter < p.L * R) :
    proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c ∈ closedBall c R := by
  let x := proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c
  have hp := proximalMap_spec p.L_pos (P.primal_continuous hAS) P.value_bddBelow c
  by_contra hn
  have hx : R < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hn
  let q := radialPoint R c x
  obtain ⟨y, hy, he⟩ := P.exists_dual_maximizer q
  have hd := actual_proximal_radial_decrease P hAS y0 hy0 c hgap hR hMR x hx y hy
  have hcost := hp q
  have hb : componentAverage P.component (jointPoint x y) ≤ primalObjective K P.component x :=
    le_csSup (K.compact.image_of_continuousOn (P.average_dual_continuous x)).bddAbove ⟨y, hy, rfl⟩
  simp only [saddleObjective, dualRegularizedSection, zero_div, zero_mul, sub_zero] at hd
  change componentAverage P.component (jointPoint q y) + p.L * ‖q - c‖ ^ 2 <
    componentAverage P.component (jointPoint x y) + p.L * ‖x - c‖ ^ 2 at hd
  change primalObjective K P.component x + p.L * ‖x - c‖ ^ 2 ≤
    primalObjective K P.component q + p.L * ‖q - c‖ ^ 2 at hcost
  rw [he] at hcost
  linarith

end NCConcave16991.Accelerated

