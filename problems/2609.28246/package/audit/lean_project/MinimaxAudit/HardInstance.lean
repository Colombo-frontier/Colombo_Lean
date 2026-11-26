import MinimaxAudit.SourceNormal

/-! Actual admissible scalar minimax instances on the manuscript's public
product balls. Every analytic clause is proved for the concrete potential;
AdmissibleScalar is not an input assumption. -/

open scoped ContDiff

namespace MinimaxAudit

/-- Exact Euclidean product norm decomposition. -/
theorem source_norm_sq_blocks {dx dy : ℕ} (z : SaddleSpace dx dy) :
    ‖z‖ ^ 2 = ‖primalBlock z‖ ^ 2 + ‖dualBlock z‖ ^ 2 := by
  have h := join_blocks_inner (primalBlock z) (primalBlock z) (dualBlock z) (dualBlock z)
  rw [join_blocks z] at h
  simpa only [real_inner_self_eq_norm_sq] using h

/-- Public product balls have the correct L2 diameter upper bound. -/
theorem productBall_diameter_bound {dx dy : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {z w : SaddleSpace dx dy}
    (hz : z ∈ productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R))
    (hw : w ∈ productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R)) :
    ‖z - w‖ ≤ 2 * Real.sqrt 2 * R := by
  change ‖primalBlock z - 0‖ ≤ R ∧ ‖dualBlock z - 0‖ ≤ R at hz
  change ‖primalBlock w - 0‖ ≤ R ∧ ‖dualBlock w - 0‖ ≤ R at hw
  simp only [sub_zero] at hz hw
  have hx : ‖primalBlock z - primalBlock w‖ ≤ 2 * R :=
    (norm_sub_le _ _).trans (by linarith)
  have hy : ‖dualBlock z - dualBlock w‖ ≤ 2 * R :=
    (norm_sub_le _ _).trans (by linarith)
  have hs := source_norm_sq_blocks (z - w)
  rw [source_primal_sub, source_dual_sub] at hs
  have hx0 := norm_nonneg (primalBlock z - primalBlock w)
  have hy0 := norm_nonneg (dualBlock z - dualBlock w)
  have hx2 : ‖primalBlock z - primalBlock w‖ ^ 2 ≤ 4 * R ^ 2 := by nlinarith
  have hy2 : ‖dualBlock z - dualBlock w‖ ^ 2 ≤ 4 * R ^ 2 := by nlinarith
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := norm_nonneg (z - w)
  have htarget : 0 ≤ 2 * Real.sqrt 2 * R := by positivity
  nlinarith

/-- Opposite feasible points attain the public product-ball diameter, using
one actual unit vector from each orthonormal frame. -/
theorem productBall_diameter_exact {n dx dy : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) :
    Metric.diam (productDomain (Metric.closedBall (0 : Primal dx) R)
      (Metric.closedBall (0 : Dual dy) R)) = 2 * Real.sqrt 2 * R := by
  let Z := productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R)
  let z := joinBlocks (R • U 0) (R • V 0)
  let w := joinBlocks ((-R) • U 0) ((-R) • V 0)
  have hz : z ∈ Z := by
    simp [Z, z, productDomain, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR, hU.norm_eq_one, hV.norm_eq_one]
  have hw : w ∈ Z := by
    simp [Z, w, productDomain, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR, hU.norm_eq_one, hV.norm_eq_one]
  have hdist : dist z w = 2 * Real.sqrt 2 * R := by
    rw [dist_eq_norm]
    have hx : primalBlock (z - w) = (2 * R) • U 0 := by
      ext i
      simp [z, w, joinBlocks, primalBlock]
      ring
    have hy : dualBlock (z - w) = (2 * R) • V 0 := by
      ext i
      simp [z, w, joinBlocks, dualBlock]
      ring
    have hsq := source_norm_sq_blocks (z - w)
    rw [hx, hy, norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg zero_le_two hR), hU.norm_eq_one, hV.norm_eq_one, mul_one] at hsq
    have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := norm_nonneg (z - w)
    have htarget : 0 ≤ 2 * Real.sqrt 2 * R := by positivity
    nlinarith
  have hall : ∀ x ∈ Z, ∀ y ∈ Z, dist x y ≤ 2 * Real.sqrt 2 * R := by
    intro x hx y hy
    simpa only [dist_eq_norm] using productBall_diameter_bound hR hx hy
  have htop : Metric.ediam Z ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Metric.ediam_le_of_forall_dist_le hall)
  have hlo := Metric.dist_le_diam_of_mem' htop hz hw
  rw [hdist] at hlo
  exact le_antisymm (Metric.diam_le_of_forall_dist_le (by positivity) hall) hlo

noncomputable def hardSeed (n : ℕ) (R : ℝ) : ℝ :=
  geometryKappa * R / Real.sqrt (n + 1)

noncomputable def hardGateWidth (n : ℕ) (R : ℝ) : ℝ :=
  geometryEta * hardSeed n R / (n + 1 : ℝ)

noncomputable def hardAmplitude (profile : GateProfile) (p n : ℕ) (L R : ℝ) : ℝ :=
  L * hardGateWidth n R ^ (p - 1) / chainSmoothnessConstant p profile

theorem hardSeed_pos (n : ℕ) {R : ℝ} (hR : 0 < R) : 0 < hardSeed n R := by
  unfold hardSeed geometryKappa
  positivity

theorem hardGateWidth_pos (n : ℕ) {R : ℝ} (hR : 0 < R) : 0 < hardGateWidth n R := by
  unfold hardGateWidth geometryEta
  exact div_pos (mul_pos (by norm_num) (hardSeed_pos n hR)) (by positivity)

theorem hardAmplitude_pos (profile : GateProfile) (p n : ℕ) {L R : ℝ}
    (hL : 0 < L) (hR : 0 < R) : 0 < hardAmplitude profile p n L R := by
  unfold hardAmplitude
  exact div_pos (mul_pos hL (pow_pos (hardGateWidth_pos n hR) _))
    (chainSmoothnessConstant_pos p profile)

/-- Global, not merely feasible-domain, regularity of the calibrated hard
potential. This records the extra global clauses asserted by source main(i). -/
theorem hardInstance_global {n dx dy : ℕ} (profile : GateProfile)
    {p : ℕ} (hp : 2 ≤ p) {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) :
    let phi := minimaxHardPotential profile (hardGateWidth n R) (hardAmplitude profile p n L R)
      (balancedQ n) (hardSeed n R) hU hV
    ContDiff ℝ ∞ phi ∧
    (∀ y : Dual dy, ConvexOn ℝ Set.univ (fun x => phi (joinBlocks x y))) ∧
    (∀ x : Primal dx, ConcaveOn ℝ Set.univ (fun y => phi (joinBlocks x y))) ∧
    (∀ z w : SaddleSpace dx dy, ‖iteratedFDeriv ℝ p phi z - iteratedFDeriv ℝ p phi w‖ ≤ L * ‖z - w‖) := by
  let c := hardSeed n R
  let tau := hardGateWidth n R
  let lam := hardAmplitude profile p n L R
  let phi := minimaxHardPotential profile tau lam (balancedQ n) c hU hV
  let mu := lam * (1 - balancedQ n)
  have htau := hardGateWidth_pos n hR
  have hlam := hardAmplitude_pos profile p n hL hR
  have hmu : 0 ≤ mu := mul_nonneg hlam.le (sub_nonneg.mpr (balancedQ_le_one n))
  have hc : ContDiff ℝ ∞ phi := framedHardPotential_contDiff profile htau.ne'
    lam (balancedQ n) c (euclideanSaddleSign dx dy) (blockPairedFrame_orthonormal hU hV) (Fin.last n)
  have hd : Differentiable ℝ phi := fun z =>
    (framedHardPotential_hasFDerivAt profile htau.ne' lam (balancedQ n) c (euclideanSaddleSign dx dy)
      (euclideanSaddleSign_involutive dx dy) (blockPairedFrame_orthonormal hU hV) (Fin.last n) z).differentiableAt
  have hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w) :=
    minimaxHardPotential_strong_monotone profile (c := c) htau.ne' (balancedQ_nonneg n) hlam.le hU hV
  have hsc := saddle_strong_convex_concave phi hd mu hs
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro y
    exact strongConvexOn_zero.mp (StrongConvexOn.mono hmu (hsc.1 y))
  · intro x
    exact strongConcaveOn_zero.mp (StrongConcaveOn.mono hmu (hsc.2 x))
  · intro z w
    exact minimaxHardPotential_calibrated_smoothness profile hp htau hL.le
      (balancedQ_nonneg n) (balancedQ_le_one n) hU hV w z

/-- The fully concrete source objective belongs to the original admissible
class for all p≥2, all positive L,R, and every actual orthonormal primal/dual frame.
Neither smoothness, convexity, nor saddle existence is supplied as a premise. -/
theorem hardInstance_admissible {n dx dy : ℕ} (profile : GateProfile)
    {p : ℕ} (hp : 2 ≤ p) {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) :
    AdmissibleScalar p L (2 * Real.sqrt 2 * R)
      (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R)
      (minimaxHardPotential profile (hardGateWidth n R) (hardAmplitude profile p n L R)
        (balancedQ n) (hardSeed n R) hU hV) := by
  let c := hardSeed n R
  let tau := hardGateWidth n R
  let lam := hardAmplitude profile p n L R
  let phi := minimaxHardPotential profile tau lam (balancedQ n) c hU hV
  let mu := lam * (1 - balancedQ n)
  have hc : 0 < c := by dsimp [c, hardSeed, geometryKappa]; positivity
  have htau : 0 < tau := by dsimp [tau, hardGateWidth]; unfold geometryEta; positivity
  have hlam : 0 < lam := by
    dsimp [lam, hardAmplitude]
    exact div_pos (mul_pos hL (pow_pos htau _)) (chainSmoothnessConstant_pos p profile)
  have hq0 := balancedQ_nonneg n
  have hq1 := balancedQ_le_one n
  have hqlt : balancedQ n < 1 := by
    unfold balancedQ
    have hd : (0 : ℝ) < 1 / (4 * (n + 1 : ℝ)) := by positivity
    linarith
  have hmu : 0 ≤ mu := mul_nonneg hlam.le (sub_nonneg.mpr hq1)
  have hcont : ContDiff ℝ ∞ phi :=
    framedHardPotential_contDiff profile htau.ne' lam (balancedQ n) c (euclideanSaddleSign dx dy)
      (blockPairedFrame_orthonormal hU hV) (Fin.last n)
  have hdiff : Differentiable ℝ phi := fun z =>
    (framedHardPotential_hasFDerivAt profile htau.ne' lam (balancedQ n) c (euclideanSaddleSign dx dy)
      (euclideanSaddleSign_involutive dx dy) (blockPairedFrame_orthonormal hU hV) (Fin.last n) z).differentiableAt
  have hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w) :=
    fun z w => minimaxHardPotential_strong_monotone profile (c := c) htau.ne' hq0 hlam.le hU hV z w
  have hconvex := saddle_strong_convex_concave phi hdiff mu hs
  have he := framedHardPotential_exists_unique_zero profile (c := c) htau.ne' hq0 hqlt hlam
    (euclideanSaddleSign dx dy) (euclideanSaddleSign_involutive dx dy)
    (blockPairedFrame_orthonormal hU hV) (Fin.last n)
  obtain ⟨zstar, hzero, _⟩ := he
  have hzero' : scalarSaddleOperator phi zstar = 0 := hzero
  have hstar : ‖zstar‖ ≤ R / 8 :=
    source_zero_inner_radius hU hV profile htau hlam hq0 hq1 hR rfl rfl zstar hzero'
  have hzstar := source_inner_zero_feasible hR.le hstar
  have hneX : (Metric.closedBall (0 : Primal dx) R).Nonempty := ⟨0, by simp [hR.le]⟩
  have hneY : (Metric.closedBall (0 : Dual dy) R).Nonempty := ⟨0, by simp [hR.le]⟩
  have hD : 0 < 2 * Real.sqrt 2 * R := by positivity
  refine ⟨hp, hL, hD, hneX, hneY, isCompact_closedBall _ _, isCompact_closedBall _ _,
    convex_closedBall _ _, convex_closedBall _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz w hw
    exact productBall_diameter_bound hR.le hz hw
  · refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩
    exact (contDiff_infty.mp hcont p).contDiffOn
  · intro y _
    have h0 : StrongConvexOn Set.univ 0 (fun x => phi (joinBlocks x y)) :=
      StrongConvexOn.mono hmu (hconvex.1 y)
    exact (strongConvexOn_zero.mp h0).subset (Set.subset_univ _) (convex_closedBall _ _)
  · intro x _
    have h0 : StrongConcaveOn Set.univ 0 (fun y => phi (joinBlocks x y)) :=
      StrongConcaveOn.mono hmu (hconvex.2 x)
    exact (strongConcaveOn_zero.mp h0).subset (Set.subset_univ _) (convex_closedBall _ _)
  · intro z _ w _
    exact minimaxHardPotential_calibrated_smoothness profile hp htau hL.le hq0 hq1 hU hV w z
  · let xstar := primalBlock zstar
    let ystar := dualBlock zstar
    have hzjoin : joinBlocks xstar ystar = zstar := join_blocks zstar
    have hgzero : gradient phi (joinBlocks xstar ystar) = 0 := by
      apply (euclideanSaddleSign dx dy).injective
      simpa only [hzjoin, scalarSaddleOperator, map_zero] using hzero'
    have hpzero : primalBlock (gradient phi (joinBlocks xstar ystar)) = 0 := by
      rw [hgzero]
      ext i
      rfl
    have hdzero : dualBlock (gradient phi (joinBlocks xstar ystar)) = 0 := by
      rw [hgzero]
      ext i
      rfl
    refine ⟨xstar, hzstar.1, ystar, hzstar.2, ?_⟩
    intro u _ v _
    have hP := saddle_strong_primal_support phi hdiff mu hs xstar u ystar
    have hD := saddle_strong_dual_support phi hdiff mu hs xstar ystar v
    rw [hpzero, inner_zero_left, add_zero] at hP
    rw [hdzero, inner_zero_left, add_zero] at hD
    have hnP : 0 ≤ mu / 2 * ‖u - xstar‖ ^ 2 := by positivity
    have hnD : 0 ≤ mu / 2 * ‖v - ystar‖ ^ 2 := by positivity
    constructor <;> linarith

end MinimaxAudit
