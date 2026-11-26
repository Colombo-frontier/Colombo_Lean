import MinimaxAudit.SourceGapParameters

/-! Product-domain gap obstruction for the actual gated source objective.
The proof constructs its interior saddle and feasible comparison points; no
ideal gain or uniform perturbation inequality is an assumed field. -/
open Set Metric
open scoped ContDiff RealInnerProductSpace
namespace MinimaxAudit
set_option maxHeartbeats 2000000
section ActualGap
variable {n dx dy : ℕ} {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
variable (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)

theorem source_product_gap_lower (profile : GateProfile) {tau lam c R : ℝ}
    (htau : 0 < tau) (hlam : 0 < lam) (hR : 0 < R)
    (hc : c = geometryKappa * R / Real.sqrt (n+1))
    (ht : tau = geometryEta * c / (n+1 : ℝ))
    (z : SaddleSpace dx dy)
    (hz : z ∈ productDomain (closedBall (0 : Primal dx) R) (closedBall (0 : Dual dy) R))
    (hr : |pairedA U V (Fin.last n) z| ≤ tau) :
    lam * c ^ 2 / 16 ≤
      auditedSaddleGap (closedBall (0 : Primal dx) R) (closedBall (0 : Dual dy) R)
        (fun x y => minimaxHardPotential profile tau lam (balancedQ n) c hU hV (joinBlocks x y))
        (primalBlock z) (dualBlock z) := by
  let phi := minimaxHardPotential profile tau lam (balancedQ n) c hU hV
  let x := primalBlock z
  let y := dualBlock z
  have hxy : joinBlocks x y = z := join_blocks z
  have hc0 : 0 ≤ c := by rw [hc]; unfold geometryKappa; positivity
  have hq0 := balancedQ_nonneg n
  have hq1 := balancedQ_le_one n
  have hk : 0 ≤ geometryKappa := by norm_num [geometryKappa]
  have hC : ContDiff ℝ ∞ phi := framedHardPotential_contDiff profile htau.ne'
    lam (balancedQ n) c (euclideanSaddleSign dx dy)
    (blockPairedFrame_orthonormal hU hV) (Fin.last n)
  have hd : Differentiable ℝ phi := hC.differentiable (by simp)
  have hm : ∀ v w, lam * (1 - balancedQ n) * ‖v - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi v - scalarSaddleOperator phi w) (v - w) :=
    minimaxHardPotential_strong_monotone profile htau.ne' hq0 hlam.le hU hV
  change ‖primalBlock z - 0‖ ≤ R ∧ ‖dualBlock z - 0‖ ≤ R at hz
  simp only [sub_zero] at hz
  have hxR : ‖x‖ ≤ R := hz.1
  have hyR : ‖y‖ ≤ R := hz.2
  have hneX : (closedBall (0 : Primal dx) R).Nonempty := ⟨0, by simpa using hR.le⟩
  have hneY : (closedBall (0 : Dual dy) R).Nonempty := ⟨0, by simpa using hR.le⟩
  have hb := saddle_differences_bddAbove_of_compact (fun u v => phi (joinBlocks u v))
    (isCompact_closedBall 0 R) (isCompact_closedBall 0 R) hneX hneY x y
    (hd.continuous.comp (continuous_join_primal y)).continuousOn
    (hd.continuous.comp (continuous_join_dual x)).continuousOn
  by_cases hinner : ‖x‖ ≤ R - 2 * geometryKappa * R ∧ ‖y‖ ≤ R - 2 * geometryKappa * R
  · let s := balancedQ n ^ n * c - pairedA U V (Fin.last n) (joinBlocks x y)
    have hs : s = balancedQ n ^ n * c - pairedA U V (Fin.last n) (joinBlocks x y) := rfl
    have ha : |pairedA U V (Fin.last n) (joinBlocks x y)| ≤ tau := by rwa [hxy]
    have hsb := source_deficit_bounds hc0 ht ha hs
    have hs0 : 0 ≤ s := (by positivity : 0 ≤ c / 2).trans hsb.1
    have hdx := source_weightWitness_small hU hR.le hc0 hc ht hs0 hsb.2
    have hdy := source_weightWitness_small hV hR.le hc0 hc ht hs0 hsb.2
    have hxf : ‖x + weightWitness hU (balancedQ n) s‖ ≤ R :=
      (norm_add_le _ _).trans (by nlinarith [hinner.1, mul_nonneg hk hR.le])
    have hyf : ‖y + weightWitness hV (balancedQ n) s‖ ≤ R :=
      (norm_add_le _ _).trans (by nlinarith [hinner.2, mul_nonneg hk hR.le])
    have hxf' : x + weightWitness hU (balancedQ n) s ∈ closedBall (0 : Primal dx) R := by simpa using hxf
    have hyf' : y + weightWitness hV (balancedQ n) s ∈ closedBall (0 : Dual dy) R := by simpa using hyf
    have heD := uniform_product_potential_approximation profile htau hlam.le hq0 hq1 hR.le c hU hV
      x (y + weightWitness hV (balancedQ n) s) hxR hyf
    have heP := uniform_product_potential_approximation profile htau hlam.le hq0 hq1 hR.le c hU hV
      (x + weightWitness hU (balancedQ n) s) y hxf hyR
    have hideal := idealHardPotential_witness_exact lam (balancedQ n) c s hU hV x y hs
    have hg := saddleGap_stability_at_witness
      (phi0 := fun u v => idealHardPotential lam (balancedQ n) c U V (joinBlocks u v))
      hb hxf' hyf' heD heP (le_of_eq hideal.symm)
    have hquad : lam * c ^ 2 / 8 ≤ lam / 2 * s ^ 2 := by
      have hsquares : c ^ 2 / 4 ≤ s ^ 2 := by nlinarith [hsb.1]
      have hmul := mul_le_mul_of_nonneg_left hsquares (show 0 ≤ lam / 2 by positivity)
      nlinarith
    have hpt := source_parameter_perturbation_identity hc ht
    have hpert : 3 * lam * tau * R * Real.sqrt (n+1) =
        3 * (geometryEta / geometryKappa) * (lam * c ^ 2) := by
      calc
        _ = 3 * lam * (tau * R * Real.sqrt (n+1)) := by ring
        _ = _ := by rw [hpt]; ring
    rw [hpert] at hg
    have hconst : (1 : ℝ) / 16 ≤ 1 / 8 - 6 * (geometryEta / geometryKappa) := by
      norm_num [geometryEta, geometryKappa]
    have hmul := mul_le_mul_of_nonneg_right hconst (show 0 ≤ lam * c ^ 2 by positivity)
    change lam * c ^ 2 / 16 ≤ auditedSaddleGap _ _ (fun u v => phi (joinBlocks u v)) x y
    nlinarith
  · have he := framedHardPotential_exists_unique_zero profile (c := c)
      htau.ne' hq0 (balancedQ_lt_one n) hlam
      (euclideanSaddleSign dx dy) (euclideanSaddleSign_involutive dx dy)
      (blockPairedFrame_orthonormal hU hV) (Fin.last n)
    obtain ⟨zstar,hzero,_⟩ := he
    have hz0 : scalarSaddleOperator phi zstar = 0 := hzero
    have hstar := source_zero_inner_radius hU hV profile htau hlam hq0 hq1 hR hc ht zstar hz0
    have hxstar := (source_block_norms_le zstar).1.trans hstar
    have hystar := (source_block_norms_le zstar).2.trans hstar
    have hstarfeasible := source_inner_zero_feasible hR.le hstar
    have hz0' : scalarSaddleOperator phi (joinBlocks (primalBlock zstar) (dualBlock zstar)) = 0 := by
      simpa using hz0
    have hmu : 0 ≤ lam * (1 - balancedQ n) := mul_nonneg hlam.le (sub_nonneg.mpr hq1)
    have hscale : lam * c ^ 2 / 16 ≤ lam * (1 - balancedQ n) * R ^ 2 / 8 := by
      have hnpos : (0 : ℝ) < 32 * (n+1 : ℝ) := by positivity
      have hcn := source_seed_square_identity hc
      have heq : lam * (1 - balancedQ n) * R ^ 2 / 8 =
          lam * R ^ 2 / (32 * (n+1 : ℝ)) := by unfold balancedQ; field_simp; ring
      rw [heq]
      apply (le_div_iff₀ hnpos).2
      have hconst : 2 * geometryKappa ^ 2 ≤ (1 : ℝ) := by norm_num [geometryKappa]
      have hmul := mul_le_mul_of_nonneg_right hconst (show 0 ≤ lam * R ^ 2 by positivity)
      calc
        lam * c ^ 2 / 16 * (32 * (n+1 : ℝ)) = 2 * lam * (c ^ 2 * (n+1 : ℝ)) := by ring
        _ = 2 * geometryKappa ^ 2 * (lam * R ^ 2) := by rw [hcn]; ring
        _ ≤ 1 * (lam * R ^ 2) := hmul
        _ = _ := one_mul _
    simp only [not_and_or, not_le] at hinner
    rcases hinner with hxouter | hyouter
    · have hdist : R / 2 ≤ ‖x - primalBlock zstar‖ := by
        have ht := norm_le_norm_sub_add x (primalBlock zstar)
        norm_num [geometryKappa] at hxouter
        nlinarith
      have hg := saddle_strong_primal_shell_gap_lower phi hd (lam * (1-balancedQ n)) hmu hm
        (isCompact_closedBall 0 R) (isCompact_closedBall 0 R)
        (primalBlock zstar) (dualBlock zstar) hstarfeasible.1 hstarfeasible.2 hz0'
        x y R hR.le hdist
      exact hscale.trans hg
    · have hdist : R / 2 ≤ ‖y - dualBlock zstar‖ := by
        have ht := norm_le_norm_sub_add y (dualBlock zstar)
        norm_num [geometryKappa] at hyouter
        nlinarith
      have hg := saddle_strong_dual_shell_gap_lower phi hd (lam * (1-balancedQ n)) hmu hm
        (isCompact_closedBall 0 R) (isCompact_closedBall 0 R)
        (primalBlock zstar) (dualBlock zstar) hstarfeasible.1 hstarfeasible.2 hz0'
        x y R hR.le hdist
      exact hscale.trans hg

end ActualGap
end MinimaxAudit
