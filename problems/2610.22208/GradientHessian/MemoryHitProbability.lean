import GradientHessian.MemoryMissJets
import GradientHessian.SharpSphereTail

/-! The exact memory repair test has an absolute exponentially small
single-point probability under the actual independent sphere law. -/

noncomputable section
namespace GradientHessian.MemoryHitProbability
open MeasureTheory SphereGaussian
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem repair_hit_bound (r : ℝ) (x : E) :
    (sphereLaw E).real {v | 1/8 < |LatchChain.u r v x|} ≤
      2*Real.exp (-(Module.finrank ℝ E : ℝ)/18432) := by
  let y := RadialSquash.squash 8 (r⁻¹ • x)
  have he (v : E) : LatchChain.u r v x = ⟪y,v⟫_ℝ := by
    exact real_inner_comm _ _
  by_cases hy : y=0
  · have hempty : {v : E | 1/8 < |LatchChain.u r v x|} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, he v, hy, inner_zero_left, abs_zero, Set.mem_empty_iff_false]
      norm_num
    rw [hempty, measureReal_empty]
    positivity
  · have htail := SharpSphereTail.sphereLaw_sharp_tail y hy (t := 1/8) (by norm_num)
    have hsub : {v : E | 1/8 < |LatchChain.u r v x|} ⊆ {v | 1/8 ≤ |⟪y,v⟫_ℝ|} := by
      intro v hv
      change 1/8 < |LatchChain.u r v x| at hv
      rw [he v] at hv
      exact hv.le
    have hn : ‖y‖ ≤ 12 := by
      simpa only [show (3:ℝ)*8/2=12 by norm_num] using
        RadialSquash.norm_squash_bound (K := 8) (by norm_num) (r⁻¹ • x)
    have hden : 0<2*‖y‖^2 := by positivity
    have hdenle : 2*‖y‖^2 ≤ 288 := by nlinarith [norm_nonneg y]
    have hq := div_le_div_of_nonneg_left
      (show 0≤(Module.finrank ℝ E:ℝ)*(1/8)^2 by positivity) hden hdenle
    have hexp : -(Module.finrank ℝ E:ℝ)*(1/8)^2/(2*‖y‖^2) ≤
        -(Module.finrank ℝ E:ℝ)/18432 := by
      convert neg_le_neg hq using 1 <;> ring
    exact (measureReal_mono hsub).trans (htail.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)))

theorem manuscript_memory_hit {p : ℕ} (hp : 0<p) (r : ℝ) (x : EuclideanSpace ℝ (Fin p)) :
    (sphereLaw (EuclideanSpace ℝ (Fin p))).real {v | 1/8 < |LatchChain.u r v x|} ≤
      2*Real.exp (-(p:ℝ)/18432) := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  simpa using repair_hit_bound r x

end GradientHessian.MemoryHitProbability
