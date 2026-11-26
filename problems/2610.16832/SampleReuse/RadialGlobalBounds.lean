import SampleReuse.RadialWallBounds
import SampleReuse.RadialExterior

open SecondOrder
open scoped Topology BigOperators

namespace SampleReuse
noncomputable section

def cutoffJetBound (R : ℝ) (k : ℕ) : ℝ :=
  if k=0 then 1 else (R⁻¹)^k*cutoffRadialConstant k

theorem cutoffJetBound_nonneg {R : ℝ} (hR : 0 < R) (k : ℕ) :
    0 ≤ cutoffJetBound R k := by
  unfold cutoffJetBound
  split_ifs
  · norm_num
  · exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) _) (cutoffRadialConstant_pos k).le

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radialCutoffLoss_jet_bound {R : ℝ} (hR : 0 < R)
    (k : ℕ) (hk : k ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ k (radialCutoffLoss R : E → ℝ) x‖ ≤ cutoffJetBound R k := by
  by_cases hk0 : k=0
  · subst k
    rw [norm_iteratedFDeriv_zero]
    have hh := radialCutoff_mem (‖x‖/R)
    simpa only [radialCutoffLoss, Real.norm_of_nonneg hh.1, cutoffJetBound, if_pos rfl] using hh.2
  · simpa only [cutoffJetBound, if_neg hk0] using radialCutoffLoss_derivative_bound hR k hk x

theorem radialGlobalization_iterated_product_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (b : ℝ) {R : ℝ} (hR : 0 < R) (B : ℕ → ℝ) (k : ℕ) (hk : k ≤ 3)
    (x : E) (_hB : ∀ j, j ≤ 3 → 0 ≤ B j)
    (hb : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    ‖iteratedFDeriv ℝ k (radialGlobalization f b R) x‖ ≤
      (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*cutoffJetBound R i*B (k-i)) +
        ‖iteratedFDeriv ℝ k (radialWallLoss b R : E → ℝ) x‖ := by
  have hkc : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hg : ContDiff ℝ 3 (radialCutoffLoss R : E → ℝ) := radialCutoffLoss_contDiff hR 3
  have hw : ContDiff ℝ k (radialWallLoss b R : E → ℝ) := radialWallLoss_contDiff b hR k
  unfold radialGlobalization
  rw [iteratedFDeriv_add_apply' (((hg.mul hf).of_le hkc).contDiffAt) hw.contDiffAt]
  apply (norm_add_le _ _).trans
  apply add_le_add_right
  apply (norm_iteratedFDeriv_mul_le hg hf x hkc).trans
  apply Finset.sum_le_sum
  intro i hi
  have hi3 : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
  have hki : k-i ≤ 3 := by omega
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (radialCutoffLoss_jet_bound hR i hi3 x) (Nat.cast_nonneg _))
    (hb (k-i) hki) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (cutoffJetBound_nonneg hR i))

theorem radialGlobalization_higher_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {b R : ℝ} (hbp : 0 ≤ b) (hR : 0 < R) (B : ℕ → ℝ)
    (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (x : E)
    (hB : ∀ j, j ≤ 3 → 0 ≤ B j)
    (hb : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    ‖iteratedFDeriv ℝ k (radialGlobalization f b R) x‖ ≤
      (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*cutoffJetBound R i*B (k-i)) +
        b*R*(R⁻¹)^k*wallRadialConstant k :=
  (radialGlobalization_iterated_product_bound hf b hR B k hk3 x hB hb).trans
    (add_le_add_left (radialWallLoss_derivative_bound hbp hR k hk1 hk3 x) _)

theorem radialGlobalization_second_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {b R : ℝ} (hbp : 0 ≤ b) (hR : 0 < R) (B : ℕ → ℝ) (x : E)
    (hB : ∀ j, j ≤ 3 → 0 ≤ B j)
    (hb : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    ‖iteratedFDeriv ℝ 2 (radialGlobalization f b R) x‖ ≤
      B 2+2*(R⁻¹*cutoffRadialConstant 1)*B 1+(R⁻¹)^2*cutoffRadialConstant 2*B 0+
        b*R*(R⁻¹)^2*wallRadialConstant 2 := by
  have hh := radialGlobalization_higher_bound hf hbp hR B 2 (by decide) (by decide) x hB hb
  simpa [Finset.sum_range_succ, Nat.choose, cutoffJetBound] using hh

theorem radialGlobalization_third_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {b R : ℝ} (hbp : 0 ≤ b) (hR : 0 < R) (B : ℕ → ℝ) (x : E)
    (hB : ∀ j, j ≤ 3 → 0 ≤ B j)
    (hb : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    ‖iteratedFDeriv ℝ 3 (radialGlobalization f b R) x‖ ≤
      B 3+3*(R⁻¹*cutoffRadialConstant 1)*B 2+
        3*((R⁻¹)^2*cutoffRadialConstant 2)*B 1+(R⁻¹)^3*cutoffRadialConstant 3*B 0+
        b*R*(R⁻¹)^3*wallRadialConstant 3 := by
  have hh := radialGlobalization_higher_bound hf hbp hR B 3 (by decide) le_rfl x hB hb
  simpa [Finset.sum_range_succ, Nat.choose, cutoffJetBound] using hh

variable [CompleteSpace E]

theorem radialWallLoss_gradient_bound {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (x : E) :
    ‖gradient (radialWallLoss b R) x‖ ≤ b := by
  by_cases hx : x=0
  · subst x
    have he : (radialWallLoss b R : E → ℝ) =ᶠ[𝓝 0] (fun _ => 0) := by
      have hy : ∀ᶠ y : E in 𝓝 0, ‖y‖ < R/2 :=
        continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using (half_pos hR)))
      exact hy.mono (fun _ hy => radialWall_zero b hR hy.le)
    simp only [gradient, he.fderiv_eq, fderiv_const, Pi.zero_apply, map_zero, norm_zero]
    exact hb
  · rw [radialWallLoss_gradient b hR hx, norm_smul]
    have hS := radialRise_mem (‖x‖/R)
    rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg hb hS.1) (norm_nonneg x)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]
    exact mul_le_of_le_one_right hb hS.2

theorem radialGlobalization_gradient_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {b R : ℝ} (hbp : 0 ≤ b) (hR : 0 < R) (B : ℕ → ℝ) (x : E)
    (hB : ∀ j, j ≤ 3 → 0 ≤ B j)
    (hb : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    ‖gradient (radialGlobalization f b R) x‖ ≤ B 1+R⁻¹*cutoffRadialConstant 1*B 0+b := by
  have hh := radialGlobalization_iterated_product_bound hf b hR B 1 (by decide) x hB hb
  have hw : ‖iteratedFDeriv ℝ 1 (radialWallLoss b R : E → ℝ) x‖ ≤ b := by
    rw [norm_first_iteratedFDeriv, ← norm_gradient_eq_fderiv]
    exact radialWallLoss_gradient_bound hbp hR x
  rw [norm_gradient_eq_fderiv, ← norm_first_iteratedFDeriv]
  apply hh.trans
  simpa [Finset.sum_range_succ, Nat.choose, cutoffJetBound] using
    add_le_add_left hw (B 1+R⁻¹*cutoffRadialConstant 1*B 0)

end
end SampleReuse
