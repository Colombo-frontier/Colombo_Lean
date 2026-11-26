import Bilevel.PolishedLiteralFlattenMap
import Bilevel.ZeroChainFlatteningBounds

/-! Generic composition estimate applied to the manuscript's genuine C-infinity flattening. -/
noncomputable section
namespace Bilevel.PolishedLiteralFlatteningTools
open ChiBoundedChain PolishedLiteralFlattenCutoff PolishedLiteralFlattenMap
theorem linear_scale_jet_le {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (s : ℝ) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun w => f (s • w)) z‖ ≤
      ‖iteratedFDeriv ℝ k f (s • z)‖*|s|^k := by
  let g : Space n →L[ℝ] Space n := s • ContinuousLinearMap.id ℝ (Space n)
  have hg : ‖g‖ ≤ |s| := by
    apply ContinuousLinearMap.opNorm_le_bound g (abs_nonneg _)
    intro v
    change ‖s • v‖ ≤ |s| * ‖v‖
    simp only [norm_smul, Real.norm_eq_abs, le_refl]
  change ‖iteratedFDeriv ℝ k (f ∘ g) z‖ ≤ _
  rw [g.iteratedFDeriv_comp_right hf z (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg _) (norm_nonneg _)

theorem jet_sub_const {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (c : ℝ) (z : Space n) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (fun w => f w-c) z = iteratedFDeriv ℝ k f z := by
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' (hf.of_le hk').contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne (show k ≠ 0 by omega), Pi.zero_apply, add_zero]

/-- Subtracting a constant at the evaluation point before applying the
composition estimate retains the required δ^(1-k) dependence. -/
theorem flatten_positive_jet_bound {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (K M δ : ℝ) (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcore : ∀ (j : ℕ), 1 ≤ j → j ≤ 3 → ∀ w : Space n, ‖iteratedFDeriv ℝ j (coreMap n) w‖ ≤ K)
    (houter : ∀ (j : ℕ), 1 ≤ j → j ≤ 3 → ∀ w : Space n,
      ‖iteratedFDeriv ℝ j f w‖ ≤ M*δ/δ^j)
    (z : Space n) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun w => f (flattenMap n δ w)) z‖ ≤
      (k.factorial:ℝ)*M*K^k*δ/δ^k := by
  let x : Space n := δ⁻¹ • z
  let c := f (δ • coreMap n x)
  let g : Space n → ℝ := fun w => f (δ • w)-c
  have hfd : ContDiff ℝ 3 (fun w : Space n => f (δ • w)) := hf.comp (contDiff_id.const_smul δ)
  have hg : ContDiff ℝ 3 g := hfd.sub contDiff_const
  have ho (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j g (coreMap n x)‖ ≤ M*δ := by
    by_cases hj0 : j = 0
    · subst j
      simp only [norm_iteratedFDeriv_zero, g, c, sub_self, norm_zero]
      exact mul_nonneg hM hδ.le
    · rw [jet_sub_const hfd c _ j (by omega) (by omega)]
      have hs := linear_scale_jet_le hf δ (coreMap n x) j (by omega)
      rw [abs_of_pos hδ] at hs
      calc
        _ ≤ ‖iteratedFDeriv ℝ j f (δ • coreMap n x)‖*δ^j := hs
        _ ≤ (M*δ/δ^j)*δ^j := mul_le_mul_of_nonneg_right
          (houter j (by omega) (by omega) _) (pow_nonneg hδ.le _)
        _ = M*δ := by field_simp
  have hi (j : ℕ) (hj0 : 1 ≤ j) (hjk : j ≤ k) :
      ‖iteratedFDeriv ℝ j (coreMap n) x‖ ≤ K^j :=
    (hcore j hj0 (by omega) x).trans (by simpa only [pow_one] using pow_le_pow_right₀ hK hj0)
  have hcomp := norm_iteratedFDeriv_comp_le hg (coreMap_contDiff n)
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk) x ho hi
  have hs := linear_scale_jet_le (hg.comp (coreMap_contDiff n)) δ⁻¹ z k hk
  have he : (fun w : Space n => (g ∘ coreMap n) (δ⁻¹ • w)) =
      fun w => f (flattenMap n δ w)-c := by
    ext w
    rw [flattenMap_eq_scaled_coreMap n δ hδ.ne']
    rfl
  have hfc : ContDiff ℝ 3 (fun w => f (flattenMap n δ w)) := hf.comp (flattenMap_contDiff n δ)
  rw [he, jet_sub_const hfc c z k hk0 hk,
    abs_of_pos (inv_pos.mpr hδ)] at hs
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (g ∘ coreMap n) x‖*(δ⁻¹)^k := hs
    _ ≤ ((k.factorial:ℝ)*(M*δ)*K^k)*(δ⁻¹)^k :=
      mul_le_mul_of_nonneg_right hcomp (pow_nonneg (inv_nonneg.mpr hδ.le) _)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring


end Bilevel.PolishedLiteralFlatteningTools
