import Bilevel.ZeroChainResidualBounds
import Bilevel.ScaledZeroChain

/-! Exact amplitude and length scaling of the manuscript's residual certificate. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainResidualScaled
open ZeroChain ZeroChainResidual ZeroChainResidualLocality ZeroChainResidualBounds

def scaled {n : ℕ} (f : Space n → ℝ) (a β : ℝ) (z : Space n) : ℝ := a*f (β⁻¹ • z)
def R (n : ℕ) (a β : ℝ) : Space n → ℝ := scaled (residual n) a β
def A (n : ℕ) (a β : ℝ) : Space n → ℝ := scaled (revealed n) a β
def Rzero (n : ℕ) (a β : ℝ) : Space n → ℝ := scaled (rawResidual n) a β

/-- This is the displayed tail-mask sum in the manuscript, with its exact
coordinate normalization z_j/β. -/
theorem Rzero_formula (n : ℕ) (a β : ℝ) (z : Space n) :
    Rzero n a β z = a*∑ i : Fin (n+1), component n i (β⁻¹ • z)*
      ZeroChainResidualCutoffs.energyCutoff (∑ j : Fin (n+1), if i ≤ j then
        ZeroChainResidualCutoffs.coordinateCutoff (z j/β)^2 else 0) := by
  simp only [Rzero, scaled, rawResidual, maskedComponent, tailMask, tailEnergy,
    PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]

theorem R_eq_centered (n : ℕ) (a β : ℝ) (z : Space n) :
    R n a β z = Rzero n a β z-Rzero n a β 0 := by
  simp [R, Rzero, scaled, ZeroChainResidual.residual, mul_sub]

theorem exact_split (n : ℕ) (a β : ℝ) (z : Space n) :
    A n a β z+R n a β z = ScaledZeroChain.value n a β z := by
  dsimp [A, R, scaled, ScaledZeroChain.value]
  rw [← mul_add, ZeroChainResidual.exact_split]

@[simp] theorem R_zero (n : ℕ) (a β : ℝ) : R n a β 0 = 0 := by simp [R, scaled]

theorem scaled_contDiff {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f) (a β : ℝ) :
    ContDiff ℝ 3 (scaled f a β) :=
  contDiff_const.mul (hf.comp (contDiff_id.const_smul β⁻¹))

theorem R_contDiff (n : ℕ) (a β : ℝ) : ContDiff ℝ 3 (R n a β) :=
  scaled_contDiff (residual_contDiff n) a β

theorem A_contDiff (n : ℕ) (a β : ℝ) : ContDiff ℝ 3 (A n a β) :=
  scaled_contDiff (revealed_contDiff n) a β

theorem scaled_gradient {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f) (a β : ℝ) (z : Space n) :
    gradient (scaled f a β) z = (a/β) • gradient f (β⁻¹ • z) := by
  have h := (hf (β⁻¹ • z)).hasGradientAt
  have hd := (h.hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul β⁻¹)).const_mul a
  have hg : HasGradientAt (scaled f a β) ((a/β) • gradient f (β⁻¹ • z)) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hd using 1
    ext v
    simp [InnerProductSpace.toDual_apply, div_eq_mul_inv]
    ring
  exact hg.gradient

theorem scaled_jet_bound {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (a β B : ℝ) (ha : 0 ≤ a) (hβ : 0 < β) (k : ℕ) (hk : k ≤ 3)
    (hb : ∀ z, ‖iteratedFDeriv ℝ k f z‖ ≤ B) (z : Space n) :
    ‖iteratedFDeriv ℝ k (scaled f a β) z‖ ≤ B*a/β^k := by
  let g : Space n →L[ℝ] Space n := β⁻¹ • ContinuousLinearMap.id ℝ (Space n)
  have hg : ‖g‖ ≤ β⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound g (inv_nonneg.mpr hβ.le)
    intro v
    change ‖β⁻¹ • v‖ ≤ β⁻¹*‖v‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  change ‖iteratedFDeriv ℝ k (fun w => a • (f ∘ g) w) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hf.comp g.contDiff).of_le hk').contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, g.iteratedFDeriv_comp_right hf z hk']
  have hc := ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ k f (g z)) (fun _ => g)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  have hc' := hc.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hg k)
    (norm_nonneg (iteratedFDeriv ℝ k f (g z))))
  calc
    _ ≤ a*(‖iteratedFDeriv ℝ k f (g z)‖*(β⁻¹)^k) := mul_le_mul_of_nonneg_left hc' ha
    _ ≤ a*(B*(β⁻¹)^k) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hb _) (by positivity)) ha
    _ = B*a/β^k := by rw [inv_pow, div_eq_mul_inv]; ring

theorem R_uniform_jet_bound : ∃ B : Fin 4 → ℝ, (∀ j, 0 ≤ B j) ∧
    ∀ (j : Fin 4) (n : ℕ) (a β : ℝ), 0 ≤ a → 0 < β → ∀ z : Space n,
      ‖iteratedFDeriv ℝ j.val (R n a β) z‖ ≤ B j*a/β^j.val := by
  obtain ⟨B,hB,hb⟩ := residual_uniform_jet_bound
  refine ⟨B,hB,fun j n a β ha hβ z => ?_⟩
  exact scaled_jet_bound (residual_contDiff n) a β (B j) ha hβ j.val (by omega) (hb j n) z

theorem scaled_coordinate_small {n : ℕ} (β : ℝ) (hβ : 0 < β) (z : Space n)
    (j : Fin (n+1)) (hj : |z j| ≤ β/4) : |(β⁻¹ • z) j| ≤ 1/4 := by
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hβ)]
  apply (inv_mul_le_iff₀ hβ).mpr
  linarith

theorem A_gradient_support (n r : ℕ) (a β : ℝ) (hβ : 0 < β) (z : Space n)
    (hz : ∀ j : Fin (n+1), r ≤ j.val → |z j| ≤ β/4)
    (j : Fin (n+1)) (hj : r ≤ j.val) : gradient (A n a β) z j = 0 := by
  rw [A, scaled_gradient ((revealed_contDiff n).differentiable (by norm_num)), PiLp.smul_apply,
    revealed_gradient_support r (β⁻¹ • z) (fun k hk => scaled_coordinate_small β hβ z k (hz k hk)) j hj,
    smul_zero]

theorem R_gradient_support (n r : ℕ) (a β : ℝ) (hβ : 0 < β) (z : Space n)
    (hz : ∀ j : Fin (n+1), r ≤ j.val → |z j| ≤ β/4)
    (j : Fin (n+1)) (hj : r+1 ≤ j.val) : gradient (R n a β) z j = 0 := by
  rw [R, scaled_gradient ((residual_contDiff n).differentiable (by norm_num)), PiLp.smul_apply,
    residual_gradient_support r (β⁻¹ • z) (fun k hk => scaled_coordinate_small β hβ z k (hz k hk)) j hj,
    smul_zero]

theorem A_gradient_zero (n : ℕ) (a β : ℝ) : gradient (A n a β) 0 = 0 := by
  rw [A, scaled_gradient ((revealed_contDiff n).differentiable (by norm_num)), smul_zero,
    revealed_gradient_zero, smul_zero]

/-- The derivative scaling in the original residual certificate, with the
paper's amplitude a=η L β² and a numerical 0≤η≤1. -/
theorem source_residual_jet_bounds : ∃ B : Fin 4 → ℝ, (∀ j, 0 ≤ B j) ∧
    ∀ (j : Fin 4) (n : ℕ) (η L β : ℝ), 0 ≤ η → η ≤ 1 → 0 ≤ L → 0 < β → ∀ z : Space n,
      ‖iteratedFDeriv ℝ j.val (R n (η*L*β^2) β) z‖ ≤ B j*L*β^(2-(j.val:ℤ)) := by
  obtain ⟨B,hB,hb⟩ := R_uniform_jet_bound
  refine ⟨B,hB,fun j n η L β hη hη1 hL hβ z => ?_⟩
  have ha : 0 ≤ η*L*β^2 := by positivity
  have hs := hb j n (η*L*β^2) β ha hβ z
  have hp : β^(2-(j.val:ℤ)) = β^2/β^j.val := by
    rw [zpow_sub₀ hβ.ne']
    norm_cast
  rw [hp]
  apply hs.trans
  have hBj := hB j
  have hm := mul_le_mul_of_nonneg_left hη1
    (show 0 ≤ B j*L*β^2/β^j.val by positivity)
  convert hm using 1 <;> ring

end Bilevel.ZeroChainResidualScaled
