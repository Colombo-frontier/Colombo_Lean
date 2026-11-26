import FreshGradientMinimax.CoreScalarLipschitz
import FreshGradientMinimax.SparsePairNorm

/-! Scalar and vector difference bounds for the actual square links. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem two_variable_sub_le {f : ℝ → ℝ → ℝ} {A B : ℝ}
    (h1 : ∀ a b c, |f a b - f c b| ≤ A * |a - c|)
    (h2 : ∀ a b d, |f a b - f a d| ≤ B * |b - d|) (a b c d : ℝ) :
    |f a b - f c d| ≤ A * |a - c| + B * |b - d| := by
  calc
    _ = |(f a b - f c b) + (f c b - f c d)| := by congr 1; ring
    _ ≤ |f a b - f c b| + |f c b - f c d| := abs_add_le _ _
    _ ≤ _ := add_le_add (h1 a b c) (h2 c b d)

theorem rootLink_sub_le {s : ℝ} (hs : |s| = 1) (a b c d : ℝ) :
    |rootLink s a b - rootLink s c d| ≤ 20 * |a - c| + 20 * |b - d| := by
  apply two_variable_sub_le
  · intro a b c
    exact scalar_sub_le_of_derivative_bound (fun x => rootLink_hasDerivAt_first s x b)
      (fun x => (rootLink_component_bounds hs x b).2.1) a c
  · intro a b d
    exact scalar_sub_le_of_derivative_bound (rootLink_hasDerivAt_second s a)
      (fun x => (rootLink_component_bounds hs a x).2.2.1) b d

theorem rootLinkD1_sub_le {s : ℝ} (hs : |s| = 1) (a b c d : ℝ) :
    |rootLinkD1 s a b - rootLinkD1 s c d| ≤ 1000 * |a - c| + 1000 * |b - d| := by
  apply two_variable_sub_le
  · intro a b c
    exact scalar_sub_le_of_derivative_bound (fun x => rootLinkD1_hasDerivAt_first s x b)
      (fun x => (rootLink_component_bounds hs x b).2.2.2.1) a c
  · intro a b d
    exact scalar_sub_le_of_derivative_bound (rootLinkD1_hasDerivAt_second s a)
      (fun x => (rootLink_component_bounds hs a x).2.2.2.2.1) b d

theorem rootLinkD2_sub_le {s : ℝ} (hs : |s| = 1) (a b c d : ℝ) :
    |rootLinkD2 s a b - rootLinkD2 s c d| ≤ 1000 * |a - c| + 1000 * |b - d| := by
  apply two_variable_sub_le
  · intro a b c
    exact scalar_sub_le_of_derivative_bound (fun x => rootLinkD2_hasDerivAt_first s x b)
      (fun x => (rootLink_component_bounds hs x b).2.2.2.2.1) a c
  · intro a b d
    exact scalar_sub_le_of_derivative_bound (rootLinkD2_hasDerivAt_second s a)
      (fun x => (rootLink_component_bounds hs a x).2.2.2.2.2) b d

theorem rootLink_adjacent_sub_norm {n : ℕ} {s : ℝ} (hs : |s| = 1) (u v : Euclid (n + 1)) :
    ‖adjacentVector (rootLink s) u - adjacentVector (rootLink s) v‖ ≤ 40 * ‖u - v‖ :=
  adjacentVector_sub_norm_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rootLink_sub_le hs) u v

theorem rootLinkD1_adjacent_sub_norm {n : ℕ} {s : ℝ} (hs : |s| = 1) (u v : Euclid (n + 1)) :
    ‖adjacentVector (rootLinkD1 s) u - adjacentVector (rootLinkD1 s) v‖ ≤ 2000 * ‖u - v‖ :=
  adjacentVector_sub_norm_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rootLinkD1_sub_le hs) u v

theorem rootLinkD2_adjacent_sub_norm {n : ℕ} {s : ℝ} (hs : |s| = 1) (u v : Euclid (n + 1)) :
    ‖adjacentVector (rootLinkD2 s) u - adjacentVector (rootLinkD2 s) v‖ ≤ 2000 * ‖u - v‖ :=
  adjacentVector_sub_norm_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rootLinkD2_sub_le hs) u v

theorem rootLink_linear_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℝ) (A B : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun y => rootLink s (A y) (B y))
      (rootLinkD1 s (A x) (B x) • A + rootLinkD2 s (A x) (B x) • B) x := by
  have hp := (coreGateRoot_hasDerivAt (s * A x)).comp_hasFDerivAt x (A.hasFDerivAt.const_mul s)
  have hb := (coreThetaRoot_hasDerivAt (-B x)).comp_hasFDerivAt x B.hasFDerivAt.neg
  apply (hp.mul hb).congr_fderiv
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, smul_eq_mul, Function.comp_def, rootLinkD1, rootLinkD2]
  ring

end FreshGradientMinimax
