import GradientHessian.Model
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! Actual first and second jets under a fixed continuous linear coordinate
map and scalar multiplier. The reply transformations are continuous linear
maps, independent of the unknown objective. -/

noncomputable section
namespace GradientHessian.JetPullback

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def first (L : F →L[ℝ] G) : (G →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ F G ℝ).flip L

@[simp] theorem first_apply (L : F →L[ℝ] G) (l : G →L[ℝ] ℝ) : first L l = l.comp L := rfl

def second (L : F →L[ℝ] G) : (G →L[ℝ] G →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ F G (F →L[ℝ] ℝ)).flip L).comp
    (ContinuousLinearMap.compL ℝ G (G →L[ℝ] ℝ) (F →L[ℝ] ℝ) (first L))

@[simp] theorem second_apply (L : F →L[ℝ] G) (B : G →L[ℝ] G →L[ℝ] ℝ) (u v : F) :
    second L B u v = B (L u) (L v) := rfl

theorem first_norm_le (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1) (l : G →L[ℝ] ℝ) :
    ‖first L l‖ ≤ ‖l‖ :=
  (ContinuousLinearMap.opNorm_comp_le l L).trans
    ((mul_le_mul_of_nonneg_left hL (norm_nonneg l)).trans_eq (mul_one _))

theorem second_norm_le (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1) (B : G →L[ℝ] G →L[ℝ] ℝ) :
    ‖second L B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro u
  change ‖first L (B (L u))‖ ≤ _
  apply (first_norm_le L hL _).trans
  exact (B.le_opNorm (L u)).trans (mul_le_mul_of_nonneg_left
    ((L.le_opNorm u).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg u)).trans_eq (one_mul _)))
    (norm_nonneg B))

theorem second_lipschitz (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1) : LipschitzWith 1 (second L) := by
  apply LipschitzWith.of_dist_le_mul
  intro B C
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, map_sub] using second_norm_le L hL (B-C)

theorem fderiv_comp (L : F →L[ℝ] G) {f : G → ℝ} (hf : Differentiable ℝ f) (x : F) :
    fderiv ℝ (fun y => f (L y)) x = first L (fderiv ℝ f (L x)) :=
  ((hf (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv

theorem hessian_comp (L : F →L[ℝ] G) {f : G → ℝ} (hf : ContDiff ℝ 2 f) (x : F) :
    fderiv ℝ (fderiv ℝ (fun y => f (L y))) x = second L (fderiv ℝ (fderiv ℝ f) (L x)) := by
  have he : fderiv ℝ (fun y => f (L y)) = fun y => first L (fderiv ℝ f (L y)) :=
    funext (fderiv_comp L (hf.differentiable (by norm_num)))
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num)
  rw [he]
  have h := ((first L).hasFDerivAt.comp x ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt)).fderiv
  convert h using 1

def scalar (a : ℝ) (L : F →L[ℝ] G) (f : G → ℝ) (x : F) : ℝ := a*f (L x)

def ordinary (a : ℝ) (L : F →L[ℝ] G) (j : ℝ × (G →L[ℝ] ℝ)) : ℝ × (F →L[ℝ] ℝ) :=
  (a*j.1, a • first L j.2)

def rich (a : ℝ) (L : F →L[ℝ] G) (j : ℝ × (G →L[ℝ] ℝ) × (G →L[ℝ] G →L[ℝ] ℝ)) :
    ℝ × (F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ) :=
  (a*j.1, a • first L j.2.1, a • second L j.2.2)

theorem ordinary_continuous (a : ℝ) (L : F →L[ℝ] G) : Continuous (ordinary a L) :=
  (continuous_const.mul continuous_fst).prodMk
    (continuous_const.smul ((first L).continuous.comp continuous_snd))

theorem rich_continuous (a : ℝ) (L : F →L[ℝ] G) : Continuous (rich a L) :=
  (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.smul ((first L).continuous.comp (continuous_fst.comp continuous_snd))).prodMk
      (continuous_const.smul ((second L).continuous.comp (continuous_snd.comp continuous_snd))))

theorem scalar_fderiv (a : ℝ) (L : F →L[ℝ] G) {f : G → ℝ} (hf : Differentiable ℝ f) (x : F) :
    fderiv ℝ (scalar a L f) x = a • first L (fderiv ℝ f (L x)) :=
  (((hf (L x)).hasFDerivAt.comp x L.hasFDerivAt).const_mul a).fderiv

theorem scalar_hessian (a : ℝ) (L : F →L[ℝ] G) {f : G → ℝ} (hf : ContDiff ℝ 2 f) (x : F) :
    fderiv ℝ (fderiv ℝ (scalar a L f)) x = a • second L (fderiv ℝ (fderiv ℝ f) (L x)) := by
  have hdiff : Differentiable ℝ (fun y => f (L y)) := (hf.differentiable (by norm_num)).comp L.differentiable
  have he : fderiv ℝ (scalar a L f) = fun y => a • fderiv ℝ (fun z => f (L z)) y := by
    funext y
    rw [scalar_fderiv a L (hf.differentiable (by norm_num)), fderiv_comp L (hf.differentiable (by norm_num))]
  have hd : Differentiable ℝ (fderiv ℝ (fun y => f (L y))) :=
    ((hf.comp L.contDiff).fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num)
  rw [he, (hd x).hasFDerivAt.const_smul a |>.fderiv, hessian_comp L hf x]

theorem ordinary_exact (a : ℝ) (L : F →L[ℝ] G) {f : G → ℝ} (hf : Differentiable ℝ f) (x : F) :
    JetLocality.ordinaryJet (scalar a L f) x = ordinary a L (JetLocality.ordinaryJet f (L x)) := by
  simp only [JetLocality.ordinaryJet, scalar_fderiv a L hf, ordinary, scalar]

theorem rich_exact (a : ℝ) (L : F →L[ℝ] G) {f : G → ℝ} (hf : ContDiff ℝ 2 f) (x : F) :
    JetLocality.richJet (scalar a L f) x = rich a L (JetLocality.richJet f (L x)) := by
  simp only [JetLocality.richJet, scalar_fderiv a L (hf.differentiable (by norm_num)),
    scalar_hessian a L hf, rich, scalar]

end GradientHessian.JetPullback
