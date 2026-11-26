import GradientHessian.JetPullback
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Dimension padding for the entire C2 admissible class. The padded scalar
is independent of the extra coordinates; no additional analytic assumption
or Hessian-norm bound is introduced. -/

noncomputable section
namespace GradientHessian.EuclideanPadding
open Model Set

variable {N d : ℕ}

def split (h : N ≤ d) : Point d ≃ₗᵢ[ℝ] WithLp 2 (Point N × Point (d-N)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm)).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin N ⊕ Fin (d-N) => ℝ))

def projection (h : N ≤ d) : Point d →L[ℝ] Point N :=
  (ContinuousLinearMap.fst ℝ (Point N) (Point (d-N))).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Point N) (Point (d-N))).toContinuousLinearMap.comp
      (split h).toLinearIsometry.toContinuousLinearMap)

def insertion (h : N ≤ d) : Point N →L[ℝ] Point d :=
  (split h).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Point N) (Point (d-N))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (Point N) (Point (d-N))))

@[simp] theorem projection_insertion (h : N ≤ d) (x : Point N) : projection h (insertion h x) = x := by
  simp [projection, insertion]

theorem insertion_norm (h : N ≤ d) (x : Point N) : ‖insertion h x‖ = ‖x‖ := by
  simp only [insertion, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map]
  exact WithLp.norm_equiv_symm_fst 2 (Point N) (Point (d-N)) x

theorem projection_norm_le (h : N ≤ d) : ‖projection h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hfst := WithLp.norm_fst_le (Point N) (split h x)
  simpa only [LinearIsometryEquiv.norm_map, one_mul] using hfst

theorem projection_lipschitz (h : N ≤ d) : LipschitzWith 1 (projection h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul, ← map_sub]
  exact ((projection h).le_opNorm (x-y)).trans
    ((mul_le_mul_of_nonneg_right (projection_norm_le h) (norm_nonneg _)).trans_eq (one_mul _))

theorem projection_surjective (h : N ≤ d) : Function.Surjective (projection h) :=
  fun x => ⟨insertion h x, projection_insertion h x⟩

theorem covector_norm (h : N ≤ d) (l : First N) : ‖JetPullback.first (projection h) l‖ = ‖l‖ := by
  apply le_antisymm (JetPullback.first_norm_le _ (projection_norm_le h) l)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [JetPullback.first_apply, ContinuousLinearMap.comp_apply, projection_insertion, insertion_norm]
    using (l.comp (projection h)).le_opNorm (insertion h x)

def objective (h : N ≤ d) (f : Point N → ℝ) (x : Point d) : ℝ := f (projection h x)

theorem objective_eq_scalar (h : N ≤ d) (f : Point N → ℝ) :
    objective h f = JetPullback.scalar 1 (projection h) f := by
  funext x
  simp only [objective, JetPullback.scalar, one_mul]

theorem objective_range (h : N ≤ d) (f : Point N → ℝ) : range (objective h f) = range f := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_range_self _
  · rintro ⟨x, rfl⟩
    exact ⟨insertion h x, congrArg f (projection_insertion h x)⟩

@[simp] theorem objective_zero (h : N ≤ d) (f : Point N → ℝ) : objective h f 0 = f 0 := by
  simp only [objective, map_zero]

theorem objective_fderiv (h : N ≤ d) {f : Point N → ℝ} (hf : Differentiable ℝ f) (x : Point d) :
    fderiv ℝ (objective h f) x = JetPullback.first (projection h) (fderiv ℝ f (projection h x)) :=
  JetPullback.fderiv_comp _ hf x

theorem objective_hessian (h : N ≤ d) {f : Point N → ℝ} (hf : ContDiff ℝ 2 f) (x : Point d) :
    fderiv ℝ (fderiv ℝ (objective h f)) x =
      JetPullback.second (projection h) (fderiv ℝ (fderiv ℝ f) (projection h x)) :=
  JetPullback.hessian_comp _ hf x

theorem objective_admissible (h : N ≤ d) {T : ℝ} {f : Point N → ℝ} (hf : Admissible T f) :
    Admissible T (objective h f) := by
  refine ⟨hf.smooth.comp (projection h).contDiff, ?_, ?_, ?_⟩
  · rw [objective_range]
    exact hf.boundedBelow
  · rw [objective_range, objective_zero]
    exact hf.gap
  · have he : fderiv ℝ (fderiv ℝ (objective h f)) =
        JetPullback.second (projection h) ∘ (fderiv ℝ (fderiv ℝ f)) ∘ projection h :=
      funext (objective_hessian h hf.smooth)
    rw [he]
    simpa only [one_mul] using (JetPullback.second_lipschitz (projection h) (projection_norm_le h)).comp
      (hf.hessianLip.comp (projection_lipschitz h))

theorem objective_stationary (h : N ≤ d) {f : Point N → ℝ} (hf : Differentiable ℝ f) :
    stationary (objective h f) = projection h ⁻¹' stationary f := by
  ext x
  simp only [stationary, Set.mem_setOf_eq, Set.mem_preimage, objective_fderiv h hf x, covector_norm]

theorem ordinary_exact (h : N ≤ d) {f : Point N → ℝ} (hf : Differentiable ℝ f) (x : Point d) :
    ordinaryOracle (objective h f) x = JetPullback.ordinary 1 (projection h) (ordinaryOracle f (projection h x)) := by
  rw [objective_eq_scalar]
  exact JetPullback.ordinary_exact 1 (projection h) hf x

theorem rich_exact (h : N ≤ d) {f : Point N → ℝ} (hf : ContDiff ℝ 2 f) (x : Point d) :
    richOracle (objective h f) x = JetPullback.rich 1 (projection h) (richOracle f (projection h x)) := by
  rw [objective_eq_scalar]
  exact JetPullback.rich_exact 1 (projection h) hf x

end GradientHessian.EuclideanPadding
