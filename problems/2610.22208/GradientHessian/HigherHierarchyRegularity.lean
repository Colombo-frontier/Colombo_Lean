import GradientHessian.HigherHierarchyRegularityInduction
import GradientHessian.HigherHierarchyBaselineDerivatives
import GradientHessian.Normalization

/-! The literal source uniform-regularity theorem and its normalization.
All constants are independent of task count, height, and register dimensions;
K is the one fixed absolute radius multiplier of the construction. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u

def regularityConstant (K : ℝ) : ℝ :=
  4*firstConstant K + 18*secondConstant K + 9*thirdConstant K + 769

theorem regularityConstant_pos {K : ℝ} (hK : 0 ≤ K) : 0 < regularityConstant K := by
  have h1 := firstConstant_pos hK
  have h2 := secondConstant_pos hK
  have h3 := thirdConstant_pos hK
  unfold regularityConstant
  positivity

theorem regularityConstant_bounds {K : ℝ} (hK : 0 ≤ K) :
    4*firstConstant K ≤ regularityConstant K ∧ 18*secondConstant K ≤ regularityConstant K ∧
      768+9*thirdConstant K ≤ regularityConstant K := by
  have h1 := firstConstant_pos hK
  have h2 := secondConstant_pos hK
  have h3 := thirdConstant_pos hK
  unfold regularityConstant
  constructor
  · linarith
  constructor <;> linarith

def hessianConstant (K : ℝ) : NNReal := ⟨max 0 (regularityConstant K), le_max_left _ _⟩

theorem hessianConstant_coe {K : ℝ} (hK : 0 ≤ K) :
    (hessianConstant K : ℝ) = regularityConstant K := max_eq_right (regularityConstant_pos hK).le

def normalizationScale (K : ℝ) : ℝ := max 1 (Real.sqrt (regularityConstant K))

theorem normalizationScale_pos (K : ℝ) : 0 < normalizationScale K :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem normalizationScale_square {K : ℝ} (hK : 0 ≤ K) : regularityConstant K ≤ normalizationScale K^2 := by
  rw [← Real.sq_sqrt (regularityConstant_pos hK).le]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)] [∀ t, CompleteSpace (H t)]

theorem scalar_third_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (Z : Space Y E H m t) :
    ‖iteratedFDeriv ℝ 3 (scalar K t d) Z‖ ≤ regularityConstant K := by
  have hK0 : 0 < K := by linarith
  rw [show scalar K t d = fun W => baseline K t W + residual K t d W from
    funext (scalar_eq_baseline_add_residual K t d)]
  exact (Inner.norm_iteratedFDeriv_add_le (baseline_contDiff hK0 t)
    (residual_contDiff hK0 t d) (n := 3) le_rfl Z).trans
    ((add_le_add (baseline_third_bound (by linarith : 1 ≤ K) t Z)
      (residual_third_bound hK t d hd Z)).trans (regularityConstant_bounds hK0.le).2.2)

theorem scalar_hessian_lipschitz {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) :
    LipschitzWith (hessianConstant K) (fderiv ℝ (fderiv ℝ (scalar K t d))) := by
  apply Normalization.hessian_lipschitz_of_third_bound (scalar_contDiff (by linarith) t d)
  intro Z
  rw [hessianConstant_coe (by linarith : 0 ≤ K)]
  exact scalar_third_bound hK t d hd Z

theorem residual_gradient_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (Z : Space Y E H m t) :
    ‖gradient (residual K t d) Z‖ ≤ regularityConstant K*((m+1:ℝ)^2+(8/3)^(t+1)) := by
  rw [show ‖gradient (residual K t d) Z‖ = ‖fderiv ℝ (residual K t d) Z‖ from
    (InnerProductSpace.toDual ℝ (Space Y E H m t)).symm.norm_map _,
    ← LocalizedNormDerivatives.norm_first_derivative]
  have h := residual_first_bound hK t d hd Z
  have hc := (regularityConstant_bounds (by linarith : 0 ≤ K)).1
  have hp : (8/3:ℝ)^t ≤ (8/3)^(t+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact h.trans (mul_le_mul hc (add_le_add_left hp _) (by positivity)
    (regularityConstant_pos (by linarith)).le)

structure RegularityBounds (K : ℝ) (t : ℕ) (d : Data Y E H m t) : Prop where
  smooth : ContDiff ℝ 3 (scalar K t d)
  first : ∀ Z, ‖iteratedFDeriv ℝ 1 (residual K t d) Z‖ ≤
    regularityConstant K*((m+1:ℝ)^2+(8/3)^(t+1))
  second : ∀ Z, ‖iteratedFDeriv ℝ 2 (residual K t d) Z‖ ≤ regularityConstant K*(m+1)
  third : ∀ Z, ‖iteratedFDeriv ℝ 3 (residual K t d) Z‖ ≤ regularityConstant K
  full_third : ∀ Z, ‖iteratedFDeriv ℝ 3 (scalar K t d) Z‖ ≤ regularityConstant K
  hessian_lipschitz : LipschitzWith (hessianConstant K) (fderiv ℝ (fderiv ℝ (scalar K t d)))

/-- Manuscript `thm:regularity-log`, with source height q=t+1. -/
theorem source_regularity {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) : RegularityBounds K t d := by
  have hK0 : 0 ≤ K := by linarith
  refine ⟨scalar_contDiff (by linarith) t d, ?_, ?_, ?_, scalar_third_bound hK t d hd,
    scalar_hessian_lipschitz hK t d hd⟩
  · intro Z
    have h := residual_gradient_bound hK t d hd Z
    simpa only [gradient, LinearIsometryEquiv.norm_map, LocalizedNormDerivatives.norm_first_derivative] using h
  · intro Z
    exact (residual_second_bound hK t d hd Z).trans
      (mul_le_mul_of_nonneg_right (regularityConstant_bounds hK0).2.1 (by positivity))
  · intro Z
    exact (residual_third_bound hK t d hd Z).trans
      (by linarith [(regularityConstant_bounds hK0).2.2])

def normalizedScalar (K : ℝ) (t : ℕ) (d : Data Y E H m t) : Space Y E H m t → ℝ :=
  Normalization.rescale (normalizationScale K) (scalar K t d)

omit [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)] in
theorem normalizedScalar_contDiff {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t) :
    ContDiff ℝ 3 (normalizedScalar K t d) :=
  Normalization.rescale_contDiff _ (scalar_contDiff (by linarith) t d)

theorem normalizedScalar_third_le_one {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (Z : Space Y E H m t) :
    ‖iteratedFDeriv ℝ 3 (normalizedScalar K t d) Z‖ ≤ 1 :=
  Normalization.rescale_third_le_one (normalizationScale_pos K)
    (normalizationScale_square (by linarith)) (scalar_contDiff (by linarith) t d)
    (scalar_third_bound hK t d hd) Z

theorem normalizedScalar_hessian_lipschitz {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) :
    LipschitzWith 1 (fderiv ℝ (fderiv ℝ (normalizedScalar K t d))) :=
  Normalization.hessian_lipschitz_of_third_bound (normalizedScalar_contDiff hK t d) 1
    (normalizedScalar_third_le_one hK t d hd)

omit [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)] in
theorem normalizedScalar_fderiv {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (Z : Space Y E H m t) :
    fderiv ℝ (normalizedScalar K t d) Z =
      fderiv ℝ (scalar K t d) ((normalizationScale K)⁻¹ • Z) :=
  Normalization.rescale_fderiv (normalizationScale_pos K).ne'
    ((scalar_contDiff (by linarith) t d).differentiable (by norm_num)) Z

theorem normalizedScalar_gradient {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (Z : Space Y E H m t) :
    gradient (normalizedScalar K t d) Z = gradient (scalar K t d) ((normalizationScale K)⁻¹ • Z) := by
  simp only [gradient, normalizedScalar_fderiv hK t d Z]

omit [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)] in
theorem normalizedScalar_ordinaryJet {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (Z : Space Y E H m t) :
    JetLocality.ordinaryJet (normalizedScalar K t d) Z =
      (normalizationScale K*(JetLocality.ordinaryJet (scalar K t d) ((normalizationScale K)⁻¹ • Z)).1,
        (JetLocality.ordinaryJet (scalar K t d) ((normalizationScale K)⁻¹ • Z)).2) :=
  Normalization.rescale_ordinaryJet (normalizationScale_pos K).ne'
    ((scalar_contDiff (by linarith) t d).differentiable (by norm_num)) Z

omit [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)] in
theorem normalizedScalar_richJet {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (Z : Space Y E H m t) :
    JetLocality.richJet (normalizedScalar K t d) Z =
      (normalizationScale K*(JetLocality.richJet (scalar K t d) ((normalizationScale K)⁻¹ • Z)).1,
        (JetLocality.richJet (scalar K t d) ((normalizationScale K)⁻¹ • Z)).2.1,
        (normalizationScale K)⁻¹ • (JetLocality.richJet (scalar K t d) ((normalizationScale K)⁻¹ • Z)).2.2) :=
  Normalization.rescale_richJet (normalizationScale_pos K).ne'
    ((scalar_contDiff (by linarith) t d).of_le (by decide : (2:WithTop ℕ∞) ≤ 3)) Z

end GradientHessian.HigherHierarchy
