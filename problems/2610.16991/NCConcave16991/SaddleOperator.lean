import NCConcave16991.SaddleSupport

/-! # The actual biased proximal saddle operator of Appendix B.2 -/

open Set InnerProductSpace
open scoped InnerProductSpace

namespace NCConcave16991

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

def dualInclusion (dx dy : ℕ) : DualSpace dy →L[ℝ] JointSpace dx dy :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (PrimalSpace dx) (DualSpace dy)).symm :
    (PrimalSpace dx × DualSpace dy) →L[ℝ] JointSpace dx dy).comp
      (ContinuousLinearMap.inr ℝ (PrimalSpace dx) (DualSpace dy))

theorem jointPoint_dual_hasFDerivAt (x : PrimalSpace dx) (y : DualSpace dy) :
    HasFDerivAt (fun v => jointPoint x v) (dualInclusion dx dy) y := by
  convert (dualInclusion dx dy).hasFDerivAt.add_const (jointPoint x 0) using 1
  ext v
  change WithLp.toLp 2 (x, v) = WithLp.toLp 2 (0, v) + WithLp.toLp 2 (x, 0)
  simp [← WithLp.toLp_add]

theorem Problem.hasGradientAt_dual_section (P : Problem p dx dy K)
    (x : PrimalSpace dx) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    HasGradientAt (fun v => componentAverage P.component (jointPoint x v))
      (averageMap P.componentGradient (jointPoint x y)).snd y := by
  have hj := P.hasGradientAt_average (jointPoint x y) hy
  have hc := hj.hasFDerivAt.comp y (jointPoint_dual_hasFDerivAt x y)
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlin : toDual ℝ (DualSpace dy)
      (averageMap P.componentGradient (jointPoint x y)).snd =
      (toDual ℝ (JointSpace dx dy) (averageMap P.componentGradient (jointPoint x y))).comp
        (dualInclusion dx dy) := by
    ext v
    change ⟪(averageMap P.componentGradient (jointPoint x y)).snd, v⟫_ℝ =
      ⟪averageMap P.componentGradient (jointPoint x y), dualInclusion dx dy v⟫_ℝ
    simp [dualInclusion, WithLp.prod_inner_apply]
  rw [hlin]
  exact hc

def saddleObjective (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (c x : PrimalSpace dx) (y : DualSpace dy) : ℝ :=
  dualRegularizedSection P μ y0 x y + p.L * ‖x - c‖ ^ 2

def saddlePrimalGradient (P : Problem p dx dy K) (c : PrimalSpace dx)
    (z : JointSpace dx dy) : PrimalSpace dx :=
  (averageMap P.componentGradient z).fst + (2 * p.L) • (z.fst - c)

def saddleDualGradient (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (z : JointSpace dx dy) : DualSpace dy :=
  (averageMap P.componentGradient z).snd - μ • (z.snd - y0)

/-- The signed gradient `(∇x Q_c, -∇y Q_c)` of the actual saddle objective. -/
def saddleOperator (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (c : PrimalSpace dx) (z : JointSpace dx dy) : JointSpace dx dy :=
  jointPoint (saddlePrimalGradient P c z) (-saddleDualGradient P μ y0 z)

theorem saddle_primal_hasGradientAt (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (c x : PrimalSpace dx) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    HasGradientAt (fun u => saddleObjective P μ y0 c u y)
      (saddlePrimalGradient P c (jointPoint x y)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (dualRegularizedSection_hasGradientAt P μ y0 y hy x).hasFDerivAt.add
    (scaled_sqDistance_hasGradientAt p.L c x).hasFDerivAt
  convert hd using 1 <;> first
    | rfl
    | simp [saddleObjective, saddlePrimalGradient, jointPoint, map_add]

theorem saddle_dual_hasGradientAt (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (c x : PrimalSpace dx) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    HasGradientAt (saddleObjective P μ y0 c x)
      (saddleDualGradient P μ y0 (jointPoint x y)) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hq := scaled_sqDistance_hasGradientAt (μ / 2) y0 y
  have hd := ((P.hasGradientAt_dual_section x y hy).hasFDerivAt.sub hq.hasFDerivAt).add_const
    (p.L * ‖x - c‖ ^ 2)
  convert hd using 1 <;> first
    | rfl
    | (simp [saddleObjective, dualRegularizedSection, saddleDualGradient, jointPoint, map_sub]
       <;> congr 1 <;> ring)

theorem saddle_primal_stronglyConvex (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (μ : ℝ) (y0 : DualSpace dy) (c : PrimalSpace dx) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    StrongConvexOn univ p.L (fun x => saddleObjective P μ y0 c x y) :=
  weaklyConvex_prox_strong (dualRegularizedSection_weaklyConvex P hAS μ y0 y hy) c

theorem saddle_dual_stronglyConcave (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (c x : PrimalSpace dx) :
    StrongConcaveOn K.carrier μ (saddleObjective P μ y0 c x) := by
  rw [strongConcaveOn_iff_convex]
  have hh := (strongConcaveOn_iff_convex.mp (dualRegularizedSection_stronglyConcave P μ y0 x)).add_const
    (p.L * ‖x - c‖ ^ 2)
  convert hh using 1
  ext y
  simp only [saddleObjective, Pi.add_apply]
  ring

/-- The two genuine section support inequalities give the saddle support
inequality used in Appendix B.2. -/
theorem saddleOperator_support (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (μ : ℝ) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (z z' : JointSpace dx dy) (hz : z ∈ productDomain dx K) (hz' : z' ∈ productDomain dx K) :
    saddleObjective P μ y0 c z.fst z'.snd - saddleObjective P μ y0 c z'.fst z.snd +
      p.L / 2 * ‖z.fst - z'.fst‖ ^ 2 + μ / 2 * ‖z.snd - z'.snd‖ ^ 2 ≤
      ⟪saddleOperator P μ y0 c z, z - z'⟫_ℝ := by
  have hp := strongConvex_gradient_support
    (saddle_primal_stronglyConvex P hAS μ y0 c z.snd hz)
    (mem_univ z.fst) (mem_univ z'.fst)
    (saddle_primal_hasGradientAt P μ y0 c z.fst z.snd hz)
  have hd := strongConcave_gradient_support (saddle_dual_stronglyConcave P μ y0 c z.fst)
    hz hz' (saddle_dual_hasGradientAt P μ y0 c z.fst z.snd hz)
  change saddleObjective P μ y0 c z.fst z.snd +
    ⟪saddlePrimalGradient P c z, z'.fst - z.fst⟫_ℝ +
    p.L / 2 * ‖z'.fst - z.fst‖ ^ 2 ≤ saddleObjective P μ y0 c z'.fst z.snd at hp
  change saddleObjective P μ y0 c z.fst z'.snd ≤ saddleObjective P μ y0 c z.fst z.snd +
    ⟪saddleDualGradient P μ y0 z, z'.snd - z.snd⟫_ℝ -
    μ / 2 * ‖z'.snd - z.snd‖ ^ 2 at hd
  rw [norm_sub_rev z'.fst z.fst, inner_sub_right] at hp
  rw [norm_sub_rev z'.snd z.snd, inner_sub_right] at hd
  change saddleObjective P μ y0 c z.fst z'.snd - saddleObjective P μ y0 c z'.fst z.snd +
      p.L / 2 * ‖z.fst - z'.fst‖ ^ 2 + μ / 2 * ‖z.snd - z'.snd‖ ^ 2 ≤
      ⟪saddlePrimalGradient P c z, z.fst - z'.fst⟫_ℝ +
        ⟪-saddleDualGradient P μ y0 z, z.snd - z'.snd⟫_ℝ
  simp only [inner_neg_left, inner_sub_right]
  nlinarith only [hp, hd]

/-- The anisotropic strong monotonicity follows by adding the support
inequality in the two orders; no cross-Hessian cancellation is assumed. -/
theorem saddleOperator_anisotropic_monotone (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (μ : ℝ) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (z z' : JointSpace dx dy) (hz : z ∈ productDomain dx K) (hz' : z' ∈ productDomain dx K) :
    p.L * ‖z.fst - z'.fst‖ ^ 2 + μ * ‖z.snd - z'.snd‖ ^ 2 ≤
      ⟪saddleOperator P μ y0 c z - saddleOperator P μ y0 c z', z - z'⟫_ℝ := by
  have h1 := saddleOperator_support P hAS μ y0 c z z' hz hz'
  have h2 := saddleOperator_support P hAS μ y0 c z' z hz' hz
  have he : z' - z = -(z - z') := by abel
  rw [he, inner_neg_right, norm_sub_rev z'.fst z.fst, norm_sub_rev z'.snd z.snd] at h2
  rw [inner_sub_left]
  nlinarith only [h1, h2]

def dualSign (z : JointSpace dx dy) : JointSpace dx dy := jointPoint z.fst (-z.snd)

theorem dualSign_sub (z z' : JointSpace dx dy) :
    dualSign (z - z') = dualSign z - dualSign z' := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · rfl
  · change -(z.snd - z'.snd) = -z.snd - (-z'.snd)
    abel

theorem dualSign_norm (z : JointSpace dx dy) : ‖dualSign z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖z.fst‖ ^ 2 + ‖-z.snd‖ ^ 2 = ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2
  rw [norm_neg]

def dualSignLinear (dx dy : ℕ) : JointSpace dx dy →ₗ[ℝ] JointSpace dx dy where
  toFun := dualSign
  map_add' := by
    intro z z'
    apply WithLp.ofLp_injective
    apply Prod.ext
    · rfl
    · change -(z.snd + z'.snd) = -z.snd + -z'.snd
      abel
  map_smul' := by
    intro a z
    apply WithLp.ofLp_injective
    apply Prod.ext
    · rfl
    · change -(a • z.snd) = a • (-z.snd)
      module

def signedComponentGradient (P : Problem p dx dy K) (i : Fin p.n) (z : JointSpace dx dy) :=
  dualSign (P.componentGradient i z)

theorem averageMap_signedComponentGradient (P : Problem p dx dy K) (z : JointSpace dx dy) :
    averageMap (signedComponentGradient P) z = dualSign (averageMap P.componentGradient z) := by
  change (p.n : ℝ)⁻¹ • ∑ i, dualSignLinear dx dy (P.componentGradient i z) =
    dualSignLinear dx dy ((p.n : ℝ)⁻¹ • ∑ i, P.componentGradient i z)
  rw [map_smul, map_sum]

theorem signedComponentGradient_averagedSmooth (P : Problem p dx dy K) (hAS : P.averagedSmooth) :
    AveragedSmooth (signedComponentGradient P) (productDomain dx K) p.L := by
  intro z hz z' hz'
  simpa only [signedComponentGradient, ← dualSign_sub, dualSign_norm] using hAS z hz z' hz'

def saddleCorrection (L μ : ℝ) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (z : JointSpace dx dy) : JointSpace dx dy :=
  jointPoint ((2 * L) • (z.fst - c)) (μ • (z.snd - y0))

theorem saddleOperator_eq_signed_plus_correction (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (c : PrimalSpace dx) (z : JointSpace dx dy) :
    saddleOperator P μ y0 c z =
      dualSign (averageMap P.componentGradient z) + saddleCorrection p.L μ y0 c z := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · rfl
  · change -((averageMap P.componentGradient z).snd - μ • (z.snd - y0)) =
      -(averageMap P.componentGradient z).snd + μ • (z.snd - y0)
    abel

theorem saddleCorrection_lipschitz (L μ : ℝ) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hμL : μ ≤ L)
    (y0 : DualSpace dy) (c : PrimalSpace dx) (z z' : JointSpace dx dy) :
    ‖saddleCorrection L μ y0 c z - saddleCorrection L μ y0 c z'‖ ≤ 2 * L * ‖z - z'‖ := by
  have he : saddleCorrection L μ y0 c z - saddleCorrection L μ y0 c z' =
      jointPoint ((2 * L) • (z.fst - z'.fst)) (μ • (z.snd - z'.snd)) := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · change (2 * L) • (z.fst - c) - (2 * L) • (z'.fst - c) =
        (2 * L) • (z.fst - z'.fst)
      module
    · change μ • (z.snd - y0) - μ • (z'.snd - y0) = μ • (z.snd - z'.snd)
      module
  have hsq : ‖saddleCorrection L μ y0 c z - saddleCorrection L μ y0 c z'‖ ^ 2 =
      (2 * L) ^ 2 * ‖z.fst - z'.fst‖ ^ 2 + μ ^ 2 * ‖z.snd - z'.snd‖ ^ 2 := by
    rw [he, WithLp.prod_norm_sq_eq_of_L2]
    simp only [jointPoint, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have hmu2 : μ ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hμ (by linarith) 2
  have hm := mul_le_mul_of_nonneg_right hmu2 (sq_nonneg ‖z.snd - z'.snd‖)
  have hnorm := joint_difference_norm_sq z z'
  have hnormscale := congrArg (fun r : ℝ => (2 * L) ^ 2 * r) hnorm
  have hsquare : ‖saddleCorrection L μ y0 c z - saddleCorrection L μ y0 c z'‖ ^ 2 ≤
      (2 * L * ‖z - z'‖) ^ 2 := by nlinarith only [hsq, hm, hnormscale]
  have hr : 0 ≤ 2 * L * ‖z - z'‖ := by positivity
  nlinarith only [hsquare, norm_nonneg (saddleCorrection L μ y0 c z - saddleCorrection L μ y0 c z'), hr]

/-- The concrete operator has the `3L` Lipschitz constant claimed in B.2. -/
theorem saddleOperator_lipschitz (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 ≤ μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (z z' : JointSpace dx dy) (hz : z ∈ productDomain dx K) (hz' : z' ∈ productDomain dx K) :
    ‖saddleOperator P μ y0 c z - saddleOperator P μ y0 c z'‖ ≤ 3 * p.L * ‖z - z'‖ := by
  rw [saddleOperator_eq_signed_plus_correction, saddleOperator_eq_signed_plus_correction]
  have he : dualSign (averageMap P.componentGradient z) + saddleCorrection p.L μ y0 c z -
      (dualSign (averageMap P.componentGradient z') + saddleCorrection p.L μ y0 c z') =
      (dualSign (averageMap P.componentGradient z) - dualSign (averageMap P.componentGradient z')) +
        (saddleCorrection p.L μ y0 c z - saddleCorrection p.L μ y0 c z') := by abel
  rw [he]
  calc
    _ ≤ ‖dualSign (averageMap P.componentGradient z) - dualSign (averageMap P.componentGradient z')‖ +
        ‖saddleCorrection p.L μ y0 c z - saddleCorrection p.L μ y0 c z'‖ := norm_add_le _ _
    _ = ‖averageMap P.componentGradient z - averageMap P.componentGradient z'‖ +
        ‖saddleCorrection p.L μ y0 c z - saddleCorrection p.L μ y0 c z'‖ := by
      rw [← dualSign_sub, dualSign_norm]
    _ ≤ p.L * ‖z - z'‖ + 2 * p.L * ‖z - z'‖ :=
      add_le_add (P.average_gradient_lipschitz hAS z hz z' hz')
        (saddleCorrection_lipschitz p.L μ p.L_pos.le hμ hμL y0 c z z')
    _ = 3 * p.L * ‖z - z'‖ := by ring

end

end NCConcave16991
