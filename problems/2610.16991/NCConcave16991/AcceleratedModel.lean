import NCConcave16991.SaddleSupport
import NCConcave16991.SVRGResidual
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Order.Compact

/-!
# Actual affine models from checked primal-dual residuals

The dual objective is the supremum of the actual negative saddle sections.
The affine lower model is derived from actual section derivatives, convexity,
concavity and outward normal-cone residuals, rather than assumed.
-/

noncomputable section

open Set
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Accelerated

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- A genuine differentiable compact convex-concave saddle problem. -/
structure CompactSaddle (X Y : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] where
  primal : Set X
  dual : Set Y
  primal_nonempty : primal.Nonempty
  dual_nonempty : dual.Nonempty
  primal_compact : IsCompact primal
  dual_compact : IsCompact dual
  primal_convex : Convex ℝ primal
  dual_convex : Convex ℝ dual
  objective : X → Y → ℝ
  gradientX : X → Y → X
  gradientY : X → Y → Y
  convexX : ∀ y ∈ dual, ConvexOn ℝ primal (fun x ↦ objective x y)
  concaveY : ∀ x ∈ primal, ConcaveOn ℝ dual (objective x)
  continuousX : ∀ y ∈ dual, ContinuousOn (fun x ↦ objective x y) primal
  continuousY : ∀ x ∈ primal, ContinuousOn (objective x) dual
  derivativeX : ∀ x ∈ primal, ∀ y ∈ dual, HasGradientAt (fun u ↦ objective u y) (gradientX x y) x
  derivativeY : ∀ x ∈ primal, ∀ y ∈ dual, HasGradientAt (objective x) (gradientY x y) y

variable (F : CompactSaddle X Y)

/-- The actual convex dual objective `-min_x F(x,y)`. -/
def dualValue (y : Y) : ℝ := sSup ((fun x ↦ -F.objective x y) '' F.primal)

/-- The actual primal objective `max_y F(x,y)`. -/
def primalValue (x : X) : ℝ := sSup (F.objective x '' F.dual)

 theorem dualValue_bddAbove {y : Y} (hy : y ∈ F.dual) :
    BddAbove ((fun x ↦ -F.objective x y) '' F.primal) :=
  (F.primal_compact.image_of_continuousOn (F.continuousX y hy).neg).bddAbove

 theorem primalValue_bddAbove {x : X} (hx : x ∈ F.primal) :
    BddAbove (F.objective x '' F.dual) :=
  (F.dual_compact.image_of_continuousOn (F.continuousY x hx)).bddAbove

 theorem negative_section_le_dual {x : X} (hx : x ∈ F.primal) {y : Y} (hy : y ∈ F.dual) :
    -F.objective x y ≤ dualValue F y :=
  le_csSup (dualValue_bddAbove F hy) ⟨x, hx, rfl⟩

 theorem section_le_primal {x : X} (hx : x ∈ F.primal) {y : Y} (hy : y ∈ F.dual) :
    F.objective x y ≤ primalValue F x :=
  le_csSup (primalValue_bddAbove F hx) ⟨y, hy, rfl⟩

/-- The actual dual supremum is attained and is the negative of an actual minimum. -/
theorem dualValue_attained {y : Y} (hy : y ∈ F.dual) :
    ∃ x ∈ F.primal, dualValue F y = -F.objective x y ∧
      ∀ u ∈ F.primal, F.objective x y ≤ F.objective u y := by
  obtain ⟨x, hx, hmin⟩ := F.primal_compact.exists_isMinOn F.primal_nonempty (F.continuousX y hy)
  refine ⟨x, hx, le_antisymm ?_ (negative_section_le_dual F hx hy), hmin⟩
  apply csSup_le (F.primal_nonempty.image _)
  rintro v ⟨u, hu, rfl⟩
  exact neg_le_neg (hmin hu)

/-- The first-order convex support inequality follows from the actual derivative. -/
theorem primal_support {x u : X} (hx : x ∈ F.primal) (hu : u ∈ F.primal)
    {y : Y} (hy : y ∈ F.dual) :
    F.objective x y + ⟪F.gradientX x y, u - x⟫_ℝ ≤ F.objective u y := by
  have hc : StrongConvexOn F.primal 0 (fun u ↦ F.objective u y) := by
    rw [strongConvexOn_iff_convex]
    simpa using F.convexX y hy
  simpa using strongConvex_gradient_support hc hx hu (F.derivativeX x hx y hy)

 theorem dual_support {x : X} (hx : x ∈ F.primal) {y w : Y}
    (hy : y ∈ F.dual) (hw : w ∈ F.dual) :
    F.objective x w ≤ F.objective x y + ⟪F.gradientY x y, w - y⟫_ℝ := by
  have hc : StrongConcaveOn F.dual 0 (F.objective x) := by
    rw [strongConcaveOn_iff_convex]
    simpa using F.concaveY x hx
  simpa using strongConcave_gradient_support hc hy hw (F.derivativeY x hx y hy)

/-- A concrete saddle solve result with feasible primal and dual points and explicit normals. -/
structure ProxResult where
  x : X
  y : Y
  normalX : X
  normalY : Y

/-- The observable checked block residual, expressed with the actual section gradients. -/
def ResidualCheck (τ ζ : ℝ) (v : Y) (r : ProxResult (X := X) (Y := Y)) : Prop :=
  r.x ∈ F.primal ∧ r.y ∈ F.dual ∧
  r.normalX ∈ SVRG.normalCone F.primal r.x ∧
  r.normalY ∈ SVRG.normalCone F.dual r.y ∧
  ‖F.gradientX r.x r.y + r.normalX‖ ≤ ζ ∧
  ‖-F.gradientY r.x r.y + τ • (r.y - v) + r.normalY‖ ≤ ζ

/-- The residual blocks give a lower affine model of the actual negative primal section. -/
theorem residual_affine_model {DX DY τ ζ : ℝ}
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    {v : Y} {r : ProxResult (X := X) (Y := Y)} (hr : ResidualCheck F τ ζ v r)
    {w : Y} (hw : w ∈ F.dual) :
    dualValue F r.y + ⟪τ • (v - r.y), w - r.y⟫_ℝ - (DX + DY) * ζ ≤
      -F.objective r.x w := by
  rcases hr with ⟨hx, hy, hnx, hny, hrx, hry⟩
  have hζ : 0 ≤ ζ := (norm_nonneg _).trans hrx
  have hprimal : dualValue F r.y ≤ -F.objective r.x r.y + DX * ζ := by
    apply csSup_le (F.primal_nonempty.image _)
    rintro q ⟨u, hu, rfl⟩
    have hs := primal_support F hx hu hy
    have hn := hnx u hu
    have hi := real_inner_le_norm (-(F.gradientX r.x r.y + r.normalX)) (u - r.x)
    simp only [inner_neg_left, norm_neg, inner_add_left] at hi
    have hb := mul_le_mul hrx (hDX u hu r.x hx) (norm_nonneg _) hζ
    nlinarith
  have hs := dual_support F hx hy hw
  have hn := hny w hw
  have hi := real_inner_le_norm (-(-F.gradientY r.x r.y + τ • (r.y - v) + r.normalY)) (w - r.y)
  have hb := mul_le_mul hry (hDY w hw r.y hy) (norm_nonneg _) hζ
  have hdiff : τ • (r.y - v) = -(τ • (v - r.y)) := by rw [smul_sub, smul_sub]; abel
  simp only [inner_neg_left, norm_neg] at hi
  rw [hdiff] at hi hb
  simp only [inner_add_left, inner_neg_left] at hi
  nlinarith

/-- The same model is a lower model of the genuine dual objective. -/
theorem residual_dual_model {DX DY τ ζ : ℝ}
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    {v : Y} {r : ProxResult (X := X) (Y := Y)} (hr : ResidualCheck F τ ζ v r)
    {w : Y} (hw : w ∈ F.dual) :
    dualValue F r.y + ⟪τ • (v - r.y), w - r.y⟫_ℝ - (DX + DY) * ζ ≤ dualValue F w :=
  (residual_affine_model F hDX hDY hr hw).trans (negative_section_le_dual F hr.1 hw)

/-- The actual Euclidean product residual in the paper's check. -/
def jointResidual (τ : ℝ) (v : Y) (r : ProxResult (X := X) (Y := Y)) : WithLp 2 (X × Y) :=
  WithLp.toLp 2 (F.gradientX r.x r.y + r.normalX,
    -F.gradientY r.x r.y + τ • (r.y - v) + r.normalY)

/-- A bound on the genuine joint norm implies both block checks used in the proof. -/
theorem residualCheck_of_joint {τ ζ : ℝ} {v : Y} {r : ProxResult (X := X) (Y := Y)}
    (hx : r.x ∈ F.primal) (hy : r.y ∈ F.dual)
    (hnx : r.normalX ∈ SVRG.normalCone F.primal r.x)
    (hny : r.normalY ∈ SVRG.normalCone F.dual r.y)
    (hr : ‖jointResidual F τ v r‖ ≤ ζ) : ResidualCheck F τ ζ v r := by
  refine ⟨hx, hy, hnx, hny, ?_, ?_⟩
  · exact (WithLp.norm_fst_le X (jointResidual F τ v r)).trans hr
  · exact (WithLp.norm_snd_le X (jointResidual F τ v r)).trans hr

end NCConcave16991.Accelerated



