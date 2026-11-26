import NoisyZO.Model
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Transferring highest-derivative Hölder control to the gradient

For a real Hilbert space, the gradient is the inverse Riesz isometry applied
to the Fréchet derivative.  Currying identifies the `(k - 1)`-st derivative
of that derivative with the `k`-th derivative of the scalar function.  Both
identifications preserve the multilinear operator norm.
-/

open scoped ContDiff Gradient InnerProductSpace

namespace NoisyZO

noncomputable section

/-- The zeroth iterated Fréchet derivative is the original value embedded by
an isometry, so it preserves norms of differences. -/
theorem norm_iteratedFDeriv_zero_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ =
      ‖f x - f y‖ := by
  let C := (continuousMultilinearCurryFin0 ℝ E F).symm
  change ‖C (f x) - C (f y)‖ = ‖f x - f y‖
  rw [← C.map_sub, C.norm_map]

/-- The operator norm of a difference of `(k-1)`-st gradient derivatives is
exactly the norm of the corresponding difference of `k`-th derivatives. -/
theorem norm_iteratedFDeriv_gradient_sub
    {d m : ℕ} (f : Point d → ℝ) (x y : Point d) :
    ‖iteratedFDeriv ℝ m (∇ f) x - iteratedFDeriv ℝ m (∇ f) y‖ =
      ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ := by
  let L := (InnerProductSpace.toDual ℝ (Point d)).symm
  let C := (continuousMultilinearCurryRightEquiv' ℝ m (Point d) ℝ).symm
  have hgrad (z : Point d) :
      iteratedFDeriv ℝ m (∇ f) z =
        L.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (fderiv ℝ f) z) := by
    change iteratedFDeriv ℝ m (L ∘ fderiv ℝ f) z = _
    exact L.toContinuousLinearEquiv.iteratedFDeriv_comp_left
  have hcurry (z : Point d) :
      iteratedFDeriv ℝ (m + 1) f z =
        C (iteratedFDeriv ℝ m (fderiv ℝ f) z) := by
    have h := iteratedFDeriv_succ_eq_comp_right
      (𝕜 := ℝ) (f := f) (x := z) (n := m)
    simpa only [C, Function.comp_apply] using h
  let Ax := iteratedFDeriv ℝ m (fderiv ℝ f) x
  let Ay := iteratedFDeriv ℝ m (fderiv ℝ f) y
  have hcomp :
      L.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap Ax -
          L.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap Ay =
        L.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
          (Ax - Ay) := by
    ext v
    simp
  calc
    ‖iteratedFDeriv ℝ m (∇ f) x - iteratedFDeriv ℝ m (∇ f) y‖ =
        ‖L.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap Ax -
          L.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap Ay‖ := by
            rw [hgrad x, hgrad y]
    _ = ‖L.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
          (Ax - Ay)‖ := by rw [hcomp]
    _ = ‖Ax - Ay‖ := by
      exact L.toLinearIsometry.norm_compContinuousMultilinearMap (Ax - Ay)
    _ = ‖C (Ax - Ay)‖ := (C.norm_map (Ax - Ay)).symm
    _ = ‖C Ax - C Ay‖ := by rw [C.map_sub]
    _ = ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ := by
      rw [hcurry x, hcurry y]

/-- The Riesz and currying isometries identify gradient increments with
first Fréchet-derivative increments. -/
theorem norm_gradient_sub_eq_iteratedFDeriv_one_sub
    {d : ℕ} (f : Point d → ℝ) (x y : Point d) :
    ‖∇ f x - ∇ f y‖ =
      ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ := by
  calc
    ‖∇ f x - ∇ f y‖ =
        ‖iteratedFDeriv ℝ 0 (∇ f) x -
          iteratedFDeriv ℝ 0 (∇ f) y‖ := by
      symm
      exact norm_iteratedFDeriv_zero_sub (∇ f) x y
    _ = ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ := by
      simpa only [Nat.zero_add] using
        norm_iteratedFDeriv_gradient_sub f x y (m := 0)

/-- The class's highest-derivative Hölder field is therefore precisely the
Hölder premise required by vector Taylor expansion of the gradient. -/
theorem NormalizedObjective.gradient_higher_holder
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x y : Point d) :
    ‖iteratedFDeriv ℝ (o.k - 1) (∇ F.f) x -
        iteratedFDeriv ℝ (o.k - 1) (∇ F.f) y‖ ≤
      ‖x - y‖ ^ o.alpha := by
  have hk1 : 1 ≤ o.k := le_trans (by omega) o.two_le_k
  calc
    ‖iteratedFDeriv ℝ (o.k - 1) (∇ F.f) x -
        iteratedFDeriv ℝ (o.k - 1) (∇ F.f) y‖ =
        ‖iteratedFDeriv ℝ ((o.k - 1) + 1) F.f x -
          iteratedFDeriv ℝ ((o.k - 1) + 1) F.f y‖ :=
      norm_iteratedFDeriv_gradient_sub F.f x y
    _ = ‖iteratedFDeriv ℝ o.k F.f x - iteratedFDeriv ℝ o.k F.f y‖ := by
      rw [Nat.sub_add_cancel hk1]
    _ ≤ ‖x - y‖ ^ o.alpha := F.higher_holder x y

end

end NoisyZO
