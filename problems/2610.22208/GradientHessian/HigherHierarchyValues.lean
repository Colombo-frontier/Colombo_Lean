import GradientHessian.HigherHierarchyZero
import GradientHessian.HigherHierarchyNodeValues
import GradientHessian.HigherHierarchyBaseline

/-! Actual recursive value and energy bounds. The only hypotheses on the
tree are source coefficient validity and the fixed scale separation. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u
open InnerCoordinates

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

/-- The one shared numerical block, through all Euclidean physical layers. -/
def numericalProjection : (t : ℕ) → Space Y E H m t →L[ℝ] Y
  | 0 => (numerical Y E (m+1) (Inner.absoluteDepth+2)).comp
      (numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2))
  | t+1 => (numericalProjection t).comp (lower (Space Y E H m t) (H t))

theorem numericalProjection_norm_le : (t : ℕ) → ‖numericalProjection (Y := Y) (E := E) (H := H) (m := m) t‖ ≤ 1
  | 0 => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (Inner.numerical_norm_le _ _) (Inner.numerical_norm_le _ _)
        (norm_nonneg (numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2)))
        zero_le_one).trans_eq (one_mul 1))
  | t+1 => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (numericalProjection_norm_le t) (lower_norm_le _ _)
        (norm_nonneg (lower (Space Y E H m t) (H t))) zero_le_one).trans_eq (one_mul 1))

variable [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)]

theorem residual_global_bounds {K : ℝ} (hK : 16 ≤ K) :
    ∀ t (d : Data Y E H m t), Valid Y E H m t d → ∀ Z : Space Y E H m t,
      -energy m K t - Leaf.leafJetConstant*(m+1:ℝ)^3 ≤ residual K t d Z ∧ residual K t d Z ≤ 0 := by
  intro t
  induction t with
  | zero =>
    intro d hd Z
    exact ⟨FirstHeight.sourceResidual_global_lower d hd Z, FirstHeight.sourceResidual_nonpos d hd.opNorm Z⟩
  | succ t ih =>
    intro d hd Z
    have h := nodeResidual_bounds (baseline K t) (fun i => scalar K t (d.children i))
      (fun i => outgoing K t (d.children i)) (energy_pos m (K := K) (by linarith) t).le
      (mul_nonneg Leaf.leafJetConstant_pos.le (by positivity))
      (width_pos m t) (scale_separation m hK t) (centers K d)
      (centers_norm (by linarith) d hd) Z
      (fun i => ih (d.children i) (hd.1 i) (lower _ _ Z))
      (fun i => outgoing_bounds K t (d.children i) (lower _ _ Z))
    simpa only [residual, scalar, baseline, nodeResidual, energy_succ, spacing] using h

theorem residual_nonpos {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (Z : Space Y E H m t) : residual K t d Z ≤ 0 :=
  (residual_global_bounds hK t d hd Z).2

omit [CompleteSpace E] in
theorem residual_bounded {K : ℝ} (hK : 16 ≤ K) :
    ∀ t (d : Data Y E H m t), Valid Y E H m t d → ∀ Z : Space Y E H m t,
      ‖numericalProjection t Z‖ ≤ Leaf.numericalRadius →
      -energy m K t ≤ residual K t d Z ∧ residual K t d Z ≤ 0 := by
  intro t
  induction t with
  | zero =>
    intro d hd Z hZ
    exact FirstHeight.sourceResidual_bounded d hd.opNorm Z hZ
  | succ t ih =>
    intro d hd Z hZ
    have hf (i : Fin 8) := ih (d.children i) (hd.1 i) (lower _ _ Z) hZ
    have h := nodeResidual_bounds (baseline K t) (fun i => scalar K t (d.children i))
      (fun i => outgoing K t (d.children i)) (energy_pos m (K := K) (by linarith) t).le
      (C := 0) le_rfl (width_pos m t) (scale_separation m hK t) (centers K d)
      (centers_norm (by linarith) d hd) Z
      (fun i => by simpa only [sub_zero] using hf i)
      (fun i => outgoing_bounds K t (d.children i) (lower _ _ Z))
    simpa only [residual, scalar, baseline, nodeResidual, energy_succ, spacing, sub_zero] using h

omit [CompleteSpace E] in
theorem scalar_energy {K : ℝ} (hK : 16 ≤ K) :
    ∀ t (d : Data Y E H m t), Valid Y E H m t d → ∀ Z : Space Y E H m t,
      positiveBaseline K t Z - energy m K t - Inner.innerConstant*(m+1:ℝ) ≤ scalar K t d Z := by
  intro t
  induction t with
  | zero =>
    intro d hd Z
    exact FirstHeight.sourceNode_energy d hd.lower Z
  | succ t ih =>
    intro d hd Z
    have h := nodeScalar_energy (baseline K t) (fun i => scalar K t (d.children i))
      (fun i => outgoing K t (d.children i)) (energy_pos m (K := K) (by linarith) t).le
      (mul_nonneg Inner.innerConstant_pos.le (by positivity))
      (width_pos m t) (scale_separation m hK t) (centers K d)
      (centers_norm (by linarith) d hd) Z
      (positiveBaseline_le_baseline K t (lower _ _ Z))
      (fun i => ih (d.children i) (hd.1 i) (lower _ _ Z))
      (fun i => outgoing_bounds K t (d.children i) (lower _ _ Z))
    simpa only [scalar, positiveBaseline, nodeBaseline, energy_succ, spacing] using h

omit [CompleteSpace E] in
theorem scalar_lower {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (Z : Space Y E H m t) :
    -energy m K t - Inner.innerConstant*(m+1:ℝ) ≤ scalar K t d Z := by
  have hp := positiveBaseline_nonneg (by linarith : 0 ≤ K) t Z
  have hf := scalar_energy hK t d hd Z
  linarith

omit [CompleteSpace E] in
theorem scalar_coercive {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) :
    Filter.Tendsto (scalar K t d) (Bornology.cobounded (Space Y E H m t)) Filter.atTop := by
  apply HierarchyCoercivity.coercive_of_linear_lower
    (C := positiveOffset m K t + energy m K t + Inner.innerConstant*(m+1:ℝ))
    (HierarchyCoercivity.firstCoefficient_pos m)
  intro Z
  have hp := positiveBaseline_linear_lower K t Z
  have hf := scalar_energy hK t d hd Z
  linarith

end GradientHessian.HigherHierarchy
