import NCConcave16991.BranchGeometry
import NCConcave16991.EndpointConstants
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Actual joint gradient and uniform smoothness of selected pipe components

The joint space uses the Hilbert L² norm, including both primal connector
coordinates and every dual layer. We construct a continuous bilinear form
from the literal component formula. Its symmetrization is the actual Hessian
operator, and its action is proved to be the actual gradient. Polarization
turns the already proved explicit quadratic estimate into the dimension-free
Hessian bound 8. No differentiability or Hessian estimate is an input.
-/

namespace NCConcave16991.PipeSmoothness

open scoped BigOperators InnerProductSpace
open BranchGeometry

set_option synthInstance.maxHeartbeats 200000

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Hessian of the diagonal of an actual continuous bilinear form. -/
noncomputable def quadraticHessian (q : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (q + q.flip)

theorem quadraticHessian_inner (q : E →L[ℝ] E →L[ℝ] ℝ) (x y : E) :
    ⟪quadraticHessian q x, y⟫_ℝ = q x y + q y x := by
  change ⟪(InnerProductSpace.toDual ℝ E).symm ((q + q.flip) x), y⟫_ℝ = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem quadratic_hasGradientAt (q : E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    HasGradientAt (fun z => q z z) (quadraticHessian q x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (q.hasFDerivAt_of_bilinear (hasFDerivAt_id (𝕜 := ℝ) x)
    (hasFDerivAt_id (𝕜 := ℝ) x)).congr_fderiv ?_
  ext y
  change q x y + q y x = ⟪quadraticHessian q x, y⟫_ℝ
  rw [quadraticHessian_inner]

theorem quadraticHessian_isSymmetric (q : E →L[ℝ] E →L[ℝ] ℝ) :
    (quadraticHessian q : E →ₗ[ℝ] E).IsSymmetric := by
  intro x y
  change ⟪quadraticHessian q x, y⟫_ℝ = ⟪x, quadraticHessian q y⟫_ℝ
  calc
    _ = q x y + q y x := quadraticHessian_inner q x y
    _ = q y x + q x y := add_comm _ _
    _ = ⟪quadraticHessian q y, x⟫_ℝ := (quadraticHessian_inner q y x).symm
    _ = _ := real_inner_comm _ _

/-- A bound on the literal diagonal quadratic form gives the exact sharp
factor two for its Hessian, proved by real polarization on unit vectors. -/
theorem quadraticHessian_norm_le (q : E →L[ℝ] E →L[ℝ] ℝ)
    (hquad : ∀ z, |q z z| ≤ 4 * ‖z‖ ^ 2) : ‖quadraticHessian q‖ ≤ 8 := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by norm_num : (0 : ℝ) ≤ 8)
  intro x y hx hy
  have hp := (abs_le.mp (hquad (x + y))).2
  have hm := (abs_le.mp (hquad (x - y))).1
  have hpar := parallelogram_law_with_norm ℝ x y
  have hpol : q (x + y) (x + y) - q (x - y) (x - y) =
      2 * (q x y + q y x) := by
    simp only [map_add, map_sub, add_apply, sub_apply]
    ring
  rw [quadraticHessian_inner]
  simp only [RCLike.re_to_real]
  rw [hx, hy] at hpar
  nlinarith

theorem quadratic_gradient_lipschitz (q : E →L[ℝ] E →L[ℝ] ℝ)
    (hquad : ∀ z, |q z z| ≤ 4 * ‖z‖ ^ 2) (x y : E) :
    ‖gradient (fun z => q z z) x - gradient (fun z => q z z) y‖ ≤ 8 * ‖x - y‖ := by
  rw [(quadratic_hasGradientAt q x).gradient, (quadratic_hasGradientAt q y).gradient,
    ← map_sub]
  exact (quadraticHessian q).le_opNorm (x - y) |>.trans
    (mul_le_mul_of_nonneg_right (quadraticHessian_norm_le q hquad) (norm_nonneg _))

end Quadratic

section Pipe

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {N : ℕ} {V : Fin (N + 1) → Type*}
    [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
    [∀ j, CompleteSpace (V j)]

abbrev Layers (V : Fin (N + 1) → Type*) := PiLp 2 V
abbrev Connectors (V : Fin (N + 1) → Type*) := WithLp 2 (V 0 × V (Fin.last N))
abbrev Joint (V : Fin (N + 1) → Type*) := WithLp 2 (Connectors V × Layers V)

noncomputable def aProj : Joint V →L[ℝ] V 0 :=
  (WithLp.fstL 2 ℝ (V 0) (V (Fin.last N))).comp
    (WithLp.fstL 2 ℝ (Connectors V) (Layers V))

noncomputable def bProj : Joint V →L[ℝ] V (Fin.last N) :=
  (WithLp.sndL 2 ℝ (V 0) (V (Fin.last N))).comp
    (WithLp.fstL 2 ℝ (Connectors V) (Layers V))

noncomputable def wProj (j : Fin (N + 1)) : Joint V →L[ℝ] V j :=
  (PiLp.proj 2 V j).comp (WithLp.sndL 2 ℝ (Connectors V) (Layers V))

omit [∀ j, CompleteSpace (V j)] in
theorem joint_norm_sq (z : Joint V) :
    ‖z‖ ^ 2 = ‖aProj z‖ ^ 2 + ‖bProj z‖ ^ 2 + ∑ j, ‖wProj j z‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

noncomputable def innerPair {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P Q : Joint V →L[ℝ] H) : Joint V →L[ℝ] Joint V →L[ℝ] ℝ :=
  (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).bilinearComp P Q

omit [∀ j, CompleteSpace (V j)] in
theorem innerPair_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P Q : Joint V →L[ℝ] H) (x y : Joint V) : innerPair P Q x y = ⟪P x, Q y⟫_ℝ := rfl

/-- Actual bounded bilinear form, retaining every literal connector, mass,
edge diagonal, and selected branch coupling of the paper's component. -/
noncomputable def componentBilinear
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (i : ι) : Joint V →L[ℝ] Joint V →L[ℝ] ℝ :=
  d • (innerPair aProj aProj + innerPair bProj bProj) +
  r • (innerPair aProj (wProj 0) - innerPair bProj (wProj (Fin.last N))) -
  (beta ι / 2) • (μ • (∑ j, innerPair (wProj j) (wProj j)) +
    ∑ t : Fin N, (innerPair (wProj t.castSucc) (wProj t.castSucc) +
      innerPair (wProj t.succ) (wProj t.succ))) +
  ∑ t : Fin N, innerPair (wProj t.succ)
    (((B t).branch i).toContinuousLinearMap.comp (wProj t.castSucc))

omit [Nonempty ι] [∀ j, CompleteSpace (V j)] in
theorem componentBilinear_diagonal
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (i : ι) (z : Joint V) :
    componentBilinear B d r μ i z z =
      fullPipeComponent B d r μ (aProj z) (bProj z) (fun j => wProj j z) i := by
  simp [componentBilinear, innerPair_apply, fullPipeComponent, pipeComponent]
  ring

/-- The actual selected component, on the correct joint Hilbert L² space. -/
noncomputable def component
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (i : ι) (z : Joint V) : ℝ :=
  fullPipeComponent B d r μ (aProj z) (bProj z) (fun j => wProj j z) i

omit [Nonempty ι] in
theorem component_hasGradientAt
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (i : ι) (z : Joint V) :
    HasGradientAt (component B d r μ i)
      (quadraticHessian (componentBilinear B d r μ i) z) z := by
  convert quadratic_hasGradientAt (componentBilinear B d r μ i) z using 1
  ext x
  exact (componentBilinear_diagonal B d r μ i x).symm

omit [Nonempty ι] in
/-- The named operator is the derivative of the actual joint gradient and
therefore the actual constant Hessian of the component. -/
theorem component_gradient_hasFDerivAt
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (i : ι) (z : Joint V) :
    HasFDerivAt (gradient (component B d r μ i))
      (quadraticHessian (componentBilinear B d r μ i)) z := by
  have hg : gradient (component B d r μ i) =
      quadraticHessian (componentBilinear B d r μ i) := by
    funext x
    exact (component_hasGradientAt B d r μ i x).gradient
  rw [hg]
  exact ContinuousLinearMap.hasFDerivAt _

/-- E.12(i): each literal selected component has a global joint gradient
Lipschitz constant 8, uniformly in the number of layers, branch dimension,
and component count. The scalar hypotheses hold for the paper's endpoint
constants and normalized branch parameter. -/
theorem component_gradient_lipschitz
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (i : ι) (x y : Joint V) :
    ‖gradient (component B d r μ i) x - gradient (component B d r μ i) y‖ ≤
      8 * ‖x - y‖ := by
  have hq : ∀ z : Joint V, |componentBilinear B d r μ i z z| ≤ 4 * ‖z‖ ^ 2 := by
    intro z
    rw [componentBilinear_diagonal, joint_norm_sq]
    exact fullPipeComponent_quadratic_bound B d r μ hd hr hμ0 hμ1 _ _ _ i
  have heq : component B d r μ i = fun z => componentBilinear B d r μ i z z := by
    funext z
    exact (componentBilinear_diagonal B d r μ i z).symm
  rw [heq]
  exact quadratic_gradient_lipschitz _ hq x y

end Pipe

section PaperParameters

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem endpoint_coupling_le_one (m : ℕ) :
    |Real.sqrt (beta ι / EndpointConstants.endpointK m)| ≤ 1 := by
  have hk := EndpointConstants.endpointK_lower m
  have hk1 : 1 < EndpointConstants.endpointK m := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
  exact (div_le_one (by linarith : 0 < EndpointConstants.endpointK m)).mpr
    ((beta_le_one (ι := ι)).trans hk1.le)

/-- E.12(i) specialized to the actual inverse-defined endpoint constants,
mass `1/(m+2)²`, and coupling `sqrt(beta/k)`, for every `m+2 ≥ 2` layers. -/
theorem paper_component_gradient_lipschitz (m : ℕ)
    {V : Fin ((m + 1) + 1) → Type*}
    [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
    [∀ j, CompleteSpace (V j)]
    (B : ∀ t : Fin (m + 1), BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (i : ι) (x y : Joint V) :
    ‖gradient (component B (EndpointConstants.endpointD m)
        (Real.sqrt (beta ι / EndpointConstants.endpointK m))
        (1 / ((m : ℝ) + 2) ^ 2) i) x -
      gradient (component B (EndpointConstants.endpointD m)
        (Real.sqrt (beta ι / EndpointConstants.endpointK m))
        (1 / ((m : ℝ) + 2) ^ 2) i) y‖ ≤ 8 * ‖x - y‖ := by
  apply component_gradient_lipschitz
  · have hd := EndpointConstants.endpointD_bounds m
    rw [abs_of_nonneg (by linarith : 0 ≤ EndpointConstants.endpointD m)]
    exact hd.2
  · exact endpoint_coupling_le_one m
  · positivity
  · have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    apply (div_le_one (by positivity : 0 < ((m : ℝ) + 2) ^ 2)).mpr
    nlinarith

end PaperParameters
end NCConcave16991.PipeSmoothness
