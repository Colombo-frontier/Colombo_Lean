import MinimaxAudit.Criteria
import Mathlib

/-!
# Affine-hull reduction for the inherited upper bound

This file proves actual normal lifting, convex-concave monotonicity
pairings, scalar-gradient/Riesz derivative-order conversion, and lossless
affine projected-operator jet formulas. It does not introduce an axiom for
the cited VI algorithm or claim an end-to-end solver complexity theorem.
-/
namespace MinimaxAudit

section AffineHull
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (V : Submodule ℝ E) [V.HasOrthogonalProjection]

/-- Embed a relative feasible set in an affine translate of a subspace. -/
def affineFeasibleSet (a : E) (K : Set V) : Set E :=
  (fun u : V => a + (u : E)) '' K

/-- The normal used in `prop:upper`. -/
noncomputable def liftedRelativeNormal (F : E) (nV : V) : E :=
  (nV : E) - (F - V.starProjection F)

/-- An actual relative normal lifts to an ambient normal by cancelling the
orthogonal component of the evaluated operator. -/
theorem lifted_relative_normal_mem {a : E} {K : Set V} {u nV : V} {F : E}
    (hn : nV ∈ normalCone K u) :
    liftedRelativeNormal V F nV ∈
      normalCone (affineFeasibleSet V a K) (a + (u : E)) := by
  rintro z ⟨v, hv, rfl⟩
  change inner ℝ ((nV : E) - (F - V.starProjection F))
    (a + (v : E) - (a + (u : E))) ≤ 0
  have hdisp : a + (v : E) - (a + (u : E)) = ((v - u : V) : E) := by
    simp only [Submodule.coe_sub]
    abel
  rw [hdisp, inner_sub_left,
    V.starProjection_inner_eq_zero F ((v - u : V) : E) (v - u).property, sub_zero]
  simpa only [Submodule.coe_inner] using hn v hv

/-- The ambient residual is exactly the embedded relative residual. -/
theorem lifted_relative_residual_eq (F : E) (nV : V) :
    F + liftedRelativeNormal V F nV =
      ((V.orthogonalProjectionOnto F + nV : V) : E) := by
  simp only [liftedRelativeNormal, Submodule.coe_add,
    Submodule.coe_orthogonalProjectionOnto_apply]
  abel

/-- In particular, certificate lifting preserves its norm exactly. -/
theorem lifted_relative_residual_norm (F : E) (nV : V) :
    ‖F + liftedRelativeNormal V F nV‖ = ‖V.orthogonalProjectionOnto F + nV‖ := by
  rw [lifted_relative_residual_eq]
  rfl

/-- Relative normal membership and the evaluated relative certificate
suffice to obtain the same ambient certificate tolerance. -/
theorem lift_relative_certificate {a : E} {K : Set V} {u nV : V} {F : E}
    {eps : ℝ} (hn : nV ∈ normalCone K u)
    (he : ‖V.orthogonalProjectionOnto F + nV‖ ≤ eps) :
    liftedRelativeNormal V F nV ∈ normalCone (affineFeasibleSet V a K) (a + (u : E)) ∧
      ‖F + liftedRelativeNormal V F nV‖ ≤ eps := by
  exact ⟨lifted_relative_normal_mem V hn, by rwa [lifted_relative_residual_norm]⟩

/-- The projected operator preserves all feasible monotonicity pairings. -/
theorem projected_operator_pairing (F : E → E) (a : E) (u v : V) :
    inner ℝ (V.orthogonalProjectionOnto (F (a + (u : E))) -
      V.orthogonalProjectionOnto (F (a + (v : E)))) (u - v) =
      inner ℝ (F (a + (u : E)) - F (a + (v : E)))
        (a + (u : E) - (a + (v : E))) := by
  rw [← map_sub, V.inner_orthogonalProjectionOnto_eq_of_mem_right]
  congr 1
  simp only [Submodule.coe_sub]
  abel

/-- The relative version of a tensor is obtained by restricting every
input direction and projecting its output. -/
noncomputable def reducedTensor {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => V) V :=
  V.orthogonalProjectionOnto.compContinuousMultilinearMap
    (A.compContinuousLinearMap fun _ => V.subtypeL)

/-- Projection/restriction does not enlarge a derivative tensor's norm. -/
theorem reduced_tensor_norm_le {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E) :
    ‖reducedTensor V A‖ ≤ ‖A‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg A)
  intro m
  change ‖V.orthogonalProjectionOnto (A fun i => ((m i : V) : E))‖ ≤ _
  calc
    _ ≤ ‖A fun i => ((m i : V) : E)‖ := V.norm_orthogonalProjectionOnto_apply_le _
    _ ≤ ‖A‖ * ∏ i, ‖((m i : V) : E)‖ := A.le_opNorm _
    _ = _ := rfl

/-- The same contraction controls differences of derivative tensors. -/
theorem reduced_tensor_difference_norm_le {k : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E) :
    ‖reducedTensor V A - reducedTensor V B‖ ≤ ‖A - B‖ := by
  have heq : reducedTensor V A - reducedTensor V B = reducedTensor V (A - B) := by
    ext m
    simp [reducedTensor, map_sub]
  rw [heq]
  exact reduced_tensor_norm_le V (A - B)

/-- Every operator jet in the relative affine coordinates is computed by
fixed linear operations on one ambient operator jet. This version uses
global `ContDiff`; the neighborhood-local version matching the manuscript
is proved below as `reduced_operator_iteratedFDeriv_on_open`. -/
theorem reduced_operator_iteratedFDeriv {k : ℕ} (F : E → E)
    (hF : ContDiff ℝ k F) (a : E) (u : V) :
    iteratedFDeriv ℝ k (fun v : V => V.orthogonalProjectionOnto (F (a + (v : E)))) u =
      reducedTensor V (iteratedFDeriv ℝ k F (a + (u : E))) := by
  have hshift : ContDiff ℝ k (fun x : E => F (a + x)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have hcomp : ContDiff ℝ k ((fun x : E => F (a + x)) ∘ V.subtypeL) :=
    hshift.comp V.subtypeL.contDiff
  change iteratedFDeriv ℝ k
    (V.orthogonalProjectionOnto ∘ ((fun x : E => F (a + x)) ∘ V.subtypeL)) u = _
  rw [V.orthogonalProjectionOnto.iteratedFDeriv_comp_left hcomp.contDiffAt le_rfl,
    V.subtypeL.iteratedFDeriv_comp_right hshift u le_rfl]
  simp only [iteratedFDeriv_comp_add_left, reducedTensor]
  rfl

/-- An ambient highest-derivative Lipschitz estimate transfers to the
relative affine operator with the same constant. -/
theorem reduced_operator_derivative_lipschitz {k : ℕ} (F : E → E)
    (hF : ContDiff ℝ k F) (a : E) (K : Set V) (L : ℝ)
    (hLip : ∀ x ∈ affineFeasibleSet V a K, ∀ y ∈ affineFeasibleSet V a K,
      ‖iteratedFDeriv ℝ k F x - iteratedFDeriv ℝ k F y‖ ≤ L * ‖x - y‖)
    {u v : V} (hu : u ∈ K) (hv : v ∈ K) :
    ‖iteratedFDeriv ℝ k (fun w : V => V.orthogonalProjectionOnto (F (a + (w : E)))) u -
      iteratedFDeriv ℝ k (fun w : V => V.orthogonalProjectionOnto (F (a + (w : E)))) v‖ ≤
      L * ‖u - v‖ := by
  rw [reduced_operator_iteratedFDeriv V F hF a u,
    reduced_operator_iteratedFDeriv V F hF a v]
  have h := hLip (a + (u : E)) ⟨u, hu, rfl⟩ (a + (v : E)) ⟨v, hv, rfl⟩
  have hdisp : a + (u : E) - (a + (v : E)) = ((u - v : V) : E) := by
    simp only [Submodule.coe_sub]
    abel
  rw [hdisp] at h
  exact le_trans (reduced_tensor_difference_norm_le V _ _) h

/-- Neighborhood-local version of the actual projected jet formula. This
matches the manuscript's open-neighborhood regularity convention. -/
theorem reduced_operator_iteratedFDeriv_on_open {k : ℕ} (F : E → E)
    (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℝ k F U)
    (a : E) (u : V) (hu : a + (u : E) ∈ U) :
    iteratedFDeriv ℝ k (fun v : V => V.orthogonalProjectionOnto (F (a + (v : E)))) u =
      reducedTensor V (iteratedFDeriv ℝ k F (a + (u : E))) := by
  let s : Set E := (fun x : E => a + x) ⁻¹' U
  let t : Set V := V.subtypeL ⁻¹' s
  have hs : IsOpen s := hU.preimage (continuous_const.add continuous_id)
  have ht : IsOpen t := hs.preimage V.subtypeL.continuous
  have hu' : u ∈ t := hu
  have hsu : V.subtypeL u ∈ s := hu
  have hshift : ContDiffOn ℝ k (fun x : E => F (a + x)) s :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hx => hx)
  have hcomp : ContDiffOn ℝ k ((fun x : E => F (a + x)) ∘ V.subtypeL) t :=
    hshift.comp V.subtypeL.contDiff.contDiffOn (fun _ hx => hx)
  have hout := V.orthogonalProjectionOnto.iteratedFDerivWithin_comp_left
    (hcomp u hu') ht.uniqueDiffOn hu' (i := k) le_rfl
  have hin := V.subtypeL.iteratedFDerivWithin_comp_right hshift hs.uniqueDiffOn
    ht.uniqueDiffOn hsu (i := k) le_rfl
  change iteratedFDeriv ℝ k
    (V.orthogonalProjectionOnto ∘ ((fun x : E => F (a + x)) ∘ V.subtypeL)) u = _
  calc
    _ = iteratedFDerivWithin ℝ k
        (V.orthogonalProjectionOnto ∘ ((fun x : E => F (a + x)) ∘ V.subtypeL)) t u :=
      (iteratedFDerivWithin_of_isOpen k ht hu').symm
    _ = V.orthogonalProjectionOnto.compContinuousMultilinearMap
        (iteratedFDerivWithin ℝ k ((fun x : E => F (a + x)) ∘ V.subtypeL) t u) := hout
    _ = V.orthogonalProjectionOnto.compContinuousMultilinearMap
        ((iteratedFDerivWithin ℝ k (fun x : E => F (a + x)) s (V.subtypeL u)).compContinuousLinearMap fun _ => V.subtypeL) := by rw [hin]
    _ = reducedTensor V (iteratedFDeriv ℝ k F (a + (u : E))) := by
      rw [iteratedFDerivWithin_of_isOpen k hs hsu]
      simp only [iteratedFDeriv_comp_add_left, reducedTensor]
      rfl

end AffineHull


section SaddleMonotonicity
variable {P Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]

/-- Convexity and concavity give the manuscript's first-order saddle
comparison inequality, using actual partial gradient derivatives. -/
theorem saddle_first_order_from_convex_concave
    {X : Set P} {Y : Set Q} {phi : P → Q → ℝ}
    {x x' gx : P} {y y' gy : Q}
    (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∈ Y) (hy' : y' ∈ Y)
    (hcx : ConvexOn ℝ X (fun u => phi u y))
    (hcy : ConcaveOn ℝ Y (fun v => phi x v))
    (hdx : HasGradientAt (fun u => phi u y) gx x)
    (hdy : HasGradientAt (fun v => phi x v) gy y) :
    phi x y' - phi x' y ≤
      inner ℝ gx (x - x') + inner ℝ (-gy) (y - y') := by
  have h1 := convex_first_order hcx hx hx' hdx.hasFDerivAt
  have h2 := convex_first_order hcy.neg hy hy' hdy.hasFDerivAt.neg
  simp only [neg_apply, Pi.neg_apply, InnerProductSpace.toDual_apply_apply] at h1 h2
  have hxx : inner ℝ gx (x - x') = -inner ℝ gx (x' - x) := by
    rw [show x - x' = -(x' - x) by abel, inner_neg_right]
  have hyy : inner ℝ (-gy) (y - y') = inner ℝ gy (y' - y) := by
    rw [show y - y' = -(y' - y) by abel, inner_neg_left, inner_neg_right, neg_neg]
  rw [hxx, hyy]
  linarith

/-- The real saddle-gradient monotonicity pairing, proved directly from
convex/concave slices and their actual gradients at the two points. -/
theorem convex_concave_gradient_monotonicity
    {X : Set P} {Y : Set Q} {phi : P → Q → ℝ}
    {x x' gx gx' : P} {y y' gy gy' : Q}
    (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∈ Y) (hy' : y' ∈ Y)
    (hcx : ∀ v ∈ Y, ConvexOn ℝ X (fun u => phi u v))
    (hcy : ∀ u ∈ X, ConcaveOn ℝ Y (fun v => phi u v))
    (hdx : HasGradientAt (fun u => phi u y) gx x)
    (hdy : HasGradientAt (fun v => phi x v) gy y)
    (hdx' : HasGradientAt (fun u => phi u y') gx' x')
    (hdy' : HasGradientAt (fun v => phi x' v) gy' y') :
    0 ≤ inner ℝ (gx - gx') (x - x') + inner ℝ ((-gy) - (-gy')) (y - y') := by
  have h1 := saddle_first_order_from_convex_concave hx hx' hy hy'
    (hcx y hy) (hcy x hx) hdx hdy
  have h2 := saddle_first_order_from_convex_concave hx' hx hy' hy
    (hcx y' hy') (hcy x' hx') hdx' hdy'
  have hxx : inner ℝ gx' (x' - x) = -inner ℝ gx' (x - x') := by
    rw [show x' - x = -(x - x') by abel, inner_neg_right]
  have hyy : inner ℝ (-gy') (y' - y) = -inner ℝ (-gy') (y - y') := by
    rw [show y' - y = -(y - y') by abel, inner_neg_right]
  rw [hxx, hyy] at h2
  simp only [inner_sub_left]
  linarith

end SaddleMonotonicity

/-- The actual Euclidean saddle signature: primal coordinates are fixed,
dual coordinates are negated. The sum index uses the product Euclidean
metric, rather than the max metric on an ordinary Lean product. -/
noncomputable def euclideanSaddleSign (dx dy : ℕ) :
    EuclideanSpace ℝ (Fin dx ⊕ Fin dy) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin dx ⊕ Fin dy) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i =>
    match i with
    | Sum.inl _ => LinearIsometryEquiv.refl ℝ ℝ
    | Sum.inr _ => LinearIsometryEquiv.neg ℝ)

theorem euclidean_saddle_sign_primal (dx dy : ℕ)
    (z : EuclideanSpace ℝ (Fin dx ⊕ Fin dy)) (i : Fin dx) :
    euclideanSaddleSign dx dy z (Sum.inl i) = z (Sum.inl i) := by rfl

theorem euclidean_saddle_sign_dual (dx dy : ℕ)
    (z : EuclideanSpace ℝ (Fin dx ⊕ Fin dy)) (i : Fin dy) :
    euclideanSaddleSign dx dy z (Sum.inr i) = -z (Sum.inr i) := by rfl

theorem euclidean_saddle_sign_norm (dx dy : ℕ)
    (z : EuclideanSpace ℝ (Fin dx ⊕ Fin dy)) :
    ‖euclideanSaddleSign dx dy z‖ = ‖z‖ := (euclideanSaddleSign dx dy).norm_map z

section ScalarJets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz identification and a fixed saddle-sign isometry convert a
scalar `(k+1)`-tensor into the corresponding vector-valued `k`-tensor. -/
noncomputable def scalarToSaddleTensor (S : E ≃ₗᵢ[ℝ] E) {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E :=
  S.toLinearIsometry.toContinuousLinearMap.compContinuousMultilinearMap
    ((InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap.compContinuousMultilinearMap ((continuousMultilinearCurryRightEquiv' ℝ k E ℝ) A))

/-- The scalar-to-saddle tensor conversion preserves the operator norm. -/
theorem scalar_to_saddle_tensor_norm (S : E ≃ₗᵢ[ℝ] E) {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ) :
    ‖scalarToSaddleTensor S A‖ = ‖A‖ := by
  unfold scalarToSaddleTensor
  rw [S.toLinearIsometry.norm_compContinuousMultilinearMap,
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.norm_compContinuousMultilinearMap,
    LinearIsometryEquiv.norm_map]

/-- In particular, highest-derivative difference norms are preserved. -/
theorem scalar_to_saddle_tensor_difference_norm (S : E ≃ₗᵢ[ℝ] E) {k : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ) :
    ‖scalarToSaddleTensor S A - scalarToSaddleTensor S B‖ = ‖A - B‖ := by
  have heq : scalarToSaddleTensor S A - scalarToSaddleTensor S B =
      scalarToSaddleTensor S (A - B) := by
    have hcur := (continuousMultilinearCurryRightEquiv' ℝ k E ℝ).map_sub A B
    ext m
    change S ((InnerProductSpace.toDual ℝ E).symm
        (((continuousMultilinearCurryRightEquiv' ℝ k E ℝ) A) m)) -
      S ((InnerProductSpace.toDual ℝ E).symm
        (((continuousMultilinearCurryRightEquiv' ℝ k E ℝ) B) m)) =
      S ((InnerProductSpace.toDual ℝ E).symm
        (((continuousMultilinearCurryRightEquiv' ℝ k E ℝ) (A - B)) m))
    rw [hcur, sub_apply, map_sub, map_sub]
  rw [heq, scalar_to_saddle_tensor_norm]

/-- A genuine scalar jet determines the genuine saddle-operator jet;
the derivative order drops by one under the gradient/Riesz conversion.
This identity does not need an extra smoothness axiom. -/
theorem scalar_jet_to_saddle_jet (S : E ≃ₗᵢ[ℝ] E) (f : E → ℝ) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (S ∘ gradient f) x =
      scalarToSaddleTensor S (iteratedFDeriv ℝ (k + 1) f x) := by
  change iteratedFDeriv ℝ k (S.toContinuousLinearEquiv ∘ gradient f) x = _
  rw [S.toContinuousLinearEquiv.iteratedFDeriv_comp_left]
  change S.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
    (iteratedFDeriv ℝ k ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv ∘ fderiv ℝ f) x) = _
  rw [(InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.iteratedFDeriv_comp_left]
  have hd : iteratedFDeriv ℝ k (fderiv ℝ f) x =
      (continuousMultilinearCurryRightEquiv' ℝ k E ℝ) (iteratedFDeriv ℝ (k + 1) f x) := by
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [hd]
  rfl

/-- The highest-order scalar modulus transfers with exactly the same
constant, before affine projection is applied. -/
theorem scalar_saddle_highest_derivative_lipschitz (S : E ≃ₗᵢ[ℝ] E)
    (f : E → ℝ) (k : ℕ) (Z : Set E) (L : ℝ)
    (hLip : ∀ x ∈ Z, ∀ y ∈ Z,
      ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) f y‖ ≤ L * ‖x - y‖)
    {x y : E} (hx : x ∈ Z) (hy : y ∈ Z) :
    ‖iteratedFDeriv ℝ k (S ∘ gradient f) x -
      iteratedFDeriv ℝ k (S ∘ gradient f) y‖ ≤ L * ‖x - y‖ := by
  rw [scalar_jet_to_saddle_jet S f k x, scalar_jet_to_saddle_jet S f k y,
    scalar_to_saddle_tensor_difference_norm]
  exact hLip x hx y hy

/-- The complete scalar jet at one feasible point supplies the complete
relative operator jet, using exactly the paper's neighborhood regularity. -/
theorem scalar_affine_jet_reduction (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (S : E ≃ₗᵢ[ℝ] E) (f : E → ℝ) (k : ℕ) (U : Set E)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U)
    (a : E) (u : V) (hu : a + (u : E) ∈ U) :
    iteratedFDeriv ℝ k
      (fun v : V => V.orthogonalProjectionOnto (S (gradient f (a + (v : E))))) u =
      reducedTensor V (scalarToSaddleTensor S (iteratedFDeriv ℝ (k + 1) f (a + (u : E)))) := by
  have hD : ContDiffOn ℝ k (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hgrad : ContDiffOn ℝ k (gradient f) U :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hD
  have hOp : ContDiffOn ℝ k (S ∘ gradient f) U :=
    S.toContinuousLinearEquiv.contDiff.comp_contDiffOn hgrad
  change iteratedFDeriv ℝ k
    (fun v : V => V.orthogonalProjectionOnto ((S ∘ gradient f) (a + (v : E)))) u = _
  rw [reduced_operator_iteratedFDeriv_on_open V (S ∘ gradient f) U hU hOp a u hu,
    scalar_jet_to_saddle_jet S f k (a + (u : E))]

/-- The same scalar jet conversion and affine projection preserve the
highest derivative modulus on every feasible relative domain. -/
theorem scalar_affine_highest_derivative_lipschitz
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] (S : E ≃ₗᵢ[ℝ] E)
    (f : E → ℝ) (k : ℕ) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ (k + 1) f U) (a : E) (K : Set V) (L : ℝ)
    (hKU : ∀ u ∈ K, a + (u : E) ∈ U)
    (hLip : ∀ x ∈ affineFeasibleSet V a K, ∀ y ∈ affineFeasibleSet V a K,
      ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) f y‖ ≤ L * ‖x - y‖)
    {u v : V} (hu : u ∈ K) (hv : v ∈ K) :
    ‖iteratedFDeriv ℝ k
        (fun w : V => V.orthogonalProjectionOnto (S (gradient f (a + (w : E))))) u -
      iteratedFDeriv ℝ k
        (fun w : V => V.orthogonalProjectionOnto (S (gradient f (a + (w : E))))) v‖ ≤
      L * ‖u - v‖ := by
  rw [scalar_affine_jet_reduction V S f k U hU hf a u (hKU u hu),
    scalar_affine_jet_reduction V S f k U hU hf a v (hKU v hv)]
  have h := hLip (a + (u : E)) ⟨u, hu, rfl⟩ (a + (v : E)) ⟨v, hv, rfl⟩
  have hdisp : a + (u : E) - (a + (v : E)) = ((u - v : V) : E) := by
    simp only [Submodule.coe_sub]
    abel
  rw [hdisp] at h
  exact le_trans ((reduced_tensor_difference_norm_le V _ _).trans_eq
    (scalar_to_saddle_tensor_difference_norm S _ _)) h

end ScalarJets
end MinimaxAudit
