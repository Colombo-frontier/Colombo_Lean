import GradientHessian.GaussianMatrixFiniteComparison
import GradientHessian.GaussianNetExtrema
import GradientHessian.GaussianNetVectorBounds

/-! Passing the proved finite matrix comparisons to the entire compact
spheres. Hypotheses identify linear projections of the actual latent
Gaussian vector; no comparison or singular-value estimate is a premise. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter
open scoped InnerProductSpace Topology

variable {a b : ℕ} [NeZero a] [NeZero b]

variable (T : (MatrixComparisonSpace a b) →L[ℝ] ((EuclideanSpace ℝ (Fin b)) →L[ℝ] (EuclideanSpace ℝ (Fin a)))) (g : (MatrixComparisonSpace a b) →L[ℝ] (EuclideanSpace ℝ (Fin a))) (h : (MatrixComparisonSpace a b) →L[ℝ] (EuclideanSpace ℝ (Fin b))) (ζ : (MatrixComparisonSpace a b) →L[ℝ] ℝ)
variable (hX : ∀ (u : (EuclideanSpace ℝ (Fin b))) (v : (EuclideanSpace ℝ (Fin a))) (z : (MatrixComparisonSpace a b)),
  ⟪matrixComparisonX u v,z⟫_ℝ = ⟪v,T z u⟫_ℝ + ζ z)
variable (hY : ∀ (u : (EuclideanSpace ℝ (Fin b))) (v : (EuclideanSpace ℝ (Fin a))) (z : (MatrixComparisonSpace a b)),
  ⟪matrixComparisonY u v,z⟫_ℝ = ⟪v,g z⟫_ℝ + ⟪u,h z⟫_ℝ)
variable (hζ : (∫ z, ζ z ∂euclideanGaussianLaw (MatrixComparisonSpace a b))=0)

include hX hY hζ in
omit [NeZero a] in
theorem gaussian_net_largest_mean {ε : ℝ} (U : UnitSphereNet (EuclideanSpace ℝ (Fin b)) ε) (V : UnitSphereNet (EuclideanSpace ℝ (Fin a)) ε) :
    (∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) - 2*ε*(∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ (∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) + ∫ z, ‖h z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b) := by
  classical
  let X : (MatrixComparisonSpace a b) → ℝ := fun z => finiteMaximum
    (fun p : U.Index × V.Index => ⟪matrixComparisonX (p.1 : (EuclideanSpace ℝ (Fin b))) (p.2 : (EuclideanSpace ℝ (Fin a))),z⟫_ℝ)
  let Y : (MatrixComparisonSpace a b) → ℝ := fun z => finiteMaximum
    (fun p : U.Index × V.Index => ⟪matrixComparisonY (p.1 : (EuclideanSpace ℝ (Fin b))) (p.2 : (EuclideanSpace ℝ (Fin a))),z⟫_ℝ)
  have ix : Integrable X (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (finiteMaximum_lipschitz.comp
    (gaussianArrayMap (MatrixComparisonSpace a b) (fun p : U.Index × V.Index => matrixComparisonX (p.1 : (EuclideanSpace ℝ (Fin b))) (p.2 : (EuclideanSpace ℝ (Fin a))))).lipschitz)
  have iy : Integrable Y (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (finiteMaximum_lipschitz.comp
    (gaussianArrayMap (MatrixComparisonSpace a b) (fun p : U.Index × V.Index => matrixComparisonY (p.1 : (EuclideanSpace ℝ (Fin b))) (p.2 : (EuclideanSpace ℝ (Fin a))))).lipschitz)
  have iT : Integrable (fun z => ‖T z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (lipschitzWith_one_norm.comp T.lipschitz)
  have ig : Integrable (fun z => ‖g z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (lipschitzWith_one_norm.comp g.lipschitz)
  have ih : Integrable (fun z => ‖h z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (lipschitzWith_one_norm.comp h.lipschitz)
  have iz : Integrable (fun z => ζ z) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable ζ.lipschitz
  have hlo : (∫ z, ‖T z‖ - 2*ε*‖T z‖ + ζ z ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ ∫ z, X z ∂euclideanGaussianLaw (MatrixComparisonSpace a b) := by
    apply integral_mono ((iT.sub (iT.const_mul (2*ε))).add iz) ix
    intro z
    have he : X z = finiteMaximum (netBilinear U V (T z)) + ζ z := by
      dsimp only [X]
      simp_rw [hX]
      exact finiteMaximum_add_const (netBilinear U V (T z)) (ζ z)
    rw [he]
    exact add_le_add_right (net_largestExpansion_bounds U V (T z)).1 _
  have hhi : (∫ z, Y z ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ ∫ z, ‖g z‖+‖h z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b) := by
    apply integral_mono iy (ig.add ih)
    intro z
    have he : Y z = finiteMaximum (netVectorSum U V (g z) (h z)) := by dsimp only [Y]; simp_rw [hY]; rfl
    rw [he]
    exact netVector_maximum U V (g z) (h z)
  have hcomp : (∫ z, X z ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ ∫ z, Y z ∂euclideanGaussianLaw (MatrixComparisonSpace a b) :=
    matrix_finiteMaximum_comparison (fun i : U.Index => (i : (EuclideanSpace ℝ (Fin b)))) (fun j : V.Index => (j : (EuclideanSpace ℝ (Fin a))))
      U.index_unit V.index_unit
  have hall := hlo.trans (hcomp.trans hhi)
  have ilow : Integrable (fun z => ‖T z‖ - 2*ε*‖T z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) :=
    iT.sub (iT.const_mul (2*ε))
  rw [integral_add ilow iz,integral_sub iT (iT.const_mul (2*ε)),
    integral_const_mul,hζ,add_zero,integral_add ig ih] at hall
  exact hall

include hX hY hζ in
omit [NeZero a] in
theorem gaussian_net_least_mean {ε : ℝ} (U : UnitSphereNet (EuclideanSpace ℝ (Fin b)) ε) (V : UnitSphereNet (EuclideanSpace ℝ (Fin a)) ε) :
    (∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) - (∫ z, ‖h z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) - ε*(∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤
      (∫ z, leastExpansion (T z) ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) + ε*(∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) := by
  classical
  let X : (MatrixComparisonSpace a b) → ℝ := fun z => finiteMinMax
    (fun p : U.Index × V.Index => ⟪matrixComparisonX (p.1 : (EuclideanSpace ℝ (Fin b))) (p.2 : (EuclideanSpace ℝ (Fin a))),z⟫_ℝ)
  let Y : (MatrixComparisonSpace a b) → ℝ := fun z => finiteMinMax
    (fun p : U.Index × V.Index => ⟪matrixComparisonY (p.1 : (EuclideanSpace ℝ (Fin b))) (p.2 : (EuclideanSpace ℝ (Fin a))),z⟫_ℝ)
  have ix : Integrable X (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (finiteMinMax_lipschitz.comp
    (gaussianArrayMap (MatrixComparisonSpace a b) (fun p : U.Index × V.Index => matrixComparisonX (p.1 : (EuclideanSpace ℝ (Fin b))) (p.2 : (EuclideanSpace ℝ (Fin a))))).lipschitz)
  have iy : Integrable Y (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (finiteMinMax_lipschitz.comp
    (gaussianArrayMap (MatrixComparisonSpace a b) (fun p : U.Index × V.Index => matrixComparisonY (p.1 : (EuclideanSpace ℝ (Fin b))) (p.2 : (EuclideanSpace ℝ (Fin a))))).lipschitz)
  have iT : Integrable (fun z => ‖T z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (lipschitzWith_one_norm.comp T.lipschitz)
  have im : Integrable (fun z => leastExpansion (T z)) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (leastExpansion_lipschitz.comp T.lipschitz)
  have ig : Integrable (fun z => ‖g z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (lipschitzWith_one_norm.comp g.lipschitz)
  have ih : Integrable (fun z => ‖h z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable (lipschitzWith_one_norm.comp h.lipschitz)
  have iz : Integrable (fun z => ζ z) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := lipschitz_integrable ζ.lipschitz
  have hlo : (∫ z, ‖g z‖-‖h z‖-ε*‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ ∫ z, Y z ∂euclideanGaussianLaw (MatrixComparisonSpace a b) := by
    apply integral_mono ((ig.sub ih).sub (ig.const_mul ε)) iy
    intro z
    have he : Y z = finiteMinMax (netVectorSum U V (g z) (h z)) := by dsimp only [Y]; simp_rw [hY]; rfl
    rw [he]
    exact netVector_minimum U V (g z) (h z)
  have hhi : (∫ z, X z ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ ∫ z, leastExpansion (T z)+ε*‖T z‖+ζ z ∂euclideanGaussianLaw (MatrixComparisonSpace a b) := by
    apply integral_mono ix ((im.add (iT.const_mul ε)).add iz)
    intro z
    have he : X z = finiteMinMax (netBilinear U V (T z)) + ζ z := by
      dsimp only [X]
      simp_rw [hX]
      exact finiteMinMax_add_const (netBilinear U V (T z)) (ζ z)
    rw [he]
    exact add_le_add_right (net_leastExpansion_bounds U V (T z)).2 _
  have hcomp : (∫ z, Y z ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ ∫ z, X z ∂euclideanGaussianLaw (MatrixComparisonSpace a b) :=
    matrix_finiteMinMax_comparison (fun i : U.Index => (i : (EuclideanSpace ℝ (Fin b)))) (fun j : V.Index => (j : (EuclideanSpace ℝ (Fin a))))
      U.index_unit V.index_unit
  have hall := hlo.trans (hcomp.trans hhi)
  have ilow : Integrable (fun z => ‖g z‖ - ‖h z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) := ig.sub ih
  have iup : Integrable (fun z => leastExpansion (T z)+ε*‖T z‖) (euclideanGaussianLaw (MatrixComparisonSpace a b)) :=
    im.add (iT.const_mul ε)
  rw [integral_sub ilow (ig.const_mul ε),integral_sub ig ih,integral_const_mul,
    integral_add iup iz,integral_add im (iT.const_mul ε),integral_const_mul,
    hζ,add_zero] at hall
  exact hall

include hX hY hζ in
theorem gaussian_sphere_mean_comparison :
    (∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ (∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) + (∫ z, ‖h z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ∧
      (∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) - (∫ z, ‖h z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤ ∫ z, leastExpansion (T z) ∂euclideanGaussianLaw (MatrixComparisonSpace a b) := by
  have hn (n : ℕ) := exists_unitSphereNet (EuclideanSpace ℝ (Fin b)) (by positivity : (0 : ℝ) < 1/((n:ℝ)+1))
  have hm (n : ℕ) := exists_unitSphereNet (EuclideanSpace ℝ (Fin a)) (by positivity : (0 : ℝ) < 1/((n:ℝ)+1))
  let U (n : ℕ) : UnitSphereNet (EuclideanSpace ℝ (Fin b)) (1/((n:ℝ)+1)) := Classical.choice (hn n)
  let V (n : ℕ) : UnitSphereNet (EuclideanSpace ℝ (Fin a)) (1/((n:ℝ)+1)) := Classical.choice (hm n)
  constructor
  · have hineq (n : ℕ) := gaussian_net_largest_mean T g h ζ hX hY hζ (U n) (V n)
    have ht : Tendsto (fun n : ℕ => (∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) -
        2*(1/((n:ℝ)+1))*(∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b))) atTop (𝓝 (∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b))) := by
      simpa only [mul_zero,zero_mul,sub_zero] using tendsto_const_nhds.sub
        ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2).mul_const (∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)))
    exact le_of_tendsto ht (Filter.Eventually.of_forall hineq)
  · have hineq (n : ℕ) : (∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) - (∫ z, ‖h z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤
        (∫ z, leastExpansion (T z) ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) +
          (1/((n:ℝ)+1))*((∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b))+(∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b))) := by
      have hh := gaussian_net_least_mean T g h ζ hX hY hζ (U n) (V n)
      linarith
    have ht : Tendsto (fun n : ℕ => (∫ z, leastExpansion (T z) ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) +
        (1/((n:ℝ)+1))*((∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b))+(∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)))) atTop
        (𝓝 (∫ z, leastExpansion (T z) ∂euclideanGaussianLaw (MatrixComparisonSpace a b))) := by
      simpa only [zero_mul,add_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const
          ((∫ z, ‖g z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b))+(∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)))).const_add (∫ z, leastExpansion (T z) ∂euclideanGaussianLaw (MatrixComparisonSpace a b))
    exact ge_of_tendsto ht (Filter.Eventually.of_forall hineq)

end GradientHessian.GaussianConcentration
