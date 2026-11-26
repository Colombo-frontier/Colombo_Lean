import Bilevel.TransportObserverFreshProjection
import Bilevel.SphereHaar
import Mathlib.MeasureTheory.Group.Integral

/-! Actual Haar projection moments on a finite-dimensional residual space.
The embedding can be into a larger ambient space. No posterior or transcript
invariance is claimed: a protocol must separately identify its residual law
with this Haar law. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open ProjectionGeometry EuclideanGaussian OrthogonalAction

theorem haar_orbit_integral_eq (d : ℕ) (f : Space d → ℝ) (x y : Space d)
    (hxy : ‖x‖ = ‖y‖) :
    (∫ A, f (A • y) ∂OrthogonalHaar.law d) =
      ∫ A, f (A • x) ∂OrthogonalHaar.law d := by
  obtain ⟨B,rfl⟩ := transitive_on_sphere d x y hxy
  simp_rw [← mul_smul]
  exact integral_mul_right_eq_self (fun A : OrthogonalHaar.Group d => f (A • x)) B

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem haar_inner_integrable (d : ℕ) (J : Space d →ₗᵢ[ℝ] E) (w : E) (x : Space d) :
    Integrable (fun A : OrthogonalHaar.Group d => ⟪w,J (A • x)⟫^2)
      (OrthogonalHaar.law d) := by
  have hc : Continuous (fun A : OrthogonalHaar.Group d => ⟪w,J (A • x)⟫^2) :=
    (continuous_const.inner (J.continuous.comp
      ((action_continuous d).comp (continuous_id.prodMk continuous_const)))).pow 2
  apply (integrable_const ((‖w‖*‖x‖)^2)).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro A
  have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm w (J (A • x))) 2
  simpa only [Real.norm_eq_abs,abs_pow,sq_abs,J.norm_map,
    action_apply,LinearIsometryEquiv.norm_map] using hh

/-- A unit vector rotated by genuine Haar measure has directional second
moment at most `‖w‖² / d` after any isometric residual-space embedding. -/
theorem haar_inner_moment_le (d : ℕ) (hd : 0 < d) (J : Space d →ₗᵢ[ℝ] E)
    (w : E) (x : Space d) (hx : ‖x‖ = 1) :
    (∫ A : OrthogonalHaar.Group d, ⟪w,J (A • x)⟫^2 ∂OrthogonalHaar.law d) ≤
      ‖w‖^2/(d:ℝ) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hi (i : Fin d) := haar_inner_integrable d J w (b i)
  have he (i : Fin d) :
      (∫ A : OrthogonalHaar.Group d, ⟪w,J (A • b i)⟫^2 ∂OrthogonalHaar.law d) =
        ∫ A : OrthogonalHaar.Group d, ⟪w,J (A • x)⟫^2 ∂OrthogonalHaar.law d :=
    haar_orbit_integral_eq d (fun y => ⟪w,J y⟫^2) x (b i)
      (hx.trans (b.orthonormal.norm_eq_one i).symm)
  have hs (A : OrthogonalHaar.Group d) : ∑ i, ⟪w,J (A • b i)⟫^2 ≤ ‖w‖^2 := by
    have ho := (b.orthonormal.comp_linearIsometryEquiv (isometry d A)).comp_linearIsometry J
    simpa only [Function.comp_apply,Real.norm_eq_abs,sq_abs,real_inner_comm,
      action_apply] using (ho.sum_inner_products_le (s := Finset.univ) w)
  have hb := integral_mono (integrable_finset_sum _ (fun i _ => hi i))
    (integrable_const (‖w‖^2)) hs
  rw [integral_finset_sum _ (fun i _ => hi i)] at hb
  simp_rw [he] at hb
  have hb' : (d:ℝ)*
      (∫ A : OrthogonalHaar.Group d, ⟪w,J (A • x)⟫^2 ∂OrthogonalHaar.law d) ≤ ‖w‖^2 := by
    simpa using hb
  apply (le_div_iff₀ (by exact_mod_cast hd : (0:ℝ) < d)).mpr
  simpa only [mul_comm] using hb'

variable [FiniteDimensional ℝ E]

theorem projection_energy_parseval {ι : Type*} [Fintype ι]
    (W : Submodule ℝ E) (b : OrthonormalBasis ι ℝ W) (z : E) :
    energy W z = ∑ i, ⟪(b i : E),z⟫^2 := by
  have hh := b.sum_sq_norm_inner (W.orthogonalProjection z)
  simpa only [energy,project,Submodule.inner_orthogonalProjection_eq_of_mem_left,
    Real.norm_eq_abs,sq_abs] using hh.symm

theorem haar_projection_integrable {ι : Type*} [Fintype ι]
    (d : ℕ) (J : Space d →ₗᵢ[ℝ] E) (W : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ W) (x : Space d) :
    Integrable (fun A : OrthogonalHaar.Group d => energy W (J (A • x)))
      (OrthogonalHaar.law d) := by
  simp_rw [projection_energy_parseval W b]
  exact integrable_finset_sum _ (fun i _ => haar_inner_integrable d J (b i : E) x)

/-- The residual Haar projection moment is at most destination rank divided
by residual dimension. It is valid for an ambient subspace W that is not
contained in the image of the residual-space embedding J. -/
theorem haar_projection_moment_le {ι : Type*} [Fintype ι]
    (d : ℕ) (hd : 0 < d) (J : Space d →ₗᵢ[ℝ] E) (W : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ W) (x : Space d) (hx : ‖x‖ = 1) :
    (∫ A : OrthogonalHaar.Group d, energy W (J (A • x)) ∂OrthogonalHaar.law d) ≤
      (Fintype.card ι : ℝ)/(d:ℝ) := by
  simp_rw [projection_energy_parseval W b]
  rw [integral_finset_sum _ (fun i _ => haar_inner_integrable d J (b i : E) x)]
  calc
    _ ≤ ∑ _i : ι, (1:ℝ)/(d:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := haar_inner_moment_le d hd J (b i : E) x hx
      have hn : ‖(b i : E)‖ = 1 := b.orthonormal.norm_eq_one i
      simpa only [hn,one_pow] using hh
    _ = _ := by simp [div_eq_mul_inv]

theorem haar_frame_integrable {ι κ : Type*} [Fintype ι]
    (d : ℕ) (J : Space d →ₗᵢ[ℝ] E) (W : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ W) (v : κ → Space d) (I : Finset κ) :
    Integrable (fun A : OrthogonalHaar.Group d =>
      frameEnergy W (fun i => J (A • v i)) I) (OrthogonalHaar.law d) := by
  exact integrable_finset_sum _ (fun i _ => haar_projection_integrable d J W b (v i))

/-- All columns are transformed by the SAME Haar action. Linearity of
expectation, rather than independence of the columns, gives the r*rank/d
Frobenius bound required for the fresh complementary block. -/
theorem haar_frame_moment_le {ι κ : Type*} [Fintype ι]
    (d : ℕ) (hd : 0 < d) (J : Space d →ₗᵢ[ℝ] E) (W : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ W) (v : κ → Space d) (I : Finset κ)
    (hv : ∀ i ∈ I, ‖v i‖ = 1) :
    (∫ A : OrthogonalHaar.Group d, frameEnergy W (fun i => J (A • v i)) I
      ∂OrthogonalHaar.law d) ≤ (I.card : ℝ)*Fintype.card ι/(d:ℝ) := by
  unfold frameEnergy
  rw [integral_finset_sum _ (fun i _ => haar_projection_integrable d J W b (v i))]
  calc
    _ ≤ ∑ _i ∈ I, (Fintype.card ι : ℝ)/(d:ℝ) :=
      Finset.sum_le_sum (fun i hi => haar_projection_moment_le d hd J W b (v i) (hv i hi))
    _ = _ := by simp [div_eq_mul_inv,mul_assoc]

theorem haar_frame_projection_failure {ι κ : Type*} [Fintype ι]
    (d : ℕ) (hd : 0 < d) (J : Space d →ₗᵢ[ℝ] E) (W : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ W) (v : κ → Space d) (I : Finset κ)
    (hv : ∀ i ∈ I, ‖v i‖ = 1) :
    (OrthogonalHaar.law d).real
      {A | (1:ℝ)/64 < frameEnergy W (fun i => J (A • v i)) I} ≤
      64*((I.card : ℝ)*Fintype.card ι/(d:ℝ)) :=
  fresh_projection_failure_of_moment _ _
    (fun A => frameEnergy_nonneg W (fun i => J (A • v i)) I)
    (haar_frame_integrable d J W b v I)
    (haar_frame_moment_le d hd J W b v I hv)

end Bilevel.TransportObserver
