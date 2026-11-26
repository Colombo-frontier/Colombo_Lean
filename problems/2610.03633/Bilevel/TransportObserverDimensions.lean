import Bilevel.TransportObserverHaarAngle
import Bilevel.TransportObserverQueryInsertion

/-! Canonical-basis and dimension-cap forms of the two separate observer
moment bounds. No additional distributional assumption is introduced. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open EuclideanGaussian ProjectionGeometry

theorem residual_dimension_real (D : ℕ) (V : Submodule ℝ (Space D)) :
    (Module.finrank ℝ Vᗮ : ℝ) = (D:ℝ)-(Module.finrank ℝ V : ℝ) := by
  have hh : Module.finrank ℝ V+Module.finrank ℝ Vᗮ = D := by
    simpa [Space] using V.finrank_add_finrank_orthogonal
  have hh' : (Module.finrank ℝ V : ℝ)+(Module.finrank ℝ Vᗮ : ℝ) = D := by exact_mod_cast hh
  linarith

theorem query_insertion_failure_dimension (D T d : ℕ)
    (V : Submodule ℝ (Space D)) (hV : Module.finrank ℝ V ≤ d) (hd : d < D)
    (μ : Measure (ProjectionPosterior.Frame D T)) [IsProbabilityMeasure μ]
    (hμ : ProjectionPosterior.Invariant D T V μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1)
    (q : Space D) (hqV : q ∈ Vᗮ) (hq : ‖q‖ = 1) (a : ℝ) (ha : 0 < a) :
    μ.real {U | a < frameEnergy (V ⊔ Submodule.span ℝ {q}) U Finset.univ-
      frameEnergy V U Finset.univ} ≤ (T:ℝ)/(((D:ℝ)-d)*a) := by
  have hD : (0:ℝ) < (D:ℝ)-d := by
    have hh : (d:ℝ) < D := by exact_mod_cast hd
    linarith
  have hvr : (Module.finrank ℝ V : ℝ) ≤ d := by exact_mod_cast hV
  have hr : (D:ℝ)-d ≤ (Module.finrank ℝ Vᗮ : ℝ) := by
    rw [residual_dimension_real]
    linarith
  have hres : 0 < Module.finrank ℝ Vᗮ := by
    have hh : (0:ℝ) < (Module.finrank ℝ Vᗮ : ℝ) := hD.trans_le hr
    exact_mod_cast hh
  have hh := invariant_query_insertion_failure D T V (stdOrthonormalBasis ℝ Vᗮ)
    (by simpa only [Fintype.card_fin] using hres) μ hμ hnorm q hqV hq a ha
  simp only [Fintype.card_fin] at hh
  exact hh.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg T) (mul_pos hD ha)
    (mul_le_mul_of_nonneg_right hr ha.le))

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G]

theorem haar_fresh_operator_failure_dimension (r d : ℕ) (hr : 0 < r)
    (J : Space r →ₗᵢ[ℝ] E) (W : Submodule ℝ E)
    (hW : Module.finrank ℝ W ≤ d) (R : Submodule ℝ (Space r))
    (hR : Module.finrank ℝ R ≤ d) (fresh : G → R) (hnorm : ∀ u, ‖fresh u‖ ≤ ‖u‖) :
    (OrthogonalHaar.law r).real
      {A | ∃ u, ‖u‖/8 < ‖project W (J (A • (fresh u : Space r)))‖} ≤
      64*(d:ℝ)^2/(r:ℝ) := by
  have hh := haar_fresh_operator_failure r hr J W (stdOrthonormalBasis ℝ W) R
    (stdOrthonormalBasis ℝ R) fresh hnorm
  simp only [Fintype.card_fin] at hh
  have hW' : (Module.finrank ℝ W : ℝ) ≤ d := by exact_mod_cast hW
  have hR' : (Module.finrank ℝ R : ℝ) ≤ d := by exact_mod_cast hR
  have hb : (Module.finrank ℝ R : ℝ)*(Module.finrank ℝ W : ℝ) ≤ (d:ℝ)^2 := by
    simpa only [pow_two] using mul_le_mul hR' hW' (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hm := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hb (Nat.cast_nonneg r)) (by norm_num : (0:ℝ) ≤ 64)
  exact hh.trans (by simpa only [mul_div_assoc] using hm)

theorem haar_fresh_operator_failure_source_dimension (D T d r : ℕ)
    (hD : T+d < D) (hres : (D:ℝ)-T-d ≤ r)
    (J : Space r →ₗᵢ[ℝ] E) (W : Submodule ℝ E)
    (hW : Module.finrank ℝ W ≤ d) (R : Submodule ℝ (Space r))
    (hR : Module.finrank ℝ R ≤ d) (fresh : G → R) (hnorm : ∀ u, ‖fresh u‖ ≤ ‖u‖) :
    (OrthogonalHaar.law r).real
      {A | ∃ u, ‖u‖/8 < ‖project W (J (A • (fresh u : Space r)))‖} ≤
      64*(d:ℝ)^2/((D:ℝ)-T-d) := by
  have hden : (0:ℝ) < (D:ℝ)-T-d := by
    have hh : (T:ℝ)+d < D := by exact_mod_cast hD
    linarith
  have hr : 0 < r := by
    have hh : (0:ℝ) < r := hden.trans_le hres
    exact_mod_cast hh
  exact (haar_fresh_operator_failure_dimension r d hr J W hW R hR fresh hnorm).trans
    (div_le_div_of_nonneg_left (by positivity) hden hres)

end Bilevel.TransportObserver
