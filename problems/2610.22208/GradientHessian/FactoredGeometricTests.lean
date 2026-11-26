import GradientHessian.FactoredTests
import GradientHessian.SphereSmallBall
import GradientHessian.UnmarkedReadout

/-! Localized-center and future-readout list bounds under an actual raw-law
factorization. The query list uses only the other-variables coordinate. -/

noncomputable section
namespace GradientHessian.FactoredTests
open MeasureTheory Matrix LowRank
open scoped InnerProductSpace

variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]

theorem center_list_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (hdim : 2≤Module.finrank ℝ E) (e : Ω ≃ᵐ E × W) (ρ : Measure Ω) (μ : Measure W)
    [IsProbabilityMeasure μ] (he : MeasurePreserving e ρ ((SphereGaussian.sphereLaw E).prod μ))
    (N : ℕ) {R w : ℝ} (hR : 0<R) (hw : 0≤w) (hRw : 16*w≤R)
    (queries : W → Fin N → E) (hq : ∀ i, Measurable (fun x => queries x i)) :
    ρ.real {x | ∃ i, ‖queries (e x).2 i-R•(e x).1‖≤3*w} ≤
      N*(2*(6*w/R)^(Module.finrank ℝ E-1)) := by
  apply list_bound e ρ (SphereGaussian.sphereLaw E) μ he N
    (fun i a v => ‖queries a i-R•v‖≤3*w)
  · intro i
    exact measurableSet_le (((hq i).comp measurable_fst).sub (measurable_const.smul measurable_snd)).norm measurable_const
  · positivity
  · intro i
    exact Filter.Eventually.of_forall (fun x => SphereSmallBall.small_support hdim (queries x i) hR hw hRw)

theorem readout_list_bound {d n r J : ℕ} [NeZero r] (hJ : 4≤J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ*B=1) (hPB : P*B=B) (fallback : Fin d → ℝ)
    (e : Ω ≃ᵐ EuclideanSpace ℝ (Fin r) × W) (ρ : Measure Ω) (μ : Measure W)
    [IsProbabilityMeasure μ]
    (he : MeasurePreserving e ρ ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod μ))
    (X : W → Matrix (Fin d) (Fin n) ℝ) (hXm : Measurable X)
    (hX : ∀ᵐ a ∂μ, X a ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (N : ℕ) (queries : W → Fin N → EuclideanSpace ℝ (Fin d))
    (hq : ∀ i, Measurable (fun a => queries a i)) (hqn : ∀ i, ∀ᵐ a ∂μ, ‖queries a i‖≤1)
    {γ : ℝ} (hγ : 0<γ) :
    ρ.real {x | ∃ i, γ < |⟪UnmarkedReadout.sourceOutput J P (X (e x).2) B fallback (e x).1,
      queries (e x).2 i⟫_ℝ|} ≤ N*(2*Real.exp (-(1/8)*γ^2*(r:ℝ))) := by
  apply list_bound e ρ (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))) μ he N
    (fun i a z => γ < |⟪UnmarkedReadout.sourceOutput J P (X a) B fallback z, queries a i⟫_ℝ|)
  · intro i
    apply measurableSet_lt measurable_const
    exact ((UnmarkedReadout.sourceOutput_measurable_comp J P B fallback
      (fun p : W × EuclideanSpace ℝ (Fin r) => X p.1) Prod.snd
      (hXm.comp measurable_fst) measurable_snd).inner ((hq i).comp measurable_fst)).abs
  · positivity
  · intro i
    filter_upwards [hX,hqn i] with a ha hn
    exact UnmarkedReadout.source_unmarked_test hJ hP ha B hB hPB fallback (queries a i) hn hγ

end GradientHessian.FactoredTests
