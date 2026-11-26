import GradientHessian.MarkHitContainment
import GradientHessian.RawFactorSeed
import GradientHessian.FactoredGeometricTests

/-! A future-mark repair bound under the original presampled hierarchy law
and any independent private-seed law. The actual shadow array is constructed
from the policy; its visibility budget and independence are not hypotheses. -/

noncomputable section
namespace GradientHessian.MarkVisibleQueries
open Classical MeasureTheory HigherHierarchy HierarchyAddresses RawHierarchy
open FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
open ControllerPolicyCoupling Matrix LowRank

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))
variable [NeZero r] [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
  (σ : Measure Seed) [IsProbabilityMeasure σ]

theorem array_probability_bound (hJ : 4≤J) (hP : IsOrthogonalProjector P)
    (hB : Bᵀ*B=1) (hPB : P*B=B) {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (t+1) (4096*J^2+1) ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | arrayHit P B fallback t leaf j policy K N fuel s₀ w} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(1/8)*(1/3072:ℝ)^2*(r:ℝ))) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  letI := RawMarkFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  let e₀ : Raw d n r J E H t ≃ᵐ EuclideanSpace ℝ (Fin r) × RawMarkFactor.Rest d n r J E H t :=
    RawMarkFactor.factor t ((leafEquiv t).symm leaf) j
  let e : Raw d n r J E H t × Seed ≃ᵐ EuclideanSpace ℝ (Fin r) × (RawMarkFactor.Rest d n r J E H t × Seed) :=
    RawFactorSeed.factor e₀
  have he₀ : MeasurePreserving e₀ (RawHierarchy.law P t)
      ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod (RawMarkFactor.restLaw P t)) :=
    RawMarkFactor.factor_preserving P t ((leafEquiv t).symm leaf) j
  have he := RawFactorSeed.factor_preserving e₀ (RawHierarchy.law P t)
    (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))) (RawMarkFactor.restLaw P t) σ he₀
  have hX : ∀ᵐ w : RawMarkFactor.Rest d n r J E H t × Seed ∂(RawMarkFactor.restLaw P t).prod σ,
      w.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J :=
    Measure.quasiMeasurePreserving_fst.ae (RawMarkFactor.restLaw_matrix_good P t)
  have hb := FactoredTests.readout_list_bound hJ hP B hB hPB fallback e ((RawHierarchy.law P t).prod σ)
    ((RawMarkFactor.restLaw P t).prod σ) he (fun w : RawMarkFactor.Rest d n r J E H t × Seed => w.1.1)
    (measurable_fst.comp measurable_fst) hX ((4096*J^2+1)*ell)
    (query (n := n) P B fallback t leaf j policy K N fuel s₀)
    (query_measurable (n := n) P B fallback t leaf j policy hK N fuel s₀)
    (fun i => Filter.Eventually.of_forall (fun w => query_norm P B fallback t leaf j policy K N fuel s₀ w i))
    (by norm_num : (0:ℝ)<1/3072)
  simpa only [e,e₀,RawFactorSeed.factor_apply,arrayHit] using hb

theorem shadow_hit_probability_bound (hJ : 4≤J) (hP : IsOrthogonalProjector P)
    (hB : Bᵀ*B=1) (hPB : P*B=B) {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (t+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | hitBy P B fallback t leaf j policy K N fuel s₀ w} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(1/8)*(1/3072:ℝ)^2*(r:ℝ))) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  apply le_trans (measureReal_mono (fun w hw => hitBy_covered P B fallback t leaf j policy hK N fuel s₀ hs hell w hw))
  exact array_probability_bound P B fallback t leaf j policy σ hJ hP hB hPB hK N fuel s₀

end GradientHessian.MarkVisibleQueries
