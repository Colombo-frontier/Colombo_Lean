import Bilevel.TransportControllerStore
import Bilevel.TransportControllerEdge
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! Borel operator-angle monitors for the actual finite projector stores.
This supplies a concrete measurable form for the variable subspace events
used by adaptive controller monitoring. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportControllerOperator
open EuclideanGaussian OrthogonalAction ProjectionGeometry
set_option maxHeartbeats 600000

def operator (D : ℕ) (A : ProjectionStore.Store D) : Space D →L[ℝ] Space D :=
  ∑ i, ContinuousLinearMap.smulRightL ℝ (Space D) (Space D) (innerSL ℝ (ProjectionStore.basis D i)) (A i)

theorem operator_apply (D : ℕ) (A : ProjectionStore.Store D) (x : Space D) :
    operator D A x = ProjectionStore.apply D A x := by
  rw [operator,ContinuousLinearMap.sum_apply]
  rfl

theorem operator_continuous (D : ℕ) : Continuous (operator D) := by
  apply continuous_finset_sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ (Space D) (Space D)
    (innerSL ℝ (ProjectionStore.basis D i))).continuous.comp (continuous_apply i)

theorem operator_subspace (D : ℕ) (W : Submodule ℝ (Space D)) :
    operator D (ProjectionStore.ofSubspace D W) = W.subtypeL.comp W.orthogonalProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact (operator_apply D _ x).trans (ProjectionStore.apply_subspace D W x)

def edgeOperator (D : ℕ) (O : OrthogonalHaar.Group D) : Space D →L[ℝ] Space D :=
  operator D (fun i => O • ProjectionStore.basis D i)

theorem edgeOperator_apply (D : ℕ) (O : OrthogonalHaar.Group D) (x : Space D) :
    edgeOperator D O x = O • x := by
  rw [edgeOperator,operator_apply,ProjectionStore.apply]
  change (∑ i, ⟪ProjectionStore.basis D i,x⟫ • isometry D O (ProjectionStore.basis D i)) = isometry D O x
  simp_rw [← map_smul]
  rw [← map_sum]
  rw [(ProjectionStore.basis D).sum_repr' x]

theorem edgeOperator_continuous (D : ℕ) : Continuous (edgeOperator D) := by
  letI : ContinuousSMul (OrthogonalHaar.Group D) (Space D) := ⟨action_continuous D⟩
  apply (operator_continuous D).comp
  exact continuous_pi (fun _ => continuous_id.smul continuous_const)

def angleOperator (D : ℕ) (W R : ProjectionStore.Store D) (O : OrthogonalHaar.Group D) :
    Space D →L[ℝ] Space D := (operator D W).comp ((edgeOperator D O).comp (operator D R))

theorem angleOperator_apply (D : ℕ) (W R : Submodule ℝ (Space D))
    (O : OrthogonalHaar.Group D) (x : Space D) :
    angleOperator D (ProjectionStore.ofSubspace D W) (ProjectionStore.ofSubspace D R) O x =
      project W (O • project R x) := by
  simp only [angleOperator,ContinuousLinearMap.comp_apply,operator_apply,
    ProjectionStore.apply_subspace,edgeOperator_apply]

theorem angleBad_iff_norm (D : ℕ) (W R : Submodule ℝ (Space D)) (O : OrthogonalHaar.Group D) :
    TransportControllerEdge.angleBad W R O ↔
      (1:ℝ)/8 < ‖angleOperator D (ProjectionStore.ofSubspace D W) (ProjectionStore.ofSubspace D R) O‖ := by
  classical
  let L := angleOperator D (ProjectionStore.ofSubspace D W) (ProjectionStore.ofSubspace D R) O
  have happ (u : R) : L (u : Space D) = project W (O • (u : Space D)) := by
    rw [angleOperator_apply,TransportObserver.project_self R u.property]
  constructor
  · rintro ⟨u,hu⟩
    by_contra hn
    have hle : ‖L‖ ≤ (1:ℝ)/8 := le_of_not_gt hn
    have hh := (L.le_opNorm (u : Space D)).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))
    rw [happ u] at hh
    exact not_lt_of_ge (by simpa [mul_comm,div_eq_mul_inv] using hh) hu
  · intro hn
    by_contra hb
    have hbound (x : Space D) : ‖L x‖ ≤ (1:ℝ)/8*‖x‖ := by
      rw [angleOperator_apply]
      have hh : ‖project W (O • project R x)‖ ≤ ‖project R x‖/8 :=
        le_of_not_gt (fun hx => hb ⟨⟨project R x,project_mem R x⟩,hx⟩)
      exact hh.trans (by
        have hh' := mul_le_mul_of_nonneg_left (TransportObserver.project_norm_le R x) (by norm_num : (0:ℝ)≤1/8)
        simpa [mul_comm,div_eq_mul_inv] using hh')
    exact not_lt_of_ge (ContinuousLinearMap.opNorm_le_bound L (by norm_num) hbound) hn

theorem angleOperator_continuous (D : ℕ) :
    Continuous (fun p : ProjectionStore.Store D × ProjectionStore.Store D × OrthogonalHaar.Group D =>
      angleOperator D p.1 p.2.1 p.2.2) :=
  ((operator_continuous D).comp continuous_fst).clm_comp
    (((edgeOperator_continuous D).comp (continuous_snd.comp continuous_snd)).clm_comp
      ((operator_continuous D).comp (continuous_fst.comp continuous_snd)))

theorem angleBad_store_measurable {Ω : Type*} [MeasurableSpace Ω] (D : ℕ)
    (W R : Ω → Submodule ℝ (Space D))
    (hW : Measurable (fun ω => ProjectionStore.ofSubspace D (W ω)))
    (hR : Measurable (fun ω => ProjectionStore.ofSubspace D (R ω)))
    (O : Ω → OrthogonalHaar.Group D) (hO : Measurable O) :
    MeasurableSet {ω | TransportControllerEdge.angleBad (W ω) (R ω) (O ω)} := by
  simp_rw [angleBad_iff_norm]
  exact measurableSet_lt measurable_const
    (((angleOperator_continuous D).measurable.comp (hW.prodMk (hR.prodMk hO))).norm)

end Bilevel.TransportControllerOperator
