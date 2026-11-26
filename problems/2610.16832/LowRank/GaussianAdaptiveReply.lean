import LowRank.GaussianAdaptiveStep
import LowRank.GaussianQueryAlgebra
import LowRank.GaussianFirstQuery

/-! The actual Gram oracle reply can be reconstructed measurably from the
enlarged exposed state after an adaptive step. -/

namespace LowRank
open MeasureTheory
open scoped Matrix
noncomputable section

variable {E F S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace S] {r s : ℕ}

theorem measurable_coordinate_rowGauge (b : OrthonormalBasis (Fin (r + 1)) ℝ E) :
    Measurable (fun p : (Fin (r + 1) → ℝ) × (Fin (r + 1) → ℝ) =>
      coordinateRotation b (rowGauge b p.1) p.2) := by
  have harg : Measurable (fun p : (Fin (r + 1) → ℝ) × (Fin (r + 1) → ℝ) =>
      (p.1, fun _ : Fin 1 => p.2)) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro i
    exact measurable_snd
  exact (measurable_pi_apply (0 : Fin 1)).comp ((measurable_rowGauge_rotation b).comp harg)

def exposedGramColumn (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (st : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) : Fin (r + 1) → ℝ :=
  Fin.cons (exposedFirstReply c st).1 (exposedFirstReply c st).2

theorem measurable_exposedGramColumn (c : OrthonormalBasis (Fin (s + 1)) ℝ F) :
    Measurable (exposedGramColumn (r := r) c) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (measurable_exposedFirstReply c).fst
  · exact (measurable_pi_apply j).comp (measurable_exposedFirstReply c).snd

theorem exposedGramColumn_eq (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    exposedGramColumn c (revealGaussianBlock c X).1 = fun i => (X * Xᵀ) i 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (revealGaussianBlock_gram_pivot c X).symm
  · exact (revealGaussianBlock_gram_column c X j).symm

def decodeAdaptiveReply (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (q : S → Fin (r + 1) → ℝ)
    (st : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ))) : Fin (r + 1) → ℝ :=
  coordinateRotation b (rowGauge b (q st.1)) (exposedGramColumn c st.2)

theorem measurable_decodeAdaptiveReply (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (q : S → Fin (r + 1) → ℝ)
    (hq : Measurable q) : Measurable (decodeAdaptiveReply b c q) := by
  have harg : Measurable (fun st : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      (q st.1, exposedGramColumn c st.2)) :=
    (hq.comp measurable_fst).prodMk ((measurable_exposedGramColumn c).comp measurable_snd)
  simpa only [Function.comp_def, decodeAdaptiveReply] using
    (measurable_coordinate_rowGauge b).comp harg

theorem decodeAdaptiveReply_eq (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (q : S → Fin (r + 1) → ℝ)
    (p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ)
    (hq : ‖(basisCoordinates b).symm (q p.1)‖ = 1) :
    decodeAdaptiveReply b c q (adaptiveGaussianStep b c q p).1 = (p.2 * p.2ᵀ) *ᵥ q p.1 := by
  change coordinateRotation b (rowGauge b (q p.1))
    (exposedGramColumn c (revealGaussianBlock c
      (rotateMatrixColumns b (rowGauge b (q p.1)) p.2)).1) = _
  rw [exposedGramColumn_eq, query_rotation_gram_reply b _ hq]
  exact query_rotation_involutive b _ _

theorem adaptive_reply_residual_independent (ν : Measure S) [IsProbabilityMeasure ν]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (q : S → Fin (r + 1) → ℝ) (hq : Measurable q)
    (hunit : ∀ st, ‖(basisCoordinates b).symm (q st)‖ = 1) (v : NNReal) :
    ProbabilityTheory.IndepFun
      (fun p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ => (p.1, (p.2 * p.2ᵀ) *ᵥ q p.1))
      (fun p => (adaptiveGaussianStep b c q p).2)
      (ν.prod (iidMatrixLaw (r + 1) (s + 1) v)) := by
  have h := (adaptiveGaussianStep_independent ν b c q hq v).comp
    (measurable_fst.prodMk (measurable_decodeAdaptiveReply b c q hq)) measurable_id
  have heq : (fun p => ((adaptiveGaussianStep b c q p).1.1,
      decodeAdaptiveReply b c q (adaptiveGaussianStep b c q p).1)) =
      (fun p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ => (p.1, (p.2 * p.2ᵀ) *ᵥ q p.1)) := by
    funext p
    exact Prod.ext rfl (decodeAdaptiveReply_eq b c q p (hunit p.1))
  simpa only [Function.comp_def, id_eq, heq] using h

end
end LowRank
