import SampleReuse.OracleAdaptiveProgram
import Mathlib.MeasureTheory.Function.Floor

/-! The reserved block capacity is a deterministic consequence of the
uniform noise bound: every edge batch is at most the root batch. Thus fresh
block reservation imposes no new restriction on Algorithm 2. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

theorem batchSize_mono_weight {scale u v : ℝ} (hs : 0 ≤ scale) (huv : u ≤ v) :
    batchSize scale u ≤ batchSize scale v :=
  max_le_max_left _ (Nat.ceil_mono (mul_le_mul_of_nonneg_left huv hs))

def chordBatchSize {E : Type*} [NormedAddCommGroup E]
    (scale σ L : ℝ) (x y : E) : ℕ := batchSize scale (min (σ^2) (L^2 * ‖x-y‖^2))

theorem chordBatchSize_pos {E : Type*} [NormedAddCommGroup E]
    (scale σ L : ℝ) (x y : E) : 0 < chordBatchSize scale σ L x y :=
  batchSize_pos _ _

theorem chordBatchSize_le_capacity {E : Type*} [NormedAddCommGroup E]
    {scale : ℝ} (hs : 0 ≤ scale) (σ L : ℝ) (x y : E) :
    chordBatchSize scale σ L x y ≤ batchSize scale (σ^2) :=
  batchSize_mono_weight hs (min_le_left _ _)

theorem chordBatchSize_measurable {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (scale σ L : ℝ) (x y : S → E) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun s => chordBatchSize scale σ L (x s) (y s)) :=
  measurable_const.max (Nat.measurable_ceil.comp
    (measurable_const.mul (measurable_const.min (measurable_const.mul ((hx.sub hy).norm.pow_const 2)))))

theorem gradient_chordBatchSize_sufficient {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) {η δ σ L : ℝ} (hη : 0 < η) (hσ : 0 ≤ σ) (hL : 0 ≤ L) (x y : E) :
    32 * (matrixMomentOrder (d + 1) δ : ℝ) * (2 * min σ (L * ‖x-y‖))^2 ≤
      (chordBatchSize (confidenceBatchScale d η δ) σ L x y : ℝ) * η^2 :=
  confidenceBatchSize_gradient_edge d hη hσ hL x y

theorem hessian_chordBatchSize_sufficient {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) {η δ σ L : ℝ} (hη : 0 < η) (hσ : 0 ≤ σ) (hL : 0 ≤ L) (x y : E) :
    8 * (matrixMomentOrder (d + 1) δ : ℝ) * (2 * min σ (L * ‖x-y‖))^2 ≤
      (chordBatchSize (confidenceBatchScale d η δ) σ L x y : ℝ) * η^2 :=
  confidenceBatchSize_hessian_edge d hη hσ hL x y

end
end SampleReuse
