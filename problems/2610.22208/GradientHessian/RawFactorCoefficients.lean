import GradientHessian.RawMarkFactor
import GradientHessian.UnmarkedReadout

/-! The isolated raw coordinates are exactly the actual numerical leaf
coefficients, including the synthesized readout of a selected future mark. -/

noncomputable section
namespace GradientHessian.RawLeafFactor
open Matrix LowRank HigherHierarchy RawHierarchy

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem leaf_A_assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (x : Raw d n r J E H t) (i : LeafSlot t),
    (leafData t (assemble P B fallback t x) i).A =
      matrixEuclideanMap (MatrixGoodSpectrum.sourceMatrix P J (leafNumerical t x i).1)
  | 0, _x, _i => rfl
  | t+1, x, i => leaf_A_assemble P B fallback t (x.1 i.1) i.2

theorem leaf_b_assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (x : Raw d n r J E H t) (i : LeafSlot t) (j : Fin (4096*J^2+1)),
    (leafData t (assemble P B fallback t x) i).b j =
      InverseGate.H₀ • matrixEuclideanMap B ((leafNumerical t x i).2 j)
  | 0, _x, _i, _j => rfl
  | t+1, x, i, j => leaf_b_assemble P B fallback t (x.1 i.1) i.2 j

theorem leaf_a_assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (x : Raw d n r J E H t) (i : LeafSlot t) (j : Fin (4096*J^2+1)),
    (leafData t (assemble P B fallback t x) i).a j =
      UnmarkedReadout.sourceOutput J P (leafNumerical t x i).1 B fallback ((leafNumerical t x i).2 j)
  | 0, _x, _i, _j => rfl
  | t+1, x, i, j => leaf_a_assemble P B fallback t (x.1 i.1) i.2 j

variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

theorem leaf_a_mark_factor (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (x : Raw d n r J E H t) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    (leafData t (assemble P B fallback t x) i).a j = UnmarkedReadout.sourceOutput J P
      (RawMarkFactor.factor t i j x).2.1 B fallback (RawMarkFactor.factor t i j x).1 := by
  rw [RawMarkFactor.factor_matrix, RawMarkFactor.factor_mark]
  exact leaf_a_assemble P B fallback t x i j

end GradientHessian.RawLeafFactor

namespace GradientHessian.RawMarkFactor
open MeasureTheory Matrix

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)] [∀ t, MeasurableSpace (H t)]
  [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]

theorem restLaw_matrix_good (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (t : ℕ) :
    ∀ᵐ x ∂restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t,
      x.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J := by
  letI := RawLeafFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  exact Measure.quasiMeasurePreserving_fst.ae (ConditionedSource.sourceLaw_good P J)

end GradientHessian.RawMarkFactor
