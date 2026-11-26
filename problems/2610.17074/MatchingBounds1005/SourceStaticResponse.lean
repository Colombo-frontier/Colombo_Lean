import MatchingBounds1005.SourceReferenceProtocol
import MatchingBounds1005.TensorPhysicalResponse
import MatchingBounds1005.VisibleCorrection

/-! The actual static tensor parameter gives the two physical source channels. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential GaussianFitter AccumulatedRows
open GaussianBlockProjection
open TensorGeometry hiding Vec

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

def cubicTensor (P : Parameters d N) (U : Vec d →L[ℝ] Vec d)
    (z : Vec (jointDim d)) : Tensor d 3 :=
  cubicSignal P.τ P.a (fun i => U (P.b i)) + P.σ₃ • gaussianTensor d 3
    (splitLinearEquiv (cubicDim d) (quarticDim d) z).1

def quarticTensor (P : Parameters d N) (U : Vec d →L[ℝ] Vec d)
    (z : Vec (jointDim d)) : Tensor d 4 :=
  quarticSignal P.τ P.a (fun i => U (P.b i)) + P.σ₄ • gaussianTensor d 4
    (splitLinearEquiv (cubicDim d) (quarticDim d) z).2

def directResponse (P : Parameters d N) (U : Vec d →L[ℝ] Vec d)
    (z : Vec (jointDim d)) (j : ℕ) (x : Vec d) : Model.Response d :=
  confineResponse P.R P.η x
    (dataResponse (10 * P.τ * N) (radial P.R x) (U P.c)
      (U (P.Q (U.adjoint (radial P.R x))))
      (channel 3 (cubicTensor P U z) (radial P.R x))
      (channel 4 (quarticTensor P U z) (radial P.R x))
      (Model.oracle (correctionSum (fun i => U (P.b i)) P.τ P.r P.a
        (Finset.univ.filter (fun i => P.disclosure i ≤ j + 1))) (radial P.R x)))

theorem cubicResponse_static (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (hσ : P.σ₃ ≠ 0) (n : ℕ) (hn : n < H)
    (h : History (Rot × Seed) (H * (d + d)) n) (z : Vec (jointDim d)) :
    cubicResponse n (rowResponse (accumulated (current P A U) n h)
      (fullSignal P U (initialSeed n h).1 + z)) =
        channel 3 (cubicTensor P (U (initialSeed n h).1) z)
          (confinedQuery A P.R n (before P A U n h)) := by
  ext i
  change ResponseHistory.currentBlock n (rowResponse (accumulated (current P A U) n h)
    (fullSignal P U (initialSeed n h).1 + z)) (Fin.castAdd d i) = _
  rw [ResponseHistory.currentBlock, dif_pos hn]
  rw [current_response (current P A U) (⟨n, hn⟩ : Fin H)]
  exact jointResponse_signal_left P.σ₃ P.σ₄ hσ _ _ _ _ i

theorem quarticResponse_static (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (hσ : P.σ₄ ≠ 0) (n : ℕ) (hn : n < H)
    (h : History (Rot × Seed) (H * (d + d)) n) (z : Vec (jointDim d)) :
    quarticResponse n (rowResponse (accumulated (current P A U) n h)
      (fullSignal P U (initialSeed n h).1 + z)) =
        channel 4 (quarticTensor P (U (initialSeed n h).1) z)
          (confinedQuery A P.R n (before P A U n h)) := by
  ext i
  change ResponseHistory.currentBlock n (rowResponse (accumulated (current P A U) n h)
    (fullSignal P U (initialSeed n h).1 + z)) (Fin.natAdd d i) = _
  rw [ResponseHistory.currentBlock, dif_pos hn]
  rw [current_response (current P A U) (⟨n, hn⟩ : Fin H)]
  exact jointResponse_signal_right P.σ₃ P.σ₄ hσ _ _ _ _ i

theorem assembled_static (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (hτ : ∀ i, 0 < P.disclosure i)
    (hr : 1 ≤ P.r) (hσ₃ : P.σ₃ ≠ 0) (hσ₄ : P.σ₄ ≠ 0) (n : ℕ) (hn : n < H)
    (h : History (Rot × Seed) (H * (d + d)) n) (z : Vec (jointDim d)) :
    assembled A (10 * P.τ * N) P.R P.η (correction P) n
      (before P A U n h,
        (U (initialSeed n h).1 (P.Q ((U (initialSeed n h).1).adjoint
          (confinedQuery A P.R n (before P A U n h)))),
          rowResponse (accumulated (current P A U) n h) (fullSignal P U (initialSeed n h).1 + z))) =
      directResponse P (U (initialSeed n h).1) z n (queryPoint A n (before P A U n h)) := by
  unfold assembled
  dsimp only
  rw [cubicResponse_static P A U hσ₃ n hn, quarticResponse_static P A U hσ₄ n hn]
  have hc : (before P A U n h).2.1.2 = U (initialSeed n h).1 P.c := replay_linear P A U n h
  have hb := before_readouts P A U hτ n h
  unfold correction
  dsimp only
  rw [hc, hb, correctionOracle_visibleAt P.b _ P.disclosure (n + 1) P.τ P.a hr]
  rfl

end MatchingBounds1005.SourceReferenceReplay
