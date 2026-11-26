import LowRank.PairedKrylovPolicy
import LowRank.KrylovCompression
import LowRank.JoinedColumnSpace

/-! Recover the compression onto the union of two Krylov spaces directly
from the two query transcripts. The combined projector absorbs each one. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def pairedKrylovRightBlocks {a b s t n r : ℕ} (data : PairedKrylovData a b s t n r) :
    Matrix (Fin b) (Fin (n * s + r * t)) ℝ :=
  joinMatrixColumns (krylovRightBlocks data.1) (krylovRightBlocks data.2)

def pairedKrylovImageBlocks {a b s t n r : ℕ} (data : PairedKrylovData a b s t n r) :
    Matrix (Fin a) (Fin (n * s + r * t)) ℝ :=
  joinMatrixColumns (krylovImageBlocks data.1) (krylovImageBlocks data.2)

theorem measurable_pairedKrylovRightBlocks (a b s t n r : ℕ) :
    Measurable (pairedKrylovRightBlocks (a := a) (b := b) (s := s) (t := t) (n := n) (r := r)) :=
  (measurable_joinMatrixColumns b (n * s) (r * t)).comp
    (((measurable_krylovRightBlocks a b s n).comp measurable_fst).prodMk
      ((measurable_krylovRightBlocks a b t r).comp measurable_snd))

theorem measurable_pairedKrylovImageBlocks (a b s t n r : ℕ) :
    Measurable (pairedKrylovImageBlocks (a := a) (b := b) (s := s) (t := t) (n := n) (r := r)) :=
  (measurable_joinMatrixColumns a (n * s) (r * t)).comp
    (((measurable_krylovImageBlocks a b s n).comp measurable_fst).prodMk
      ((measurable_krylovImageBlocks a b t r).comp measurable_snd))

def pairedKrylovCompressedMatrix {a b s t n r : ℕ} (data : PairedKrylovData a b s t n r) :
    Matrix (Fin a) (Fin b) ℝ :=
  columnRangeImage (pairedKrylovRightBlocks data) (pairedKrylovImageBlocks data)

theorem measurable_pairedKrylovCompressedMatrix (a b s t n r : ℕ) :
    Measurable (pairedKrylovCompressedMatrix (a := a) (b := b) (s := s) (t := t) (n := n) (r := r)) :=
  (measurable_columnRangeImage a b (n * s + r * t)).comp
    ((measurable_pairedKrylovRightBlocks a b s t n r).prodMk
      (measurable_pairedKrylovImageBlocks a b s t n r))

def pairedKrylovProjector {a b s t : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (n r : ℕ) (U : PairedKrylovSeed a s t) : Matrix (Fin b) (Fin b) ℝ :=
  columnRangeProjector (pairedKrylovRightBlocks (krylovBlockData A n U.1, krylovBlockData A r U.2))

theorem pairedKrylovCompressedMatrix_eq {a b s t n r : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed a s t) :
    pairedKrylovCompressedMatrix (krylovBlockData A n U.1, krylovBlockData A r U.2) =
      A * pairedKrylovProjector A n r U := by
  unfold pairedKrylovCompressedMatrix pairedKrylovProjector pairedKrylovRightBlocks pairedKrylovImageBlocks
  simp only [krylovImageBlocks_mul, ← mul_joinMatrixColumns, columnRangeImage_mul]

theorem pairedKrylovProjector_isProjector {a b s t : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (n r : ℕ) (U : PairedKrylovSeed a s t) :
    IsOrthogonalProjector (pairedKrylovProjector A n r U) :=
  columnRangeProjector_isProjector _

theorem pairedKrylovProjector_absorbs_left {a b s t : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (n r : ℕ) (U : PairedKrylovSeed a s t) :
    pairedKrylovProjector A n r U * columnRangeProjector (krylovRightBlocks (krylovBlockData A n U.1)) =
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U.1)) :=
  joinedColumnProjector_absorbs_left _ _

theorem pairedKrylovProjector_absorbs_right {a b s t : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (n r : ℕ) (U : PairedKrylovSeed a s t) :
    pairedKrylovProjector A n r U * columnRangeProjector (krylovRightBlocks (krylovBlockData A r U.2)) =
      columnRangeProjector (krylovRightBlocks (krylovBlockData A r U.2)) :=
  joinedColumnProjector_absorbs_right _ _

end
end LowRank
