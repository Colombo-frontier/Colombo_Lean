import Matvec.MainSequences
import Matvec.BallRateCorollary
import Matvec.AllDimensionSpectral

/-! Unconditional exported headline theorems of the matvec manuscript.
See `proof/matvec/COVERAGE.md` for exact statement correspondence and
the alternative proofs used for several intermediate lemmas. -/
namespace Matvec

/-- The manuscript's high-dimensional accuracy-rate corollary for both
geometries, all sufficiently small positive accuracies, and all larger
row and column dimensions. -/
theorem high_dimensional_rates : HighDimensionalRates :=
  main_sequences_imply_high_dimensional_rates main_sequence_lower_bounds

end Matvec
