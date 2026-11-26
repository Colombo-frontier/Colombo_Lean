import SampleReuse.OracleAdaptiveBatch

open MeasureTheory

namespace SampleReuse
noncomputable section

theorem adaptiveBatchMean_diagonal_measurable {Ω S E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {B : ℕ} (hB : 0 < B)
    (A : S → Ω → E) (hA : Measurable (fun w : S × Ω => A w.1 w.2))
    (n : S → ℕ) (hn : Measurable n)
    (tapes : S → SampleTape B Ω) (ht : Measurable tapes) :
    Measurable (fun s => adaptiveBatchMean hB A n s (tapes s)) :=
  (adaptiveBatchMean_measurable hB A hA n hn).comp (measurable_id.prodMk ht)

end
end SampleReuse
