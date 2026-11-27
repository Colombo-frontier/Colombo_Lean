import UpperPublicParameters

open Task006.HaarRebalancing Task006.Full.SampleInstance
namespace Task006.Full

noncomputable def upperActualBias (P : UpperProgramParameters) (d : ℕ) (L s : ℝ) : ℝ :=
  Real.sqrt d * rebalancingThreshold L d s * P.b ^ (-1 / 2 : ℝ) +
    Real.sqrt d * (d * L * P.δ / P.ρ) +
      (Real.sqrt d * P.b + L) * ((d : ℝ) * Real.exp (-s))

noncomputable def upperActualSecondMoment (P : UpperProgramParameters) (d : ℕ) (L s : ℝ) : ℝ :=
  d * rebalancingThreshold L d s * P.b ^ (1 / 2 : ℝ) +
    (d * P.b ^ 2) * ((d : ℝ) * Real.exp (-s))


noncomputable def upperRiskBudget (P : UpperProgramParameters) (d : ℕ) (L s : ℝ) (T : ℕ) : ℝ :=
  P.R ^ 2 / (2 * P.η * T) + 2 * P.R * upperActualBias P d L s +
    P.η * upperActualSecondMoment P d L s / 2 + 2 * P.ρ * L + L * (P.ρ + P.δ)

end Task006.Full
