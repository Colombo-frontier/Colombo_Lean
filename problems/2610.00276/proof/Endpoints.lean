import NoisyZO.ConcreteMain
import NoisyZO.SharpRate

/-! These checks expose the concrete lower/upper component types and the
remaining common-risk certificate interface. They do not assert completion
of the unformalized algorithm-representation bridge. -/
#check @NoisyZO.dimensionFreeLowerRate_le_concreteMinimaxRisk
#check @NoisyZO.NormalizedObjective.fullMultiscaleProjectedBudgetOutputLaw_saturated_rate
#check @NoisyZO.normalized_sharp_rate_components
#check @NoisyZO.sharp_minimax_rate_of_certificates
