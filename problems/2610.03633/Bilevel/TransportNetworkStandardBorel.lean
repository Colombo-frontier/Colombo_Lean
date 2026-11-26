import Bilevel.TransportNetworkStabilizer
import Mathlib.Topology.MetricSpace.Polish

/-! The actual compact matrix network is a standard Borel sample space,
so its regular conditional distributions are genuine Markov kernels. -/
noncomputable section
namespace Bilevel.TransportNetwork

instance orthogonal_matrix_polish (d : ℕ) : PolishSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))

instance orthogonal_polish (d : ℕ) : PolishSpace (OrthogonalHaar.Group d) :=
  (OrthogonalHaar.carrier_closed d).polishSpace

instance latent_standardBorel (n d : ℕ) : StandardBorelSpace (Latent n d) := by
  infer_instance

end Bilevel.TransportNetwork
