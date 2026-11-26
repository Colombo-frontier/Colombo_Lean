import Geode.PublicState
import Geode.Parameters
import Geode.CandidateSeparation
import Geode.ResidualDimension

/-! The exact radius budget and separation of an arbitrary final output. -/
namespace Geode

theorem eta_four_mul (ε : ℝ) : eta (4 * ε) = cutLatitude ε := by
  unfold eta cutLatitude
  congr 1 <;> ring

theorem contraction_four_mul (ε : ℝ) :
    Lorentz.latitudeContraction (eta (4 * ε)) = cutContraction ε := by
  rw [eta_four_mul]
  rfl

end Geode

namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {o : Point E} {R ε : ℝ}

theorem PublicState.radius_ge_half (s : PublicState o R (4 * ε))
    (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hk : s.cuts ≤ Geode.queryHorizon R ε) : R / 2 ≤ s.S := by
  apply Geode.residual_radius_ge_half hR hε hεmax hk
  simpa only [Geode.contraction_four_mul] using s.radius

theorem PublicState.candidates_nonempty {μ : ℝ} (s : PublicState o R μ)
    {T : ℕ} (hcuts : s.cuts ≤ T)
    (hdim : T + 3 ≤ Module.finrank ℝ (Ambient E)) : s.candidates.Nonempty := by
  apply candidateSet_nonempty s.W s.center_mem
  have h := s.dimension
  omega

theorem PublicState.output_separation (s : PublicState o R (4 * ε))
    (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hk : s.cuts ≤ Geode.queryHorizon R ε)
    (hdim : Geode.queryHorizon R ε + 3 ≤ Module.finrank ℝ (Ambient E)) (x : Point E) :
    ∃ p ∈ s.candidates, R / 2 ≤ dist x p := by
  obtain ⟨p, hp, hfar⟩ := candidate_far_of_nonempty s.center_mem s.positive.le
    (s.candidates_nonempty hk hdim) x
  exact ⟨p, hp, (s.radius_ge_half hR hε hεmax hk).trans hfar⟩

end Geode.Lorentz
