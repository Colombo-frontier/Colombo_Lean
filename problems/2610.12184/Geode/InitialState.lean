import Geode.InitialGeometry
import Geode.PublicState
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Initialization of the concrete public-state induction in a dimension
that leaves a residual direction after every permitted query. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def initialPublicState (o : Point E) (R μ : ℝ)
    (hR : 0 < R) (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) : PublicState o R μ where
  W := initialSpace o
  c := o
  S := R
  cuts := 0
  P := initialPublicDomain o (Geode.eta μ) R
  positive := hR
  center_mem := center_mem_initialSpace o
  compact := initialPublicDomain_compact o (Geode.eta_pos hμ hμmax).le hR.le
  convex := initialPublicDomain_gconvex o (Geode.eta μ) R
  section_mem := initialPublicDomain_section o (Geode.eta μ) R
  contains_ball := initialPublicDomain_contains_ball o (Geode.eta μ) R
  dimension := by simp only [finrank_initialSpace, zero_add, le_refl]
  radius := by simp only [pow_zero, one_mul]
  original := fun _ hp => candidate_distance (center_mem_initialSpace o) hR.le hp

@[simp] theorem initialPublicState_cuts (o : Point E) (R μ : ℝ)
    (hR : 0 < R) (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) :
    (initialPublicState o R μ hR hμ hμmax).cuts = 0 := rfl

@[simp] theorem initialPublicState_radius (o : Point E) (R μ : ℝ)
    (hR : 0 < R) (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) :
    (initialPublicState o R μ hR hμ hμmax).S = R := rfl

theorem initialPublicState_domain (o : Point E) (R μ : ℝ)
    (hR : 0 < R) (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) :
    (initialPublicState o R μ hR hμ hμmax).P = {o} :=
  initialPublicDomain_eq_singleton o (Geode.eta_pos hμ hμmax).le hR.le

theorem initialPublicState_nonempty (o : Point E) (R μ : ℝ)
    (hR : 0 < R) (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (hdim : 0 < Module.finrank ℝ E) :
    (initialPublicState o R μ hR hμ hμmax).candidates.Nonempty :=
  initial_candidates_nonempty o R hdim

theorem ambient_finrank (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.finrank ℝ (Ambient E) = Module.finrank ℝ E + 1 := by
  simp only [Ambient, Module.finrank_prod, Module.finrank_self, Nat.add_comm]

theorem ambient_finrank_query_dimension (T : ℕ) :
    Module.finrank ℝ (Ambient (EuclideanSpace ℝ (Fin (T + 2)))) = T + 3 := by
  rw [ambient_finrank, finrank_euclideanSpace_fin]

theorem PublicState.residual_capacity {o : Point E} {R μ : ℝ}
    (s : PublicState o R μ) {T : ℕ} (hcuts : s.cuts ≤ T)
    (hdim : T + 3 ≤ Module.finrank ℝ (Ambient E)) :
    Module.finrank ℝ s.W + 1 < Module.finrank ℝ (Ambient E) := by
  have h := s.dimension
  omega

theorem PublicState.candidates_nonempty_of_capacity {o : Point E} {R μ : ℝ}
    (s : PublicState o R μ) {T : ℕ} (hcuts : s.cuts ≤ T)
    (hdim : T + 2 ≤ Module.finrank ℝ (Ambient E)) : s.candidates.Nonempty := by
  apply candidateSet_nonempty s.W s.center_mem
  have h := s.dimension
  omega

end Geode.Lorentz
