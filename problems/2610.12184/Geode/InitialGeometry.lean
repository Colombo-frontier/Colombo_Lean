import Geode.ResidualDimension
import Geode.NormalReserve
import Geode.GeometricCarrier

/-! The concrete initial public space and candidate sphere. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def initialSpace (c : Point E) : Submodule ℝ (Ambient E) := Submodule.span ℝ {c.val}

theorem center_mem_initialSpace (c : Point E) : c.val ∈ initialSpace c :=
  Submodule.subset_span (Set.mem_singleton c.val)

theorem point_mem_initialSpace_iff (c x : Point E) : x.val ∈ initialSpace c ↔ x = c := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    have hsq : t ^ 2 = 1 := by
      have h := x.normalized
      rw [← ht, form_smul_left, form_smul_right, c.normalized] at h
      nlinarith only [h]
    have ht1 : 1 ≤ t := by
      have h := reverse_cauchy x c
      simpa only [← ht, form_smul_left, c.normalized, mul_neg_one, neg_neg] using h
    have htone : t = 1 := by nlinarith only [hsq, ht1]
    apply Point.ext
    rw [← ht, htone, one_smul]
  · intro h
    rw [h]
    exact center_mem_initialSpace c

theorem initial_section_eq_singleton (c : Point E) :
    {x : Point E | x.val ∈ initialSpace c} = {c} := by
  ext x
  exact point_mem_initialSpace_iff c x

noncomputable def initialPublicDomain (c : Point E) (η R : ℝ) : Set (Point E) :=
  Metric.closedBall c (publicRadius η R) ∩ {x | x.val ∈ initialSpace c}

theorem initialPublicDomain_eq_singleton (c : Point E) {η R : ℝ}
    (hη : 0 ≤ η) (hR : 0 ≤ R) : initialPublicDomain c η R = {c} := by
  rw [initialPublicDomain, initial_section_eq_singleton]
  apply Set.inter_eq_right.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact Metric.mem_closedBall_self (publicRadius_nonneg hη hR)

theorem initialPublicDomain_compact (c : Point E) {η R : ℝ}
    (hη : 0 ≤ η) (hR : 0 ≤ R) : IsCompact (initialPublicDomain c η R) := by
  rw [initialPublicDomain_eq_singleton c hη hR]
  exact isCompact_singleton

theorem initialPublicDomain_gconvex (c : Point E) (η R : ℝ) :
    GConvex (initialPublicDomain c η R) :=
  (gconvex_closedBall c (publicRadius η R)).inter (gconvex_section (initialSpace c))

theorem initialPublicDomain_nonempty (c : Point E) {η R : ℝ}
    (hη : 0 ≤ η) (hR : 0 ≤ R) : (initialPublicDomain c η R).Nonempty := by
  rw [initialPublicDomain_eq_singleton c hη hR]
  exact Set.singleton_nonempty c

theorem initialPublicDomain_section (c : Point E) (η R : ℝ) :
    ∀ x ∈ initialPublicDomain c η R, x.val ∈ initialSpace c := fun _ hx => hx.2

theorem initialPublicDomain_contains_ball (c : Point E) (η R : ℝ) :
    ∀ x : Point E, x.val ∈ initialSpace c → dist c x ≤ publicRadius η R →
      x ∈ initialPublicDomain c η R := by
  intro x hx hd
  exact ⟨by simpa only [Metric.mem_closedBall, dist_comm] using hd, hx⟩

theorem initialPublicDomain_subset_ball (c : Point E) {η R : ℝ}
    (hη : 0 ≤ η) (hR : 0 ≤ R) : initialPublicDomain c η R ⊆ Metric.closedBall c R := by
  rw [initialPublicDomain_eq_singleton c hη hR]
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact Metric.mem_closedBall_self hR

theorem initial_candidates_subset_ball (c : Point E) {R : ℝ} (hR : 0 ≤ R) :
    candidateSet (initialSpace c) c R ⊆ Metric.closedBall c R := by
  intro p hp
  have h := candidate_distance (center_mem_initialSpace c) hR hp
  simpa only [Metric.mem_closedBall, dist_comm, h] using le_refl R

theorem initial_hull_subset_ball (c : Point E) {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R) :
    closedGConv (initialPublicDomain c η R ∪ candidateSet (initialSpace c) c R) ⊆
      Metric.closedBall c R := by
  apply closedGConv_minimal _ Metric.isClosed_closedBall (gconvex_closedBall c R)
  exact Set.union_subset (initialPublicDomain_subset_ball c hη hR)
    (initial_candidates_subset_ball c hR)

theorem finrank_initialSpace (c : Point E) : Module.finrank ℝ (initialSpace c) = 1 := by
  apply finrank_span_singleton
  intro h
  have ht := c.future
  rw [h] at ht
  simp at ht

variable [FiniteDimensional ℝ E]

theorem finrank_initial_residual (c : Point E) :
    Module.finrank ℝ (residualSpace (initialSpace c)) = Module.finrank ℝ E := by
  have h := finrank_public_add_residual (initialSpace c) (center_mem_initialSpace c)
  rw [finrank_initialSpace] at h
  simpa only [Ambient, Module.finrank_prod, Module.finrank_self, Nat.add_left_cancel_iff] using h

theorem initial_candidates_nonempty (c : Point E) (R : ℝ)
    (hdim : 0 < Module.finrank ℝ E) : (candidateSet (initialSpace c) c R).Nonempty := by
  apply candidateSet_nonempty (initialSpace c) (center_mem_initialSpace c)
  simpa only [finrank_initialSpace, Ambient, Module.finrank_prod, Module.finrank_self,
    lt_add_iff_pos_right] using hdim

theorem initial_hull_compact (c : Point E) {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R) :
    IsCompact (closedGConv (initialPublicDomain c η R ∪ candidateSet (initialSpace c) c R)) :=
  (isCompact_closedBall c R).of_isClosed_subset (isClosed_closedGConv _)
    (initial_hull_subset_ball c hη hR)

end Geode.Lorentz
