import Geode.PublicState
import Geode.PublicQuery
import Geode.ResidualDimension

/-! A full public-state extension for each actual query point. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {o : Point E} {R μ : ℝ}

/-- The public state after retaining one residual latitude and adjoining its
normal direction. The new domain is the compact closed geodesic hull. -/
noncomputable def PublicState.cut (s : PublicState o R μ) (e : Ambient E)
    (he : IsResidual s.W e) (he1 : form E e e = 1) (hη : (Geode.eta μ) ^ 2 < 1) :
    PublicState o R μ := by
  let W' := expandedSpace s.W e
  let c' := recenteredCenter s.c e (residual_tangent s.center_mem he) he1
    (Geode.eta μ) s.S hη.le
  let S' := updatedRadius (Geode.eta μ) s.S
  let B : Set (Point E) := {x | x.val ∈ W' ∧ dist c' x ≤ publicRadius (Geode.eta μ) S'}
  have hB : Bornology.IsBounded B := by
    apply (Metric.isBounded_closedBall (x := c') (r := publicRadius (Geode.eta μ) S')).subset
    intro x hx
    exact Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hx.2)
  refine {
    W := W'
    c := c'
    S := S'
    cuts := s.cuts + 1
    P := closedGConv (s.P ∪ B)
    positive := updatedRadius_pos hη s.positive
    center_mem := recenteredCenter_mem s.center_mem he he1 (Geode.eta μ) s.S hη.le
    compact := isCompact_closedGConv_of_bounded (s.compact.isBounded.union hB)
    convex := gconvex_closedGConv _
    section_mem := ?_
    contains_ball := ?_
    dimension := ?_
    radius := ?_
    original := ?_ }
  · apply closedGConv_subset_section W' W'.closed_of_finiteDimensional
    intro x hx
    rcases hx with hx | hx
    · exact Submodule.mem_sup_left (s.section_mem x hx)
    · exact hx.1
  · intro x hx hd
    exact subset_closedGConv _ (Or.inr ⟨hx, hd⟩)
  · exact (finrank_adjoin_unit_le s.W he1).trans (by have h := s.dimension; omega)
  · change Real.sinh (updatedRadius (Geode.eta μ) s.S) = _
    rw [sinh_updatedRadius, s.radius, pow_succ]
    ring
  · intro p hp
    apply s.original p
    have hset := candidateSet_latitude_update s.center_mem he he1 hη s.positive
    rw [hset] at hp
    exact hp.1

theorem PublicState.cut_extension (s : PublicState o R μ) (e : Ambient E)
    (he : IsResidual s.W e) (he1 : form E e e = 1) (hη : (Geode.eta μ) ^ 2 < 1) :
    StateExtension s (s.cut e he he1 hη) := by
  refine ⟨le_sup_left, updatedRadius_le hη.le s.positive.le, ?_, ?_, ?_, le_rfl⟩
  · intro p hp
    change p ∈ candidateSet (expandedSpace s.W e)
      (recenteredCenter s.c e (residual_tangent s.center_mem he) he1
        (Geode.eta μ) s.S hη.le) (updatedRadius (Geode.eta μ) s.S) at hp
    rw [candidateSet_latitude_update s.center_mem he he1 hη s.positive] at hp
    exact hp.1
  · exact (Set.subset_union_left).trans (subset_closedGConv _)
  · exact Set.Subset.refl _

theorem PublicState.cut_latitude (s : PublicState o R μ) (e : Ambient E)
    (he : IsResidual s.W e) (he1 : form E e e = 1) (hη : (Geode.eta μ) ^ 2 < 1)
    {p : Point E} (hp : p ∈ (s.cut e he he1 hη).candidates) :
    form E e p.val = -Geode.eta μ * Real.sinh s.S := by
  change p ∈ candidateSet (expandedSpace s.W e)
    (recenteredCenter s.c e (residual_tangent s.center_mem he) he1
      (Geode.eta μ) s.S hη.le) (updatedRadius (Geode.eta μ) s.S) at hp
  rw [candidateSet_latitude_update s.center_mem he he1 hη s.positive] at hp
  exact hp.2

theorem RoutingData.latitude_of_point {z : Point E}
    (s : PublicState o R μ) (C : RoutingData s.P s.W s.c z μ s.S)
    {p : Point E} {v : Ambient E}
    (hp : p.val = Real.cosh s.S • s.c.val + Real.sinh s.S • v)
    (hlat : C.β = 0 ∨ form E C.e p.val = -Geode.eta μ * Real.sinh s.S) :
    C.β = 0 ∨ form E C.e v = -Geode.eta μ := by
  rcases hlat with h | h
  · exact Or.inl h
  · right
    rw [hp, form_add_right, form_smul_right, form_smul_right,
      C.residual_orthogonal _ s.center_mem] at h
    have hs := Real.sinh_pos_iff.mpr s.positive
    nlinarith

/-- A routing datum gives a full archived contact on any permitted extension
whose surviving candidates satisfy its selected latitude. -/
theorem contactSupports_of_routing {s s' : PublicState o R μ} {z y : Point E}
    (C : RoutingData s.P s.W s.c z μ s.S) (hz : z ∈ s.P)
    (hy : y ≠ z → direction z y = C.q)
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (hext : StateExtension s s') (hq : C.q ∈ s'.W)
    (hlat : ∀ p ∈ s'.candidates,
      C.β = 0 ∨ form E C.e p.val = -Geode.eta μ * Real.sinh s.S) :
    ∃ a : ArchivedContact E, a.y = y ∧ ContactSupports s' a := by
  let a : ArchivedContact E := {
    y := y, z := z, q := C.q, D := publicDistance s.c z s.S
    positive := publicDistance_pos s.c z s.positive
    tangent := C.q_tangent, unit := C.q_unit, direction_eq := hy }
  refine ⟨a, rfl, hext.domain hz, hq, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨v, hv, _, hrep⟩ := hext.candidates hp
    exact residual_distance s.c z p v s.S s.W C.contact_mem hv hrep
  · intro p hp
    obtain ⟨v, hv, _, hrep⟩ := hext.candidates hp
    have hlatitude := C.latitude_of_point s hrep (hlat p hp)
    obtain ⟨v', hv', _, hrep'⟩ := hp
    apply normalTo_iff_lorentz_halfspace.mpr
    refine ⟨(C.normal_for_candidate s.positive p v hv hrep).1, ?_⟩
    intro x hx
    apply closedGConv_subset_halfspace (a.normal μ p) ?_ (hext.hull hx)
    intro w hw
    rcases hw with hw | hw
    · exact (normalTo_iff_lorentz_halfspace.mp
        (C.normal_for_candidate s.positive p v hv hrep)).2 w hw
    · exact C.future_ball hμ hμmax s.positive p v hv hrep hlatitude
        s'.c v' s'.W s'.positive hext.radius s'.center_mem
        (hext.space C.contact_mem) hq hv' hrep' w hw.1 hw.2
  · intro p hp
    obtain ⟨v, hv, _, hrep⟩ := hext.candidates hp
    exact C.candidate_strict hμ hμmax s.positive p v hv hrep
      (C.latitude_of_point s hrep (hlat p hp))
  · intro p hp W' c' S' v' hW hc hS hSS hv' hrep' x hx hd
    obtain ⟨v, hv, _, hrep⟩ := hext.candidates hp
    exact C.future_ball hμ hμmax s.positive p v hv hrep
      (C.latitude_of_point s hrep (hlat p hp)) c' v' W' hS
      (hSS.trans hext.radius) hc (hW (hext.space C.contact_mem)) (hW hq)
      hv' hrep' x hx hd

/-- The degenerate latitude keeps the state, while a nonzero residual contact
direction makes exactly one geometric cut. -/
theorem state_extension_of_routing (s : PublicState o R μ) {z y : Point E}
    (C : RoutingData s.P s.W s.c z μ s.S) (hz : z ∈ s.P)
    (hy : y ≠ z → direction z y = C.q)
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hη : (Geode.eta μ) ^ 2 < 1) :
    ∃ s' : PublicState o R μ, ∃ a : ArchivedContact E,
      StateExtension s s' ∧ a.y = y ∧ ContactSupports s' a := by
  classical
  by_cases hβ : C.β = 0
  · have hq : C.q ∈ s.W := by simpa only [C.decomposition, hβ, zero_smul, add_zero] using C.public_mem
    obtain ⟨a, ha, hs⟩ := contactSupports_of_routing C hz hy hμ hμmax
      (StateExtension.refl s) hq (fun _ _ => Or.inl hβ)
    exact ⟨s, a, StateExtension.refl s, ha, hs⟩
  · let s' := s.cut C.e C.residual_orthogonal C.residual_unit hη
    have hext : StateExtension s s' := s.cut_extension C.e C.residual_orthogonal C.residual_unit hη
    have hq : C.q ∈ s'.W := by
      rw [C.decomposition]
      exact s'.W.add_mem (hext.space C.public_mem)
        (s'.W.smul_mem _ (mem_expandedSpace_self s.W C.e))
    obtain ⟨a, ha, hs⟩ := contactSupports_of_routing C hz hy hμ hμmax hext hq
      (fun p hp => Or.inr (s.cut_latitude C.e C.residual_orthogonal C.residual_unit hη hp))
    exact ⟨s', a, hext, ha, hs⟩

/-- Every query admits an actual public state extension and a complete contact
certificate, obtained from the geometric contact optimization. -/
theorem PublicState.query_extension (s : PublicState o R μ)
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hη : (Geode.eta μ) ^ 2 < 1)
    (hdim : Module.finrank ℝ s.W + 1 < Module.finrank ℝ (Ambient E)) (y : Point E) :
    ∃ s' : PublicState o R μ, ∃ a : ArchivedContact E,
      StateExtension s s' ∧ a.y = y ∧ ContactSupports s' a := by
  classical
  obtain ⟨e, he, he1⟩ := exists_residual_unit s.W s.center_mem (by omega)
  by_cases hy : y ∈ s.P
  · obtain ⟨C, _⟩ := on_domain_routing_exists s.W s.c y hμ hμmax s.positive
      s.center_mem hy s.section_mem s.contains_ball e he he1
    exact state_extension_of_routing s C hy (fun h => False.elim (h rfl)) hμ hμmax hη
  · obtain ⟨z, hz, C, hq, _⟩ := exterior_routing_exists s.W s.c y hμ hμmax s.positive
      s.compact s.convex s.center_mem hy s.section_mem s.contains_ball e he he1
    exact state_extension_of_routing s C hz (fun _ => hq.symm) hμ hμmax hη

end Geode.Lorentz
