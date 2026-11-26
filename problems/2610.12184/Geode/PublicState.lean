import Geode.CandidateUpdate
import Geode.GeometricRouting
import Geode.GeometricCarrier

/-! Public geometric states and persistent certificates for full contacts. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

structure PublicState (o : Point E) (R μ : ℝ) where
  W : Submodule ℝ (Ambient E)
  c : Point E
  S : ℝ
  cuts : ℕ
  P : Set (Point E)
  positive : 0 < S
  center_mem : c.val ∈ W
  compact : IsCompact P
  convex : GConvex P
  section_mem : ∀ x ∈ P, x.val ∈ W
  contains_ball : ∀ x : Point E, x.val ∈ W →
    dist c x ≤ publicRadius (Geode.eta μ) S → x ∈ P
  dimension : Module.finrank ℝ W ≤ cuts + 1
  radius : Real.sinh S = latitudeContraction (Geode.eta μ) ^ cuts * Real.sinh R
  original : ∀ p ∈ candidateSet W c S, dist o p = R

namespace PublicState

variable {o : Point E} {R μ : ℝ}

def candidates (s : PublicState o R μ) : Set (Point E) := candidateSet s.W s.c s.S

theorem center_in_domain (s : PublicState o R μ) (hη : 0 ≤ Geode.eta μ) : s.c ∈ s.P := by
  apply s.contains_ball s.c s.center_mem
  simpa only [dist_self] using publicRadius_nonneg hη s.positive.le

end PublicState

structure ArchivedContact (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  y : Point E
  z : Point E
  q : Ambient E
  D : ℝ
  positive : 0 < D
  tangent : form E z.val q = 0
  unit : form E q q = 1
  direction_eq : y ≠ z → direction z y = q

namespace ArchivedContact

noncomputable def gradient (a : ArchivedContact E) : Ambient E := by
  classical
  exact if a.y = a.z then a.q else -direction a.y a.z

noncomputable def reply (a : ArchivedContact E) (μ L : ℝ) : ℝ × Ambient E :=
  (L * (μ * a.D + dist a.y a.z), L • a.gradient)

noncomputable def normal (a : ArchivedContact E) (μ : ℝ) (p : Point E) : Ambient E :=
  a.q + μ • direction a.z p

end ArchivedContact

structure ContactSupports {o : Point E} {R μ : ℝ}
    (s : PublicState o R μ) (a : ArchivedContact E) : Prop where
  contact_mem : a.z ∈ s.P
  direction_mem : a.q ∈ s.W
  distance : ∀ p ∈ s.candidates, dist a.z p = a.D
  normal : ∀ p ∈ s.candidates, NormalTo s.P a.z (a.normal μ p)
  strict : ∀ p ∈ s.candidates, form E (a.normal μ p) p.val < 0
  future : ∀ p ∈ s.candidates, ∀ (W' : Submodule ℝ (Ambient E)) (c' : Point E)
    (S' : ℝ) (v' : Ambient E), s.W ≤ W' → c'.val ∈ W' → 0 < S' → S' ≤ s.S →
    IsResidual W' v' → p.val = Real.cosh S' • c'.val + Real.sinh S' • v' →
    ∀ x : Point E, x.val ∈ W' → dist c' x ≤ publicRadius (Geode.eta μ) S' →
      form E (a.normal μ p) x.val ≤ 0

structure StateExtension {o : Point E} {R μ : ℝ}
    (s s' : PublicState o R μ) : Prop where
  space : s.W ≤ s'.W
  radius : s'.S ≤ s.S
  candidates : s'.candidates ⊆ s.candidates
  domain : s.P ⊆ s'.P
  hull : s'.P ⊆ closedGConv (s.P ∪
    {x : Point E | x.val ∈ s'.W ∧ dist s'.c x ≤ publicRadius (Geode.eta μ) s'.S})
  cuts : s'.cuts ≤ s.cuts + 1

theorem StateExtension.refl {o : Point E} {R μ : ℝ} (s : PublicState o R μ) :
    StateExtension s s := by
  refine ⟨le_rfl, le_rfl, Set.Subset.refl _, Set.Subset.refl _, ?_, by omega⟩
  exact (Set.subset_union_left).trans (subset_closedGConv _)

theorem ContactSupports.extend {o : Point E} {R μ : ℝ}
    {s s' : PublicState o R μ} {a : ArchivedContact E}
    (h : ContactSupports s a) (he : StateExtension s s') : ContactSupports s' a := by
  refine ⟨he.domain h.contact_mem, he.space h.direction_mem,
    fun p hp => h.distance p (he.candidates hp), ?_,
    fun p hp => h.strict p (he.candidates hp), ?_⟩
  · intro p hp
    have hpold := he.candidates hp
    obtain ⟨v, hv, _, hrep⟩ := hp
    apply normalTo_iff_lorentz_halfspace.mpr
    refine ⟨(h.normal p hpold).1, ?_⟩
    intro x hx
    apply closedGConv_subset_halfspace (a.normal μ p) ?_ (he.hull hx)
    intro w hw
    rcases hw with hw | hw
    · exact (normalTo_iff_lorentz_halfspace.mp (h.normal p hpold)).2 w hw
    · exact h.future p hpold s'.W s'.c s'.S v he.space s'.center_mem s'.positive
        he.radius hv hrep w hw.1 hw.2
  · intro p hp W' c' S' v' hW hc hS hSS hv hrep x hx hdist
    exact h.future p (he.candidates hp) W' c' S' v' (he.space.trans hW) hc hS
      (hSS.trans he.radius) hv hrep x hx hdist

end Geode.Lorentz
