import NCConcave16991.MoreauEnvelope
import NCConcave16991.UpperRecurrence

/-! # Descent for the actual infimum-defined Moreau envelope -/

open Set
open scoped BigOperators

namespace NCConcave16991

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem proxObjective_bddBelow {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hb : BddBelow (range f)) (c : E) : BddBelow (range (proxObjective f L c)) := by
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := ha (mem_range_self x)
  dsimp [proxObjective]
  linarith [mul_nonneg hL (sq_nonneg ‖x - c‖)]

theorem moreauEnvelope_le_objective {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hb : BddBelow (range f)) (c x : E) :
    moreauEnvelope f L c ≤ f x + L * ‖x - c‖ ^ 2 :=
  csInf_le (proxObjective_bddBelow hL hb c) (mem_range_self x)

theorem inf_le_moreauEnvelope {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hb : BddBelow (range f)) (c : E) :
    sInf (range f) ≤ moreauEnvelope f L c := by
  apply le_csInf (range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hx : sInf (range f) ≤ f x := csInf_le hb (mem_range_self x)
  dsimp [proxObjective]
  linarith [mul_nonneg hL (sq_nonneg ‖x - c‖)]

theorem moreauEnvelope_le_value {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hb : BddBelow (range f)) (c : E) : moreauEnvelope f L c ≤ f c := by
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
    moreauEnvelope_le_objective hL hb c c

theorem moreauEnvelope_eq_proxObjective {f : E → ℝ} {L : ℝ} {c p : E}
    (hp : IsProxPoint f L c p) :
    moreauEnvelope f L c = f p + L * ‖p - c‖ ^ 2 := by
  have hb : BddBelow (range (proxObjective f L c)) := by
    refine ⟨proxObjective f L c p, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hp x
  apply le_antisymm (csInf_le hb (mem_range_self p))
  exact le_csInf (range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hp x)

/-- The exact source B descent inequality comes from evaluating the next
envelope at the current true proximal point. No descent premise is assumed. -/
theorem moreauEnvelope_proximal_descent {f : E → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hb : BddBelow (range f)) {c p : E}
    (hp : IsProxPoint f L c p) (next : E) :
    moreauEnvelope f L next ≤ moreauEnvelope f L c - L * ‖p - c‖ ^ 2 +
      L * ‖next - p‖ ^ 2 := by
  have hn := moreauEnvelope_le_objective hL hb next p
  rw [moreauEnvelope_eq_proxObjective hp, norm_sub_rev next p]
  linarith

theorem moreauEnvelope_proximal_descent_sum {f : E → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hb : BddBelow (range f)) (c p : ℕ → E)
    (hp : ∀ t, IsProxPoint f L (c t) (p t)) (S : ℕ) :
    L * (∑ t ∈ Finset.range S, ‖p t - c t‖ ^ 2) ≤
      f (c 0) - sInf (range f) +
        L * ∑ t ∈ Finset.range S, ‖c (t + 1) - p t‖ ^ 2 := by
  have ht := descent_telescopes (fun t ↦ moreauEnvelope f L (c t))
    (fun t ↦ ‖p t - c t‖ ^ 2) (fun t ↦ ‖c (t + 1) - p t‖ ^ 2) L
    (fun t ↦ moreauEnvelope_proximal_descent hL hb (hp t) (c (t + 1))) S
  have hl := inf_le_moreauEnvelope hL hb (c S)
  have hu := moreauEnvelope_le_value hL hb (c 0)
  linarith

/-- Uniform value perturbations transfer the genuine initial infimum gap. -/
theorem infimum_gap_of_uniform_comparison {f g : E → ℝ} {r Δ : ℝ}
    (hf : BddBelow (range f)) (hg : BddBelow (range g))
    (hcompare : ∀ x, f x - r ≤ g x ∧ g x ≤ f x) {c : E}
    (hgap : f c - sInf (range f) ≤ Δ) :
    g c - sInf (range g) ≤ Δ + r := by
  have hinf : sInf (range f) - r ≤ sInf (range g) := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    have hx : sInf (range f) ≤ f x := csInf_le hf (mem_range_self x)
    have hc := (hcompare x).1
    linarith
  have hc := (hcompare c).2
  linarith

end NCConcave16991
