import NCConcave16991.MoreauGradient

/-! # The actual Moreau envelope, its gradient, and the zero-query threshold -/

open Set
open scoped InnerProductSpace

namespace NCConcave16991

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def moreauEnvelope (f : E → ℝ) (L : ℝ) (c : E) : ℝ :=
  sInf (range (proxObjective f L c))

theorem moreauEnvelope_eq_minimizedValue {f : E → ℝ} {L : ℝ} {P : E → E}
    (hP : ∀ c, IsProxPoint f L c (P c)) (c : E) :
    moreauEnvelope f L c = minimizedValue f L P c := by
  have hb : BddBelow (range (proxObjective f L c)) := by
    refine ⟨proxObjective f L c (P c), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hP c x
  apply le_antisymm
  · exact csInf_le hb (mem_range_self (P c))
  · exact le_csInf (range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hP c x)

theorem moreauEnvelope_hasGradientAt [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} {P : E → E}
    (hL : 0 < L) (hf : WeaklyConvex L f)
    (hP : ∀ c, IsProxPoint f L c (P c)) (c : E) :
    HasGradientAt (moreauEnvelope f L) (proxResidual L c (P c)) c := by
  have he : moreauEnvelope f L = minimizedValue f L P :=
    funext (moreauEnvelope_eq_minimizedValue hP)
  rw [he]
  exact minimizedValue_hasGradientAt hL hf hP c

noncomputable def proximalMap [ProperSpace E] {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : Continuous f) (hb : BddBelow (range f)) (c : E) : E :=
  Classical.choose (exists_proxPoint hL hf hb c)

theorem proximalMap_spec [ProperSpace E] {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : Continuous f) (hb : BddBelow (range f)) (c : E) :
    IsProxPoint f L c (proximalMap hL hf hb c) :=
  Classical.choose_spec (exists_proxPoint hL hf hb c)

/-- The Appendix A.2 gradient formula for the actual infimum-defined envelope. -/
theorem moreauEnvelope_gradient_formula [ProperSpace E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hf : Continuous f)
    (hb : BddBelow (range f)) (hw : WeaklyConvex L f) (c : E) :
    HasGradientAt (moreauEnvelope f L)
      ((2 * L) • (c - proximalMap hL hf hb c)) c :=
  moreauEnvelope_hasGradientAt hL hw (proximalMap_spec hL hf hb) c

theorem moreauEnvelope_initial_gradient_sq [ProperSpace E] [CompleteSpace E]
    {f : E → ℝ} {L Δ : ℝ} (hL : 0 < L) (hf : Continuous f)
    (hb : BddBelow (range f)) (hw : WeaklyConvex L f) {c : E}
    (hgap : f c - sInf (range f) ≤ Δ) :
    ‖gradient (moreauEnvelope f L) c‖ ^ 2 ≤ 4 * L * Δ := by
  have hg := moreauEnvelope_gradient_formula hL hf hb hw c
  rw [hg.gradient]
  apply proxResidual_gap hL.le (proximalMap_spec hL hf hb c)
  have hl : sInf (range f) ≤ f (proximalMap hL hf hb c) :=
    csInf_le hb (mem_range_self _)
  linarith

theorem moreauEnvelope_zero_query [ProperSpace E] [CompleteSpace E]
    {f : E → ℝ} {L Δ ε : ℝ} (hL : 0 < L) (hf : Continuous f)
    (hb : BddBelow (range f)) (hw : WeaklyConvex L f) {c : E}
    (hgap : f c - sInf (range f) ≤ Δ)
    (hsmall : L * Δ / ε ^ 2 ≤ 1 / 4) (hεpos : 0 < ε) :
    ‖gradient (moreauEnvelope f L) c‖ ≤ ε := by
  have hh := (div_le_iff₀ (sq_pos_of_pos hεpos)).mp hsmall
  have hg := moreauEnvelope_initial_gradient_sq hL hf hb hw hgap
  nlinarith [norm_nonneg (gradient (moreauEnvelope f L) c)]

/-- Weak convexity is preserved by a finite-valued supremum of sections. -/
theorem weaklyConvex_sSup {ι : Type*} [Nonempty ι] {f : ι → E → ℝ} {L : ℝ}
    (hf : ∀ i, WeaklyConvex L (f i)) (hb : ∀ x, BddAbove (range (fun i ↦ f i x))) :
    WeaklyConvex L (fun x ↦ sSup (range (fun i ↦ f i x))) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb' hab
  simp only [smul_eq_mul]
  have hh : sSup (range (fun i ↦ f i (a • x + b • y))) ≤
      a * (sSup (range (fun i ↦ f i x)) + L / 2 * ‖x‖ ^ 2) +
      b * (sSup (range (fun i ↦ f i y)) + L / 2 * ‖y‖ ^ 2) -
      L / 2 * ‖a • x + b • y‖ ^ 2 := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨i, rfl⟩
    have hc := (hf i).2 (mem_univ x) (mem_univ y) ha hb' hab
    simp only [smul_eq_mul] at hc
    have hix := mul_le_mul_of_nonneg_left (le_csSup (hb x) (mem_range_self i)) ha
    have hiy := mul_le_mul_of_nonneg_left (le_csSup (hb y) (mem_range_self i)) hb'
    linarith
  linarith

end NCConcave16991
