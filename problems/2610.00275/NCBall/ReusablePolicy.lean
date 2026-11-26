import NCBall.HandleSpan
import NCBall.AdaptivePosterior

/-! # Measurable policies with adaptively reused sample handles -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace NCBall

variable (S F : Type*) [MeasurableSpace S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] (H : ℕ)

structure ReusableQueryPolicy where
  handle : (t : ℕ) → LinearHistory S t → Fin H
  direction : (t : ℕ) → LinearHistory S t → F
  measurable_handle : ∀ t, Measurable (handle t)
  measurable_direction : ∀ t, Measurable (direction t)

variable {S F H}

attribute [local irreducible] noisyHandleDirection

omit [FiniteDimensional ℝ F] in
theorem reusable_query_measurable (p : ReusableQueryPolicy S F H) (σ : ℝ) (t : ℕ) :
    Measurable (fun h : LinearHistory S t =>
      noisyHandleDirection F σ (p.handle t h) (p.direction t h)) := by
  have hm : Measurable (fun ah : F × Fin H => noisyHandleDirection F σ ah.2 ah.1) := by
    apply measurable_from_prod_countable
    intro h
    exact (noisyHandleDirection F σ h).continuous.measurable
  exact hm.comp ((p.measurable_direction t).prodMk (p.measurable_handle t))

def ReusableQueryPolicy.toLinear (p : ReusableQueryPolicy S F H) (σ : ℝ) :
    LinearQueryPolicy S (HandleLatent F H) where
  query t h := noisyHandleDirection F σ (p.handle t h) (p.direction t h)
  measurable_query := reusable_query_measurable p σ

def reusableQueryTrace (p : ReusableQueryPolicy S F H) :
    (t : ℕ) → LinearHistory S t → List (Fin H × F)
  | 0, _ => []
  | t + 1, h => (p.handle t h.1, p.direction t h.1) :: reusableQueryTrace p t h.1

omit [FiniteDimensional ℝ F] in
theorem reusableQueryTrace_map (p : ReusableQueryPolicy S F H) (σ : ℝ)
    (t : ℕ) (h : LinearHistory S t) :
    (reusableQueryTrace p t h).map (fun q => noisyHandleDirection F σ q.1 q.2) =
      linearQueryTrace (p.toLinear σ) t h := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [reusableQueryTrace, List.map_cons, linearQueryTrace, ih]; rfl

/-- No restrictions on repetition, adaptivity, or the length or norm of the
queried direction are needed for this information bound. -/
theorem reusable_query_innovation_bound (p : ReusableQueryPolicy S F H)
    (σ : ℝ) (hσ : 0 < σ) (t : ℕ) (h : LinearHistory S t) :
    ‖hiddenBlock F H (normalizedInnovation (linearPosteriorProjection (p.toLinear σ) t h)
      ((p.toLinear σ).query t h))‖ ^ 2 ≤ 1 / σ ^ 2 := by
  apply repeated_handle_innovation_bound σ hσ (reusableQueryTrace p t h)
    (linearPosteriorProjection (p.toLinear σ) t h)
    (linearPosteriorProjection_isProjection (p.toLinear σ) t h)
  intro x
  rw [linearPosteriorProjection_fixed_iff, ← reusableQueryTrace_map]
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro he q hq
    exact he _ q hq rfl
  · intro he a q hq ha
    subst a
    exact he q hq

end NCBall
