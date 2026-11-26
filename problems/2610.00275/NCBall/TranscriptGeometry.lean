import NCBall.LinearTranscript
import NCBall.ProjectionEnergy

/-! # Geometry of the directions in an actual adaptive transcript -/

noncomputable section
open scoped InnerProductSpace
namespace NCBall

variable {S E : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

def linearQueryTrace (p : LinearQueryPolicy S E) :
    (t : ℕ) → LinearHistory S t → List E
  | 0, _ => []
  | t + 1, h => p.query t h.1 :: linearQueryTrace p t h.1

theorem linearPosteriorProjection_fixed_iff (p : LinearQueryPolicy S E)
    (t : ℕ) (h : LinearHistory S t) (x : E) :
    linearPosteriorProjection p t h x = x ↔
      ∀ a ∈ linearQueryTrace p t h, ⟪a, x⟫_ℝ = 0 := by
  induction t with
  | zero => simp [linearPosteriorProjection, linearQueryTrace]
  | succ t ih =>
    change residualUpdate (linearPosteriorProjection p t h.1) (p.query t h.1) x = x ↔ _
    rw [residualUpdate_fixed_iff (linearPosteriorProjection_isProjection p t h.1), ih]
    simp only [linearQueryTrace, List.mem_cons, forall_eq_or_imp]
    exact and_comm

theorem linearPosteriorProjection_kills_query (p : LinearQueryPolicy S E)
    (t : ℕ) (h : LinearHistory S t) {a : E} (ha : a ∈ linearQueryTrace p t h) :
    linearPosteriorProjection p t h a = 0 := by
  let Q := linearPosteriorProjection p t h
  have hQ := linearPosteriorProjection_isProjection p t h
  have hx : ∀ b ∈ linearQueryTrace p t h, ⟪b, Q a⟫_ℝ = 0 :=
    (linearPosteriorProjection_fixed_iff p t h (Q a)).mp (hQ.1 a)
  have he := hQ.2 a (Q a)
  rw [hQ.1, hx a ha] at he
  exact (inner_self_eq_zero).mp he

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem linearQueryTrace_length (p : LinearQueryPolicy S E)
    (t : ℕ) (h : LinearHistory S t) : (linearQueryTrace p t h).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [linearQueryTrace, List.length_cons] using congrArg Nat.succ (ih h.1)

end NCBall
