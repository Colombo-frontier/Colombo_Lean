import Bilevel.CachedPathCap

/-! Actual deterministic cap controller from `ac:thm:cached-upper`.
The input vector sequence is arbitrary, so these invariants hold on every
oracle history, without imposing any accuracy or bounded-sample event.
Construction of those vectors by the stochastic inner procedures is separate.
-/
noncomputable section
open scoped BigOperators
namespace Bilevel.CappedExecution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure State (E : Type*) where
  point : E
  energy : ℝ
  stopped : Bool

def initial (x₀ : E) : State E := ⟨x₀, 0, false⟩

def accept (cap : ℝ) (s : State E) (G : E) : Prop :=
  s.stopped = false ∧ s.energy + ‖G‖^2 ≤ cap

def step (Λ cap : ℝ) (s : State E) (G : E) : State E :=
  if s.stopped then s else
    if s.energy + ‖G‖^2 ≤ cap then
      ⟨s.point - Λ⁻¹ • G, s.energy + ‖G‖^2, false⟩
    else ⟨s.point, s.energy, true⟩

def run (Λ cap : ℝ) (x₀ : E) (G : ℕ → E) : ℕ → State E
  | 0 => initial x₀
  | n+1 => step Λ cap (run Λ cap x₀ G n) (G n)

def executed (Λ cap : ℝ) (x₀ : E) (G : ℕ → E) (n : ℕ) : E := by
  classical
  exact if accept cap (run Λ cap x₀ G n) (G n) then G n else 0

omit [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
theorem initial_energy (x₀ : E) : (initial x₀).energy = 0 := rfl

theorem step_energy_bounds (Λ cap : ℝ) (s : State E) (G : E)
    (hs0 : 0 ≤ s.energy) (hsc : s.energy ≤ cap) :
    0 ≤ (step Λ cap s G).energy ∧ (step Λ cap s G).energy ≤ cap := by
  unfold step
  split
  · exact ⟨hs0, hsc⟩
  · split
    · exact ⟨add_nonneg hs0 (sq_nonneg _), by assumption⟩
    · exact ⟨hs0, hsc⟩

theorem run_energy_bounds (Λ cap : ℝ) (x₀ : E) (G : ℕ → E)
    (hcap : 0 ≤ cap) (n : ℕ) :
    0 ≤ (run Λ cap x₀ G n).energy ∧ (run Λ cap x₀ G n).energy ≤ cap := by
  induction n with
  | zero => exact ⟨le_rfl, hcap⟩
  | succ n ih => exact step_energy_bounds Λ cap _ _ ih.1 ih.2

theorem run_point_step (Λ cap : ℝ) (x₀ : E) (G : ℕ → E) (n : ℕ) :
    (run Λ cap x₀ G (n+1)).point =
      (run Λ cap x₀ G n).point - Λ⁻¹ • executed Λ cap x₀ G n := by
  simp only [run, step, executed, accept]
  by_cases hb : (run Λ cap x₀ G n).stopped = false
  · by_cases he : (run Λ cap x₀ G n).energy + ‖G n‖^2 ≤ cap <;> simp [hb, he]
  · have ht : (run Λ cap x₀ G n).stopped = true := by
      cases hh : (run Λ cap x₀ G n).stopped <;> simp_all
    simp [hb, ht]

theorem run_energy_step (Λ cap : ℝ) (x₀ : E) (G : ℕ → E) (n : ℕ) :
    (run Λ cap x₀ G (n+1)).energy =
      (run Λ cap x₀ G n).energy + ‖executed Λ cap x₀ G n‖^2 := by
  simp only [run, step, executed, accept]
  by_cases hb : (run Λ cap x₀ G n).stopped = false
  · by_cases he : (run Λ cap x₀ G n).energy + ‖G n‖^2 ≤ cap <;> simp [hb, he]
  · have ht : (run Λ cap x₀ G n).stopped = true := by
      cases hh : (run Λ cap x₀ G n).stopped <;> simp_all
    simp [hb, ht]

theorem run_energy_eq_sum (Λ cap : ℝ) (x₀ : E) (G : ℕ → E) (n : ℕ) :
    (run Λ cap x₀ G n).energy =
      ∑ i ∈ Finset.range n, ‖executed Λ cap x₀ G i‖^2 := by
  induction n with
  | zero => simp [run, initial]
  | succ n ih => rw [run_energy_step, Finset.sum_range_succ, ih]

theorem all_history_radius {Λ cap : ℝ} (hΛ : 0 < Λ) (hcap : 0 ≤ cap)
    (x₀ : E) (G : ℕ → E) (n : ℕ) :
    ‖(run Λ cap x₀ G n).point - x₀‖ ≤ Real.sqrt (n * cap) / Λ := by
  have h := CachedPathCap.path_distance_bound (cap := cap) (fun i => (run Λ cap x₀ G i).point)
    (executed Λ cap x₀ G) hΛ n (fun i _ => run_point_step Λ cap x₀ G i)
    (by rw [← run_energy_eq_sum]; exact (run_energy_bounds Λ cap x₀ G hcap n).2)
  simpa [run, initial] using h

/-- On an aborted history the output is the original point, exactly as in the
manuscript. Otherwise it is a selected pre-update point. -/
def output (Λ cap : ℝ) (x₀ : E) (G : ℕ → E) (N index : ℕ) : E :=
  if (run Λ cap x₀ G N).stopped then x₀ else (run Λ cap x₀ G index).point

theorem all_history_output_radius {Λ cap : ℝ} (hΛ : 0 < Λ) (hcap : 0 ≤ cap)
    (x₀ : E) (G : ℕ → E) (N index : ℕ) (hi : index ≤ N) :
    ‖output Λ cap x₀ G N index - x₀‖ ≤ Real.sqrt (N * cap) / Λ := by
  unfold output
  split
  · simp only [sub_self, norm_zero]
    positivity
  · have hb := all_history_radius hΛ hcap x₀ G index
    apply hb.trans
    apply div_le_div_of_nonneg_right _ hΛ.le
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hcap

/-- Gradient norms are bounded even on failed histories. The bound follows
from the original smooth objective and its initial gap, rather than from a
bounded-gradient assumption on the whole domain. -/
theorem all_history_output_gradient [CompleteSpace E]
    (F : E → ℝ) (g : E → E) {Λ cap Δ lower : ℝ}
    (hΛ : 0 < Λ) (hcap : 0 ≤ cap)
    (hg : ∀ z, HasGradientAt F (g z) z)
    (hlip : ∀ z w, ‖g z-g w‖ ≤ Λ * ‖z-w‖)
    (hlower : ∀ z, lower ≤ F z) (x₀ : E) (hgap : F x₀ - lower ≤ Δ)
    (G : ℕ → E) (N index : ℕ) (hi : index ≤ N) :
    ‖g (output Λ cap x₀ G N index)‖ ≤ Real.sqrt (2*Λ*Δ) + Real.sqrt (N*cap) := by
  have hΔ : 0 ≤ Δ := (sub_nonneg.mpr (hlower x₀)).trans hgap
  have hinit := Descent.gradient_sq_le_gap F x₀ (g x₀) Λ lower hΛ
    (InnerContraction.smooth_upper_model F g Λ hg hlip x₀) hlower
  have hinit' : ‖g x₀‖^2 ≤ 2*Λ*Δ :=
    hinit.trans (mul_le_mul_of_nonneg_left hgap (by positivity))
  have hb : ‖g x₀‖ ≤ Real.sqrt (2*Λ*Δ) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hinit'
  have hr := all_history_output_radius hΛ hcap x₀ G N index hi
  have hm := (hlip (output Λ cap x₀ G N index) x₀).trans
    (mul_le_mul_of_nonneg_left hr hΛ.le)
  have he : Λ * (Real.sqrt (N*cap) / Λ) = Real.sqrt (N*cap) := by field_simp
  rw [he] at hm
  have ht : ‖g (output Λ cap x₀ G N index)‖ ≤
      ‖g (output Λ cap x₀ G N index) - g x₀‖ + ‖g x₀‖ := by
    simpa using norm_add_le (g (output Λ cap x₀ G N index)-g x₀) (g x₀)
  linarith

end Bilevel.CappedExecution
