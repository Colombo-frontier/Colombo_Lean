import Bilevel.CappedExecution

/-! The actual cap controller cannot reject a step on the simultaneous
accuracy event. The rejected candidate's hypothetical next point is included
in the smooth descent argument; no bound on it is assumed.
-/
noncomputable section
open scoped BigOperators
namespace Bilevel.CappedGoodEvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem one_step_energy (F : E → ℝ) (g : E → E) {Λ e : ℝ}
    (hΛ : 0 < Λ) (hg : ∀ z, HasGradientAt F (g z) z)
    (hlip : ∀ z w, ‖g z-g w‖ ≤ Λ * ‖z-w‖)
    (x G : E) (herr : ‖G-g x‖^2 ≤ e) :
    ‖G‖^2 + 4*Λ*F (x-Λ⁻¹ • G) ≤ 4*Λ*F x + 4*e := by
  have hd := Descent.inexact_descent F x (g x) G Λ hΛ
    (InnerContraction.smooth_upper_model F g Λ hg hlip x)
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4*Λ)
  have hc : 4*Λ*(F x - ‖g x‖^2/(2*Λ) + ‖G-g x‖^2/(2*Λ)) =
      4*Λ*F x - 2*‖g x‖^2 + 2*‖G-g x‖^2 := by field_simp; ring
  rw [hc] at hm
  have hn := CachedPathCap.norm_sq_le_two G (g x)
  linarith

open CappedExecution

omit [CompleteSpace E] in
theorem step_live_iff (Λ cap : ℝ) (s : State E) (G : E) :
    (step Λ cap s G).stopped = false ↔ s.stopped = false ∧ s.energy+‖G‖^2 ≤ cap := by
  by_cases hs : s.stopped = false
  · by_cases hc : s.energy+‖G‖^2 ≤ cap <;> simp [step, hs, hc]
  · have ht : s.stopped = true := by cases hh : s.stopped <;> simp_all
    simp [step, ht]

omit [CompleteSpace E] in
theorem executed_of_next_live (Λ cap : ℝ) (x₀ : E) (G : ℕ → E) (n : ℕ)
    (hn : (run Λ cap x₀ G (n+1)).stopped = false) :
    executed Λ cap x₀ G n = G n := by
  have ha := (step_live_iff Λ cap (run Λ cap x₀ G n) (G n)).mp hn
  exact if_pos ha

/-- A concrete no-abort theorem for the implemented state machine. Accuracy
is required only at live steps, not after an abort. -/
theorem no_abort_on_good_event (F : E → ℝ) (g : E → E) {Λ Δ lower ε : ℝ}
    (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hg : ∀ z, HasGradientAt F (g z) z)
    (hlip : ∀ z w, ‖g z-g w‖ ≤ Λ * ‖z-w‖)
    (hlower : ∀ z, lower ≤ F z) (x₀ : E) (hgap : F x₀-lower ≤ Δ)
    (G : ℕ → E) (N : ℕ) (hN : 0 < N)
    (hgood : ∀ i < N,
      (run Λ (16*Λ*Δ+N*ε^2) x₀ G i).stopped = false →
      ‖G i-g (run Λ (16*Λ*Δ+N*ε^2) x₀ G i).point‖ ≤ ε/8) :
    ∀ n ≤ N,
      (run Λ (16*Λ*Δ+N*ε^2) x₀ G n).stopped = false ∧
      (run Λ (16*Λ*Δ+N*ε^2) x₀ G n).energy +
        4*Λ*F (run Λ (16*Λ*Δ+N*ε^2) x₀ G n).point ≤
          4*Λ*F x₀ + 4*n*(ε/8)^2 := by
  intro n
  induction n with
  | zero => intro _; simp [run, initial]
  | succ n ih =>
    intro hn
    have hnN : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    obtain ⟨hstop, henergy⟩ := ih (Nat.le_of_lt hnN)
    let cap := 16*Λ*Δ+N*ε^2
    let s := run Λ cap x₀ G n
    have hs : s.stopped = false := hstop
    have herr := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ε/8)).mpr
      (hgood n hnN hstop)
    have hlocal := one_step_energy F g hΛ hg hlip s.point (G n) herr
    have hfloor := mul_le_mul_of_nonneg_left (hlower (s.point-Λ⁻¹ • G n))
      (by positivity : 0 ≤ 4*Λ)
    have hgap' := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 4*Λ)
    have hcand : s.energy+‖G n‖^2 ≤ 4*Λ*Δ+4*(n+1)*(ε/8)^2 := by
      change s.energy+4*Λ*F s.point ≤ _ at henergy
      linarith
    have hn' : (n : ℝ)+1 ≤ N := by exact_mod_cast hn
    have hNN : (0 : ℝ) < N := by exact_mod_cast hN
    have hnmul := mul_le_mul_of_nonneg_right hn' (sq_nonneg ε)
    have hpos : 0 < (N : ℝ)*ε^2 := by positivity
    have hD : 0 ≤ Λ*Δ := mul_nonneg hΛ.le hΔ
    have hsafe : s.energy+‖G n‖^2 ≤ cap := by dsimp [cap]; nlinarith
    change (step Λ cap s (G n)).stopped = false ∧
      (step Λ cap s (G n)).energy + 4*Λ*F (step Λ cap s (G n)).point ≤ _
    simp only [step, hs, Bool.false_eq_true, ↓reduceIte, hsafe]
    constructor
    · trivial
    · change s.energy+4*Λ*F s.point ≤ _ at henergy
      push_cast
      linarith

/-- The actual controller's output has the good-event uniform-index bound,
after proving that the controller accepts every update. -/
theorem good_output_average (F : E → ℝ) (g : E → E) {Λ Δ lower ε : ℝ}
    (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hg : ∀ z, HasGradientAt F (g z) z)
    (hlip : ∀ z w, ‖g z-g w‖ ≤ Λ * ‖z-w‖)
    (hlower : ∀ z, lower ≤ F z) (x₀ : E) (hgap : F x₀-lower ≤ Δ)
    (G : ℕ → E) (N : ℕ) (hN : 0 < N) (horizon : 32*Λ*Δ ≤ N*ε^2)
    (hgood : ∀ i < N,
      (run Λ (16*Λ*Δ+N*ε^2) x₀ G i).stopped = false →
      ‖G i-g (run Λ (16*Λ*Δ+N*ε^2) x₀ G i).point‖ ≤ ε/8) :
    (∑ i ∈ Finset.range N, ‖g (output Λ (16*Λ*Δ+N*ε^2) x₀ G N i)‖)/N ≤ ε/2 := by
  let cap := 16*Λ*Δ+N*ε^2
  have hsafe := no_abort_on_good_event F g hΛ hΔ hε hg hlip hlower x₀ hgap G N hN hgood
  have hx : ∀ i < N, (run Λ cap x₀ G (i+1)).point =
      (run Λ cap x₀ G i).point - Λ⁻¹ • G i := by
    intro i hi
    rw [run_point_step, executed_of_next_live Λ cap x₀ G i (hsafe (i+1) (Nat.succ_le_of_lt hi)).1]
  have hh := CachedPathCap.uniform_output_average F g
    (fun i => (run Λ cap x₀ G i).point) G hΛ hε.le hg hlip hlower hgap N hN horizon hx
    (fun i hi => hgood i hi (hsafe i hi.le).1)
  have hterminal : (run Λ cap x₀ G N).stopped = false := (hsafe N le_rfl).1
  dsimp [cap] at hterminal hh
  simpa only [output, hterminal, Bool.false_eq_true, ↓reduceIte] using hh

end Bilevel.CappedGoodEvent
