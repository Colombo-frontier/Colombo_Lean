import NCBall.ShadowValue
import NCBall.LinearTranscript

/-! # A concrete clock-based charging and unlocking rule -/

noncomputable section
open MeasureTheory
namespace NCBall

variable (S : Type*) [MeasurableSpace S] (n H : ℕ)

structure RoomQueryPolicy where
  point : (t : ℕ) → LinearHistory S t → Space n
  handle : (t : ℕ) → LinearHistory S t → Fin H
  measurable_point : ∀ t, Measurable (point t)
  measurable_handle : ∀ t, Measurable (handle t)

variable {S n H}

/-- Clock-compatible queries are charged even when their transverse information
is zero. This may unlock earlier and is suitable for a stronger shadow oracle. -/
def shadowCounter (p : RoomQueryPolicy S n H) (ρ : ℝ) (q₀ : ℕ) :
    (t : ℕ) → LinearHistory S t → ℕ
  | 0, _ => 0
  | t + 1, h =>
      let k := shadowCounter p ρ q₀ t h.1
      if |p.point t h.1 0 - 4 * ρ * (k / q₀ : ℕ)| ≤ ρ then k + 1 else k

def shadowStage (p : RoomQueryPolicy S n H) (ρ : ℝ) (q₀ t : ℕ)
    (h : LinearHistory S t) : ℕ := shadowCounter p ρ q₀ t h / q₀

theorem shadowCounter_le (p : RoomQueryPolicy S n H) (ρ : ℝ) (q₀ t : ℕ)
    (h : LinearHistory S t) : shadowCounter p ρ q₀ t h ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih h.1
    simp only [shadowCounter]
    split_ifs <;> omega

theorem shadowCounter_step (p : RoomQueryPolicy S n H) (ρ : ℝ) (q₀ t : ℕ)
    (h : LinearHistory S (t + 1)) :
    shadowCounter p ρ q₀ t h.1 ≤ shadowCounter p ρ q₀ (t + 1) h ∧
      shadowCounter p ρ q₀ (t + 1) h ≤ shadowCounter p ρ q₀ t h.1 + 1 := by
  simp only [shadowCounter]
  split_ifs <;> omega

theorem shadowStage_unfinished (p : RoomQueryPolicy S n H) (ρ : ℝ) {q₀ M t : ℕ}
    (hq : 0 < q₀) (ht : t < M * q₀) (h : LinearHistory S t) :
    shadowStage p ρ q₀ t h < M := by
  rw [shadowStage, Nat.div_lt_iff_lt_mul hq]
  exact (shadowCounter_le p ρ q₀ t h).trans_lt ht

theorem shadowCounter_measurable (p : RoomQueryPolicy S n H) (ρ : ℝ) (q₀ t : ℕ) :
    Measurable (shadowCounter p ρ q₀ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hc := ih.comp (measurable_fst : Measurable (Prod.fst : LinearHistory S (t + 1) → _))
    have hd := (measurable_of_countable (fun k : ℕ => k / q₀)).comp hc
    have hp : Measurable (fun h : LinearHistory S (t + 1) => p.point t h.1) :=
      (p.measurable_point t).comp measurable_fst
    have hm : Measurable (fun h : LinearHistory S (t + 1) =>
        |p.point t h.1 0 - 4 * ρ * (shadowCounter p ρ q₀ t h.1 / q₀ : ℕ)|) := by fun_prop
    exact Measurable.ite (measurableSet_le hm measurable_const) (hc.add_const 1) hc

theorem shadowStage_measurable (p : RoomQueryPolicy S n H) (ρ : ℝ) (q₀ t : ℕ) :
    Measurable (shadowStage p ρ q₀ t) :=
  (measurable_of_countable (fun k : ℕ => k / q₀)).comp (shadowCounter_measurable p ρ q₀ t)

end NCBall
