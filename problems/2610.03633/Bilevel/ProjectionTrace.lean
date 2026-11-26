import Bilevel.ProjectionEnergy

/-! The energy envelope holds for every interleaving of queries and revelations. -/
noncomputable section
namespace Bilevel.ProjectionTrace
open ProjectionEnergy

/-- The scalar upper estimates produced by actual projection geometry. -/
inductive Trace (b : ℝ) : ℕ → ℕ → ℝ → Prop
  | initial : Trace b 0 0 0
  | query {q r : ℕ} {e e' : ℝ} : Trace b q r e → 0 ≤ e' → e' ≤ e + b → Trace b (q+1) r e'
  | reveal {q r : ℕ} {e e' : ℝ} : Trace b q r e → 0 ≤ e' → e' ≤ e / (1-e) → Trace b q (r+1) e'

theorem nonneg {b : ℝ} {q r : ℕ} {e : ℝ} (h : Trace b q r e) : 0 ≤ e := by
  cases h with
  | initial => exact le_rfl
  | query _ he _ => exact he
  | reveal _ he _ => exact he

theorem envelope_bound {b : ℝ} (hb : 0 ≤ b) {q r : ℕ} {e : ℝ}
    (h : Trace b q r e) (hcap : (r : ℝ) * ((q : ℝ) * b) < 1) :
    e ≤ envelope ((q : ℝ) * b) r := by
  induction h with
  | initial => simp [envelope]
  | @query q r e e' h he' hstep ih =>
    have hcap' : (r : ℝ) * ((q : ℝ) * b) < 1 := by
      push_cast at hcap
      nlinarith [mul_nonneg (Nat.cast_nonneg r) hb]
    have hq : 0 ≤ (q : ℝ) * b := mul_nonneg (Nat.cast_nonneg q) hb
    have hc : (r : ℝ) * ((q : ℝ) * b + b) < 1 := by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hcap
    have hs := query_step ((q : ℝ) * b) r b hq (Nat.cast_nonneg r) hb hc
    have hh := ih hcap'
    have hout : e' ≤ envelope ((q : ℝ) * b + b) r :=
      hstep.trans ((add_le_add_right hh b).trans hs)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hout
  | @reveal q r e e' h he' hstep ih =>
    have hq : 0 ≤ (q : ℝ) * b := mul_nonneg (Nat.cast_nonneg q) hb
    have hc : ((r : ℝ) + 1) * ((q : ℝ) * b) < 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcap
    have hcap' : (r : ℝ) * ((q : ℝ) * b) < 1 := by nlinarith
    have hh := ih hcap'
    have he := (before_revelation ((q : ℝ) * b) r hq hc).2
    have hs := revelation_monotone e (envelope ((q : ℝ) * b) r) hh he
    rw [revelation_step ((q : ℝ) * b) r hq hc] at hs
    simpa only [Nat.cast_add, Nat.cast_one] using hstep.trans hs

theorem twice_total_query_energy {b : ℝ} (hb : 0 ≤ b) {q r : ℕ} {e : ℝ}
    (h : Trace b q r e) (hcap : (r : ℝ) * ((q : ℝ) * b) ≤ 1/2) :
    e ≤ 2 * (q : ℝ) * b := by
  have hh := envelope_bound hb h (show (r : ℝ) * ((q : ℝ) * b) < 1 by linarith)
  have hs := envelope_le_twice ((q : ℝ) * b) r
    (mul_nonneg (Nat.cast_nonneg q) hb) hcap
  nlinarith [hh.trans hs]

end Bilevel.ProjectionTrace
