import NCBall.OracleTranscript

/-! # Recovering the fixed random seed from any recorded history -/

namespace NCBall
open MeasureTheory

def historySeed {S : Type*} : (t : ℕ) → LinearHistory S t → S
  | 0, h => h
  | t + 1, h => historySeed t h.1

theorem historySeed_measurable {S : Type*} [MeasurableSpace S] (t : ℕ) :
    Measurable (@historySeed S t) := by
  induction t with
  | zero => exact measurable_id
  | succ t ih => exact ih.comp measurable_fst

theorem oracleTranscript_seed {S Ω : Type*}
    (reply : (t : ℕ) → LinearHistory S t → Ω → ℝ) (t : ℕ) (w : S × Ω) :
    historySeed t (oracleTranscript reply t w) = w.1 := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

end NCBall
