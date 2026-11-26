import MatchingBounds1005.AccumulatedRows

/-!
# Decoding physical responses from accumulated finite histories

The policy sees one raw response block per query. Its initial seed is an
explicit measurable view of the joint seed, so undisclosed latent variables
are not made available by retaining them in the KL comparison.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.ResponseHistory
open SequentialPosterior AccumulatedRows GaussianVector GaussianFitter

variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W] {H r : ℕ}

def currentBlock (n : ℕ) (y : Fin (H * r) → ℝ) : Fin r → ℝ :=
  fun i => if hn : n < H then y (finProdFinEquiv (⟨n, hn⟩, i)) else 0

theorem currentBlock_measurable (n : ℕ) : Measurable (currentBlock (H := H) (r := r) n) := by
  by_cases hn : n < H
  · apply measurable_pi_lambda
    intro i
    simpa only [currentBlock, dif_pos hn] using
      (measurable_pi_apply (finProdFinEquiv (⟨n, hn⟩, i)))
  · apply measurable_pi_lambda
    intro i
    simpa only [currentBlock, dif_neg hn] using
      (measurable_const : Measurable (fun _ : Fin (H * r) → ℝ => (0 : ℝ)))

def decode (seedView : Ω → W) : (n : ℕ) → History Ω (H * r) n → History W r n
  | 0, h => seedView h
  | n + 1, h => (decode seedView n h.1, currentBlock n h.2)

theorem decode_measurable (seedView : Ω → W) (hv : Measurable seedView) (n : ℕ) :
    Measurable (decode (H := H) (r := r) seedView n) := by
  induction n with
  | zero => exact hv
  | succ n ih => exact (ih.comp measurable_fst).prodMk ((currentBlock_measurable n).comp measurable_snd)

theorem decode_update {d : ℕ}
    (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec d) (seedView : Ω → W)
    (n : Fin H) (h : History Ω (H * r) n.val) (x : Vec d) :
    decode seedView (n.val + 1) (h, rowResponse (accumulated current n.val h) x) =
      (decode seedView n.val h, rowResponse (current n.val h) x) := by
  change (decode seedView n.val h, currentBlock n.val (rowResponse (accumulated current n.val h) x)) = _
  apply congrArg (fun y : Fin r → ℝ => (decode seedView n.val h, y))
  funext i
  simp only [decode, currentBlock, dif_pos n.isLt]
  exact current_response current n h x i

end MatchingBounds1005.ResponseHistory
