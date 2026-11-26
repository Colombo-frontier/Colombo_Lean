import MatchingBounds1005.SequentialPosterior
import MatchingBounds1005.InnovationGaussianKL

/-!
# Accumulating actual adaptive observation rows

A fixed finite array stores one block per physical query. A new block is
inserted only at its own round; previous blocks are retained and future
blocks are zero. The resulting measurable row protocol satisfies the
posterior theorem's nested-span requirement by construction.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace MatchingBounds1005.AccumulatedRows
open GaussianVector GaussianFitter AdaptiveGaussian PosteriorGaussian SequentialPosterior

variable {Ω : Type*} [MeasurableSpace Ω] {d H r : ℕ}

def slot (i : Fin (H * r)) : Fin H := (finProdFinEquiv.symm i).1
def coordinate (i : Fin (H * r)) : Fin r := (finProdFinEquiv.symm i).2

def accumulated (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec d) :
    (n : ℕ) → History Ω (H * r) n → Fin (H * r) → Vec d
  | 0, h, i => if (slot i).val = 0 then current 0 h (coordinate i) else 0
  | n + 1, h, i => if (slot i).val = n + 1 then current (n + 1) h (coordinate i)
      else accumulated current n h.1 i

theorem accumulated_future (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec d)
    (n : ℕ) (h : History Ω (H * r) n) (i : Fin (H * r)) (hi : n < (slot i).val) :
    accumulated current n h i = 0 := by
  induction n with
  | zero => exact if_neg (Nat.ne_of_gt hi)
  | succ n ih =>
      rw [accumulated, if_neg (Nat.ne_of_gt hi)]
      exact ih h.1 (Nat.lt_of_succ_lt hi)

theorem accumulated_current (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec d)
    (n : Fin H) (h : History Ω (H * r) n.val) (i : Fin r) :
    accumulated current n.val h (finProdFinEquiv (n, i)) = current n.val h i := by
  have hs : (slot (finProdFinEquiv (n, i))).val = n.val := by
    simp only [slot, Equiv.symm_apply_apply]
  have hc : coordinate (finProdFinEquiv (n, i)) = i := by
    simp only [coordinate, Equiv.symm_apply_apply]
  have hcurrent (j : ℕ) (h : History Ω (H * r) j) (idx : Fin (H * r))
      (hj : (slot idx).val = j) : accumulated current j h idx = current j h (coordinate idx) := by
    cases j with
    | zero => exact if_pos hj
    | succ k => exact if_pos hj
  rw [hcurrent n.val h _ hs, hc]

theorem accumulated_measurable (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec d)
    (hc : ∀ n i, Measurable (fun h => current n h i)) (n : ℕ) (i : Fin (H * r)) :
    Measurable (fun h => accumulated current n h i) := by
  induction n with
  | zero =>
      by_cases hi : (slot i).val = 0
      · simpa only [accumulated, if_pos hi] using hc 0 (coordinate i)
      · simpa only [accumulated, if_neg hi] using (measurable_const : Measurable (fun _ : Ω => (0 : Vec d)))
  | succ n ih =>
      by_cases hi : (slot i).val = n + 1
      · simpa only [accumulated, if_pos hi] using hc (n + 1) (coordinate i)
      · simpa only [accumulated, if_neg hi] using ih.comp measurable_fst

theorem accumulated_nested (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec d)
    (n : ℕ) (h : History Ω (H * r) n) :
    exposure (accumulated current) n h ≤ Submodule.span ℝ (Set.range (accumulated current n h)) := by
  cases n with
  | zero => exact bot_le
  | succ n =>
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : (slot i).val = n + 1
      · rw [accumulated_future current n h.1 i (by omega)]
        exact Submodule.zero_mem _
      · have heq : accumulated current n h.1 i = accumulated current (n + 1) h i := by
          rw [accumulated, if_neg hi]
        rw [heq]
        exact Submodule.subset_span ⟨i, rfl⟩

def protocol (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec d)
    (hc : ∀ n i, Measurable (fun h => current n h i)) : RowProtocol Ω d (H * r) where
  rows := accumulated current
  measurable_rows := accumulated_measurable current hc
  nested := accumulated_nested current

theorem current_response (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec d)
    (n : Fin H) (h : History Ω (H * r) n.val) (x : Vec d) (i : Fin r) :
    rowResponse (accumulated current n.val h) x (finProdFinEquiv (n, i)) =
      rowResponse (current n.val h) x i := by
  unfold rowResponse
  rw [accumulated_current]

def Consistent (rows : (n : ℕ) → History Ω (H * r) n → Fin (H * r) → Vec d) :
    (n : ℕ) → History Ω (H * r) n → Prop
  | 0, _ => True
  | n + 1, h => rowResponse (rows n h.1) (fitter (rows n h.1) h.2) = h.2

/-- Every newly generated raw observation array is feasible for its genuine
rows, including zero or linearly dependent rows. -/
theorem consistent_update (rows : (n : ℕ) → History Ω (H * r) n → Fin (H * r) → Vec d)
    (n : ℕ) (h : History Ω (H * r) n) (x : Vec d) :
    Consistent rows (n + 1) (h, rowResponse (rows n h) x) := fitter_exact (rows n h) x

attribute [local irreducible] projection fitter rowResponse Submodule.span Submodule.orthogonal

/-- A fresh residual reproduces the entire previous raw response exactly.
The consistency premise is proved for every generated update above. -/
theorem replay_previous (rows : (n : ℕ) → History Ω (H * r) n → Fin (H * r) → Vec d)
    (n : ℕ) (h : History Ω (H * r) (n + 1)) (hh : Consistent rows (n + 1) h)
    (residual : Vec d) :
    rowResponse (rows n h.1)
      (fittedMean rows (n + 1) h + projection (exposure rows (n + 1) h)ᗮ residual) = h.2 := by
  let K := Submodule.span ℝ (Set.range (rows n h.1))
  have hm : fitter (rows n h.1) h.2 ∈ K := fitter_mem_span _ _
  have hp : projection K (fitter (rows n h.1) h.2 + projection Kᗮ residual) =
      fitter (rows n h.1) h.2 := by
    rw [map_add, projection_of_mem K _ hm,
      (InnovationGaussianKL.projection_zero_iff K _).mpr (InnovationGaussianKL.projection_mem Kᗮ residual), add_zero]
  change rowResponse (rows n h.1) (fitter (rows n h.1) h.2 + projection Kᗮ residual) = h.2
  rw [← response_projection (rows n h.1) (fitter (rows n h.1) h.2 + projection Kᗮ residual), hp]
  exact hh

end MatchingBounds1005.AccumulatedRows
