import MatchingBounds1005.ReadoutPrefixEvent
import MatchingBounds1005.SourceCalendarIndices

/-! Compressing the full analyst trace to the actual physical queries and
the frozen candidate preserves every stopped-readout prefix bound. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace BigOperators

namespace MatchingBounds1005.ScheduledPrefix
open ChronologicalProjection
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} {m n : ℕ}

theorem readoutEvent_of_prefixEvent_subsequence (xs : Fin n → E)
    (index : Fin m → Fin n) (hindex : StrictMono index)
    (I : ℕ → Submodule ℝ E) (A : Submodule ℝ E) (b : ι → E) (ell : ι → ℕ)
    (hell : ∀ s, ell s ≤ m) (hactive : ∀ s, b s ∈ A)
    (hhidden : ∀ s (hs : 0 < ell s),
      b s ∈ (I (index ⟨ell s - 1, by have := hell s; omega⟩).val)ᗮ)
    {η : ℝ} (hx : xs ∈ prefixEvent I A η) :
    (fun i => xs (index i)) ∈ readoutEvent b ell (2 * η) := by
  intro s hs c
  let j : Fin m := ⟨ell s - 1, by have := hell s; omega⟩
  let t := (index j).val
  let v := synthesis (fun i => xs (index i)) (ell s - 1) c
  have hv : v ∈ prefixSpan (List.ofFn xs) (t + 1) := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    unfold maskedPrefix
    split_ifs with hi
    · apply Submodule.subset_span
      apply List.mem_take_iff_getElem.mpr
      have hij : i ≤ j := hi
      have hit : (index i).val ≤ t := hindex.monotone hij
      refine ⟨(index i).val, ?_, ?_⟩
      · simp only [List.length_ofFn]
        exact lt_min (by omega) (index i).isLt
      · simp only [List.getElem_ofFn]
    · exact Submodule.zero_mem _
  obtain ⟨c', hc'⟩ := (mem_prefix_iff_synthesis xs t v).mp hv
  have h := hx t (b s) (hactive s) (hhidden s hs) c'
  simpa only [hc'] using h

end MatchingBounds1005.ScheduledPrefix

namespace MatchingBounds1005.SourceReferenceProgram
open ScheduledHaar ScheduledPrefix GaussianVector
variable {d N H : ℕ}

def stoppedPrefixLength (P : Parameters d N) (H : ℕ) (s : Fin N) : ℕ :=
  min (H + 1) (P.disclosure s - 1)

theorem readoutEvent_of_full_prefix (P : Parameters d N) (H : ℕ)
    (xs : Fin (commands P H).length → Vec d)
    (I : ℕ → Submodule ℝ (Vec d)) (A : Submodule ℝ (Vec d))
    (hactive : ∀ s, P.b s ∈ A)
    (hhidden : ∀ s t, t < P.disclosure s → P.b s ∈ (I t)ᗮ)
    {η : ℝ} (hx : xs ∈ prefixEvent (fun j => I (commandClock (commands P H) 1 j)) A η) :
    (fun i => xs (observationIndex P H i)) ∈ readoutEvent P.b (stoppedPrefixLength P H) (2 * η) := by
  apply readoutEvent_of_prefixEvent_subsequence xs (observationIndex P H)
    (observationIndex_strictMono P H) (fun j => I (commandClock (commands P H) 1 j)) A
    P.b (stoppedPrefixLength P H) (fun s => min_le_left _ _) hactive ?_ hx
  intro s hs
  dsimp only
  rw [observationIndex_clock]
  apply hhidden
  have hle := min_le_right (H + 1) (P.disclosure s - 1)
  change 0 < min (H + 1) (P.disclosure s - 1) at hs
  change min (H + 1) (P.disclosure s - 1) - 1 + 1 < P.disclosure s
  omega

end MatchingBounds1005.SourceReferenceProgram
