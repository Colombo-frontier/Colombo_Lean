import MatchingBounds1005.HiddenProjection
import MatchingBounds1005.ScheduledContainment

/-! # Scheduled hidden projections for every actual query prefix

This deterministic connector preserves the pre-response calendar: the first
`t+1` latent queries are bounded using `I t`. It also transports the actual
prefix span back through the physical orthogonal coordinate map.
-/

noncomputable section
open scoped InnerProductSpace
open MatchingBounds1005.ScheduledHaar

namespace MatchingBounds1005.ChronologicalProjection

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def prefixSpan (xs : List E) (n : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ {x | x ∈ xs.take n}

omit [FiniteDimensional ℝ E] in
theorem chronological_prefix_mem (xs : List E) (I : ℕ → Submodule ℝ E) (N : Submodule ℝ E)
    (hmono : ∀ t, I t ≤ I (t + 1)) (hc : ChronologicalIn I N xs)
    (t : ℕ) (x : E) (hx : x ∈ xs.take (t + 1)) : x ∈ I t ⊔ N := by
  induction xs generalizing I t with
  | nil => simp at hx
  | cons y ys ih =>
    cases t with
    | zero =>
      have he : x = y := by simpa using hx
      subst x
      exact hc.1
    | succ t =>
      simp only [List.take_succ_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (sup_le_sup_right ((monotone_nat_of_le_succ hmono) (Nat.zero_le (t + 1))) N) hc.1
      · exact ih (fun j => I (j + 1)) (fun j => hmono (j + 1)) hc.2 t hx

omit [FiniteDimensional ℝ E] in
theorem chronological_prefix_le (xs : List E) (I : ℕ → Submodule ℝ E) (N : Submodule ℝ E)
    (hmono : ∀ t, I t ≤ I (t + 1)) (hc : ChronologicalIn I N xs) (t : ℕ) :
    prefixSpan xs (t + 1) ≤ I t ⊔ N := by
  apply Submodule.span_le.mpr
  intro x hx
  exact chronological_prefix_mem xs I N hmono hc t x hx

theorem projection_norm_mono (U V : Submodule ℝ E) (h : U ≤ V) (x : E) :
    ‖U.orthogonalProjection x‖ ≤ ‖V.orthogonalProjection x‖ := by
  have hc := Submodule.orthogonalProjection_orthogonalProjection_of_le h x
  calc
    _ = ‖U.orthogonalProjection (V.orthogonalProjection x)‖ := congrArg norm hc.symm
    _ ≤ ‖U.orthogonalProjection‖ * ‖V.orthogonalProjection x‖ := U.orthogonalProjection.le_opNorm _
    _ ≤ _ := by
      simpa using (mul_le_mul_of_nonneg_right U.orthogonalProjection_norm_le
        (norm_nonneg (V.orthogonalProjection x)))

/-- Every query prefix satisfies the hidden-direction estimate on the same
global cyclic-angle event. -/
theorem hidden_prefix_bound (xs : List E) (I : ℕ → Submodule ℝ E) (A N : Submodule ℝ E)
    (hmono : ∀ t, I t ≤ I (t + 1)) (hc : ChronologicalIn I N xs)
    (hIA : ∀ t, I t ≤ A) {η : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hangle : ∀ a ∈ A, ‖N.orthogonalProjection a‖ ≤ η * ‖a‖)
    (t : ℕ) (a : E) (ha : a ∈ A) (hhidden : a ∈ (I t)ᗮ) :
    ‖(prefixSpan xs (t + 1)).orthogonalProjection a‖ ≤ 2 * η * ‖a‖ :=
  (projection_norm_mono _ _ (chronological_prefix_le xs I N hmono hc t) a).trans
    (MatchingBounds1005.hidden_projection_bound A (I t) N η hη hηhalf
      (hIA t) hangle a ha hhidden)

omit [FiniteDimensional ℝ E] in
theorem prefixSpan_map (U : E ≃ₗᵢ[ℝ] E) (xs : List E) (n : ℕ) :
    prefixSpan (xs.map U) n = (prefixSpan xs n).map U.toLinearEquiv.toLinearMap := by
  rw [prefixSpan, prefixSpan, Submodule.map_span]
  congr 1
  ext x
  simp [← List.map_take]

/-- Physical Haar coordinates preserve the actual span projection norm. -/
theorem hidden_physical_prefix_bound (U : E ≃ₗᵢ[ℝ] E)
    (xs : List E) (I : ℕ → Submodule ℝ E) (A N : Submodule ℝ E)
    (hmono : ∀ t, I t ≤ I (t + 1)) (hc : ChronologicalIn I N xs)
    (hIA : ∀ t, I t ≤ A) {η : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hangle : ∀ a ∈ A, ‖N.orthogonalProjection a‖ ≤ η * ‖a‖)
    (t : ℕ) (a : E) (ha : a ∈ A) (hhidden : a ∈ (I t)ᗮ) :
    ‖(prefixSpan (xs.map U) (t + 1)).orthogonalProjection (U a)‖ ≤ 2 * η * ‖a‖ := by
  rw [prefixSpan_map]
  have he := U.toLinearIsometry.map_orthogonalProjection (prefixSpan xs (t + 1)) a
  have hn := congrArg (fun x : E => ‖x‖) he
  have hnorm : ‖((prefixSpan xs (t + 1)).map U.toLinearEquiv.toLinearMap).orthogonalProjection (U a)‖ =
      ‖(prefixSpan xs (t + 1)).orthogonalProjection a‖ := by simpa using hn.symm
  rw [hnorm]
  exact hidden_prefix_bound xs I A N hmono hc hIA hη hηhalf hangle t a ha hhidden

end MatchingBounds1005.ChronologicalProjection
