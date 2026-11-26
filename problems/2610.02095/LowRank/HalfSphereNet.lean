import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

/-! Finite half-radius nets on the Euclidean unit sphere, with at most
5^dimension points, and deterministic operator bounds from such nets. -/

namespace LowRank
open Module
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem half_separated_card_le (s : Finset E) (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 2 ≤ ‖x - y‖) :
    s.card ≤ 5 ^ finrank ℝ E := by
  classical
  let f := fun x : E => (2 : ℝ) • x
  have hf : Function.Injective f := smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)
  have h := Besicovitch.card_le_of_separated (s.image f) ?_ ?_
  · simpa only [Finset.card_image_of_injective s hf] using h
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hs y hy]
  · intro x hx y hy hxy
    obtain ⟨x, hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy', rfl⟩ := Finset.mem_image.mp hy
    have hne : x ≠ y := fun h => hxy (congrArg f h)
    have hdist := hsep x hx' y hy' hne
    dsimp only [f]
    rw [← smul_sub, norm_smul]
    norm_num
    linarith

theorem exists_half_sphere_net (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ s : Finset E, s.card ≤ 5 ^ finrank ℝ E ∧ (∀ x ∈ s, ‖x‖ = 1) ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 2 := by
  classical
  let good := fun s : Finset E => (∀ x ∈ s, ‖x‖ = 1) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 2 ≤ ‖x - y‖)
  let sizes : Set ℕ := {n | ∃ s : Finset E, good s ∧ s.card = n}
  have hnonempty : sizes.Nonempty := ⟨0, ∅, by simp [good], by simp⟩
  have hbound : BddAbove sizes := by
    refine ⟨5 ^ finrank ℝ E, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact half_separated_card_le s (fun x hx => (hs.1 x hx).le) hs.2
  obtain ⟨s, hs, hcard⟩ := Nat.sSup_mem hnonempty hbound
  refine ⟨s, half_separated_card_le s (fun x hx => (hs.1 x hx).le) hs.2, hs.1, ?_⟩
  intro x hx
  by_contra! hfar
  have hxs : x ∉ s := by
    intro h
    have := hfar x h
    norm_num at this
  have hins : good (insert x s) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs.1 y hy
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact (hyz rfl).elim
        · exact hfar z hz'
      · rcases Finset.mem_insert.mp hz with rfl | hz'
        · simpa only [norm_sub_rev] using hfar y hy'
        · exact hs.2 y hy' z hz' hyz
  have hle := le_csSup hbound (show (insert x s).card ∈ sizes from ⟨_, hins, rfl⟩)
  rw [Finset.card_insert_of_not_mem hxs, ← hcard] at hle
  omega

theorem opNorm_le_twice_of_half_net (f : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 2)
    {B : ℝ} (hB : 0 ≤ B) (hval : ∀ y ∈ s, ‖f y‖ ≤ B) : ‖f‖ ≤ 2 * B := by
  have haux : ‖f‖ ≤ B + ‖f‖ / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    calc
      ‖f x‖ = ‖f y + f (x - y)‖ := by rw [← map_add, add_sub_cancel]
      _ ≤ ‖f y‖ + ‖f (x - y)‖ := norm_add_le _ _
      _ ≤ B + ‖f‖ * ‖x - y‖ := add_le_add (hval y hy) (f.le_opNorm _)
      _ ≤ B + ‖f‖ / 2 := by nlinarith [norm_nonneg f]
  linarith

end
end LowRank
