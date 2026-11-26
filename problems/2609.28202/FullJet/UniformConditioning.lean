import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

open scoped BigOperators ENNReal

namespace FullJet

/-- Conditioning a uniform finite law on an event gives the uniform law on
the compatible samples. This is a theorem about actual normalized PMFs. -/
theorem uniformOfFinset_filter {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (A : Set α) [DecidablePred (· ∈ A)]
    (hA : (s.filter (· ∈ A)).Nonempty)
    (hpos : ∃ a ∈ A, a ∈ (PMF.uniformOfFinset s hs).support) :
    (PMF.uniformOfFinset s hs).filter A hpos =
      PMF.uniformOfFinset (s.filter (· ∈ A)) hA := by
  classical
  have hn : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hm : ((s.filter (· ∈ A)).card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  ext a
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, PMF.toOuterMeasure_uniformOfFinset_apply]
  by_cases ha : a ∈ A
  · rw [Set.indicator_of_mem ha]
    by_cases hs' : a ∈ s
    · rw [PMF.uniformOfFinset_apply_of_mem hs hs',
        PMF.uniformOfFinset_apply_of_mem hA (Finset.mem_filter.mpr ⟨hs', ha⟩)]
      rw [ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _)) (Or.inl hn)]
      rw [div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel hn (ENNReal.natCast_ne_top _), one_mul]
      congr 3
      ext x
      simp only [Finset.mem_filter]
    · rw [PMF.uniformOfFinset_apply_of_not_mem hs hs', zero_mul,
        PMF.uniformOfFinset_apply_of_not_mem hA (by simpa [ha] using hs')]
  · rw [Set.indicator_of_not_mem ha, zero_mul,
      PMF.uniformOfFinset_apply_of_not_mem hA (by simp [ha])]

/-- A one-to-one relabeling transports uniform finite laws exactly. -/
theorem uniformOfFinset_map_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (hs : s.Nonempty) (f : α → β) (hf : Set.InjOn f s) :
    (PMF.uniformOfFinset s hs).map f = PMF.uniformOfFinset (s.image f) (hs.image f) := by
  classical
  ext b
  rw [PMF.map_apply]
  by_cases hb : b ∈ s.image f
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    rw [tsum_eq_single a]
    · rw [if_pos rfl, PMF.uniformOfFinset_apply_of_mem hs ha,
        PMF.uniformOfFinset_apply_of_mem (hs.image f) hb, Finset.card_image_of_injOn hf]
    · intro a' ha'
      by_cases hmem : a' ∈ s
      · have hne : f a ≠ f a' := fun heq => ha' (hf hmem ha heq.symm)
        simp [hne]
      · simp [PMF.uniformOfFinset_apply, hmem]
  · rw [PMF.uniformOfFinset_apply_of_not_mem (hs.image f) hb]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    by_cases heq : b = f a
    · rw [if_pos heq]
      apply PMF.uniformOfFinset_apply_of_not_mem hs
      intro ha
      exact hb (Finset.mem_image.mpr ⟨a, ha, heq.symm⟩)
    · rw [if_neg heq]

/-- Conditioning commutes with observing a deterministic function, when the
conditioning event is specified by that observation. -/
theorem map_filter_preimage {α β : Type*} (p : PMF α) (f : α → β) (A : Set β)
    (hpre : ∃ a ∈ f ⁻¹' A, a ∈ p.support)
    (hA : ∃ b ∈ A, b ∈ (p.map f).support) :
    (p.filter (f ⁻¹' A) hpre).map f = (p.map f).filter A hA := by
  classical
  ext b
  rw [PMF.map_apply, PMF.filter_apply, ← PMF.toOuterMeasure_apply, PMF.toOuterMeasure_map_apply]
  by_cases hb : b ∈ A
  · rw [Set.indicator_of_mem hb, PMF.map_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro a
    by_cases heq : b = f a
    · rw [if_pos heq, if_pos heq, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
        Set.indicator_of_mem (show a ∈ f ⁻¹' A from by
          change f a ∈ A
          rwa [← heq])]
    · simp [heq]
  · rw [Set.indicator_of_not_mem hb, zero_mul]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    by_cases heq : b = f a
    · rw [if_pos heq]
      exact PMF.filter_apply_eq_zero_of_not_mem hpre (fun ha => hb (heq.symm ▸ ha))
    · rw [if_neg heq]

end FullJet
