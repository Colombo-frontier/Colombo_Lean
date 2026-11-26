import Nonsmooth.StrongScoreVariance

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A continuous function above a level either stays above it on the complete
right half-line or has a first crossing, with strict inequality in between. -/
theorem superlevel_first_crossing_right (h : ℝ → ℝ) (hh : Continuous h)
    {a c : ℝ} (ha : c < h a) :
    (∀ x ∈ Ici a, c < h x) ∨
      ∃ b, a < b ∧ h b = c ∧ ∀ x ∈ Ioo a b, c < h x := by
  let D : Set ℝ := {x | a ≤ x ∧ h x ≤ c}
  by_cases hD : D.Nonempty
  · right
    have hclosed : IsClosed D := isClosed_Ici.inter (isClosed_le hh continuous_const)
    have hbounded : BddBelow D := ⟨a, fun x hx => hx.1⟩
    let b := sInf D
    have hbmem : b ∈ D := hclosed.csInf_mem hD hbounded
    have hab : a < b := by
      have hab' : a ≤ b := hbmem.1
      by_contra hn
      have heq : b = a := le_antisymm (le_of_not_gt hn) hab'
      have hbc := hbmem.2
      rw [heq] at hbc
      exact (not_le_of_gt ha) hbc
    have hbetween : ∀ x ∈ Ioo a b, c < h x := by
      intro x hx
      by_contra hn
      have hxD : x ∈ D := ⟨hx.1.le, le_of_not_gt hn⟩
      exact (not_le_of_gt hx.2) (csInf_le hbounded hxD)
    have hbc : h b = c := by
      apply le_antisymm hbmem.2
      by_contra hn
      obtain ⟨x, hx, hxc⟩ := intermediate_value_Ioo' hab.le hh.continuousOn
        (show c ∈ Ioo (h b) (h a) from ⟨lt_of_not_ge hn, ha⟩)
      have hhx := hbetween x hx
      rw [hxc] at hhx
      exact (lt_irrefl c) hhx
    exact ⟨b, hab, hbc, hbetween⟩
  · left
    intro x hx
    by_contra hn
    exact hD ⟨x, hx, le_of_not_gt hn⟩

theorem superlevel_first_crossing_left (h : ℝ → ℝ) (hh : Continuous h)
    {b c : ℝ} (hb : c < h b) :
    (∀ x ∈ Iic b, c < h x) ∨
      ∃ a, a < b ∧ h a = c ∧ ∀ x ∈ Ioo a b, c < h x := by
  have hn : c < (fun x => h (-x)) (-b) := by simpa only [neg_neg] using hb
  rcases superlevel_first_crossing_right (fun x => h (-x))
    (hh.comp continuous_neg) hn with hall | ⟨a, ha, hac, hbetween⟩
  · left
    intro x hx
    have he := hall (-x) (show -x ∈ Ici (-b) from neg_le_neg (show x ≤ b from hx))
    simpa only [neg_neg] using he
  · right
    refine ⟨-a, by linarith, hac, ?_⟩
    intro x hx
    have he := hbetween (-x) (show -x ∈ Ioo (-b) a from ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    simpa only [neg_neg] using he

end
end Nonsmooth
