import LowRank.GaussianOperatorTail
import LowRank.RectangularConditionalRate

/-! The upper edge of the Wishart spectral event is now proved. The
remaining probability premise is only its lower positive spectral edge. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

def wishartLowerSpectralEvent (d s : ℕ) (c₀ k : ℝ) : Set (Matrix (Fin d) (Fin s) ℝ) :=
  {X | LoewnerLE ((c₀ * (k / d) ^ 2) • (1 - leftKernelProjector X)) (wishart X)}

theorem measurableSet_wishartLowerSpectralEvent (d s : ℕ) (c₀ k : ℝ) :
    MeasurableSet (wishartLowerSpectralEvent d s c₀ k) := by
  have hW := measurable_wishart d s
  have hK := measurable_leftKernelProjector (m := Fin d) (n := Fin s)
  have hm : Measurable (fun X : Matrix (Fin d) (Fin s) ℝ =>
      wishart X - (c₀ * (k / d) ^ 2) • (1 - leftKernelProjector X)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hW)).sub
      (measurable_const.mul (measurable_const.sub
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hK))))
  exact (isClosed_setOf_posSemidef d).measurableSet.preimage hm

theorem wishartSpectralEvent_bad_le_lower_tail {d s : ℕ} (hd : 0 < d) (hs : s ≤ d)
    (c₀ k : ℝ) :
    (gaussianMatrixLaw d s).real (wishartSpectralEvent d s 8192 c₀ k)ᶜ ≤
      1 / 40 + (gaussianMatrixLaw d s).real (wishartLowerSpectralEvent d s c₀ k)ᶜ := by
  have heq : (wishartSpectralEvent d s 8192 c₀ k)ᶜ =
      {X | ¬LoewnerLE (wishart X) ((4096 : ℝ) • 1)} ∪ (wishartLowerSpectralEvent d s c₀ k)ᶜ := by
    ext X
    simp only [wishartSpectralEvent, wishartLowerSpectralEvent, Set.mem_compl_iff,
      Set.mem_setOf_eq, Set.mem_union, show (8192 : ℝ) / 2 = 4096 by norm_num]
    tauto
  rw [heq]
  exact (measureReal_union_le _ _).trans
    (add_le_add_right (gaussianMatrixLaw_wishart_upper_tail hd hs) _)

theorem wishartSpectralEvent_probability_of_lower_tail {d s : ℕ} (hd : 0 < d) (hs : s ≤ d)
    {c₀ k : ℝ}
    (hlower : (gaussianMatrixLaw d s).real (wishartLowerSpectralEvent d s c₀ k)ᶜ ≤ 1 / 40) :
    (gaussianMatrixLaw d s).real (wishartSpectralEvent d s 8192 c₀ k)ᶜ ≤ 1 / 20 := by
  have h := wishartSpectralEvent_bad_le_lower_tail hd hs c₀ k
  linarith

theorem rectangularQueryComplexity_rate_of_wishart_lower_tail {p c₀ : ℝ}
    (hp : 0 < p) (hc : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ →
      (∀ d : ℕ, d ≤ min a b → 100 * (k : ℝ) ≤ (d : ℝ) →
        (gaussianMatrixLaw d (d - k)).real (wishartLowerSpectralEvent d (d - k) c₀ k)ᶜ ≤ 1 / 40) →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤
        rectangularQueryComplexity.{u} a b k p ε δ := by
  obtain ⟨c, hpos, hmain⟩ := rectangularQueryComplexity_rate_of_wishart_probability.{u}
    hp (by norm_num : (0 : ℝ) < 8192) hc
  refine ⟨c, hpos, ?_⟩
  intro a b k ε δ hk hkN hε hε1 hδ hlow
  apply hmain a b k ε δ hk hkN hε hε1 hδ
  intro d hdN hdk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hd0 : 0 < d := by exact_mod_cast (show (0 : ℝ) < d by linarith)
  exact wishartSpectralEvent_probability_of_lower_tail hd0 (Nat.sub_le _ _) (hlow d hdN hdk)

end
end LowRank
