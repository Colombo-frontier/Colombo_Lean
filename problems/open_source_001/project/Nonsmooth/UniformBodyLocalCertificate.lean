import Nonsmooth.ActualBodyLocalCertificate
import Nonsmooth.FixedBudgetPadding
import Nonsmooth.LocalizationVolumeAccuracy

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def localizationLocalBudget (d : ℕ) : ℕ := ⌈434 * (d : ℝ) * Real.log ((d : ℝ) + 1)⌉₊

theorem localizationLocalBudget_bound (d : ℕ) (hd : 2 ≤ d) :
    (localizationLocalBudget d : ℝ) ≤ 435 * (d : ℝ) * Real.log ((d : ℝ) + 1) := by
  simpa only [localizationLocalBudget, show (434 : ℝ) + 1 = 435 by norm_num] using
    uniform_localization_stage_budget_bound d hd (by norm_num : (0 : ℝ) ≤ 434)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem uniform_body_local_certificate {R : ℝ} (B : LocalizationBody E R)
    (hd : 2 ≤ Module.finrank ℝ E) :
    ∃ p : Policy Unit (CircularHistory × CyclicPeakState) (Feasible E R),
      ∃ next : CircularHistory → LocalizationBody E R,
      p.IsMeasurable ∧ (∀ h, (next h).carrier ⊆ B.carrier) ∧
      ∀ f : E → ℝ, ConvexOn ℝ B.carrier f →
        let T := localizationLocalBudget (Module.finrank ℝ E)
        let st := p.run (fun z => f z.val) () T
        (∀ z ∈ B.carrier, f z < f (p.result (fun z => f z.val) () T).val → z ∈ (next st.1).carrier) ∧
        volume (next st.1).carrier + ENNReal.ofReal (1 / 8 : ℝ) * volume B.carrier ≤ volume B.carrier := by
  obtain ⟨T, p, _out, next, hp, _hout, _houtm, hT, hsub, hcert⟩ := actual_body_local_certificate B hd
  have hcap : T ≤ localizationLocalBudget (Module.finrank ℝ E) := by
    unfold localizationLocalBudget
    exact_mod_cast hT.trans (Nat.le_ceil (434 * (Module.finrank ℝ E : ℝ) * Real.log ((Module.finrank ℝ E : ℝ) + 1)))
  refine ⟨fixedBudgetPadding p T, next, fixedBudgetPadding_measurable p hp T, hsub, ?_⟩
  intro f hf
  dsimp only
  rw [fixedBudgetPadding_final_state p hcap, fixedBudgetPadding_result p hcap]
  exact hcert f hf

end
end Nonsmooth
