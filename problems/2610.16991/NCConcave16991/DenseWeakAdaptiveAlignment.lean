import NCConcave16991.DenseWeakAdaptiveTotalInformation
import NCConcave16991.DenseWeakAlignmentInformation
import NCConcave16991.DenseWeakRowInformationBudget

/-! # Actual adaptive static-bank alignment probability -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem adaptive_alignment_probability_le {n m D r B : ℕ} (hm : m ≤ n)
    (hparity : m % 2 = n % 2)
    (nextRow : ∀ t : ℕ, (Fin t → Fin D → Fin 2) → Fin n)
    (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hfresh : ∀ t < r, ∀ h,
      0 < (columnBankLaw n m D hm).eventMass
        {bank | (RowExperiment.policyExperiment nextRow t).run columnBit bank = h} →
      nextRow t h ∉ (RowExperiment.policyExperiment nextRow t).observedRows h)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (v : (Fin r → Fin D → Fin 2) → Fin B → Fin D → ℝ)
    (hv : ∀ h t, (∑ j, (v h t j) ^ 2) ≤ 1)
    (hB : 1 ≤ B) (hD : 512 * Real.log ((B : ℝ) + 2) + 2048 ≤ (D : ℝ)) :
    (columnBankLaw n m D hm).eventMass {bank |
      (bankLabels bank,(RowExperiment.policyExperiment nextRow r).run columnBit bank) ∈
        alignmentEvent v ((5 / 32 : ℝ) * Real.sqrt (D : ℝ))} ≤ 1 / 8 := by
  let E := RowExperiment.policyExperiment nextRow r
  let P := labelTranscriptLaw hm E
  have hlabels : P.fst = rademacherLaw D :=
    FiniteLaw.eq_of_mass_eq _ _ (labelTranscriptLaw_fst_mass hm E)
  have hi := adaptive_bank_information_le hm hparity nextRow hrn hbudget hfresh
  have hinfo : P.mutualInformation ≤ (D : ℝ) / 8000 := by
    apply hi.trans
    have hh := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    convert hh using 1 <;> ring
  have hp := alignment_probability_of_information P hlabels v hv hB hD hinfo
  simpa only [P, labelTranscriptLaw, FiniteLaw.map_eventMass, Set.preimage, E] using hp

end NCConcave16991.DenseWeakHiding
