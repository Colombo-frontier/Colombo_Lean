import NCConcave16991.DenseWeakAlignment
import NCConcave16991.DenseWeakAlignmentArithmetic

/-! # The actual one-stage alignment probability from low mutual information -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

theorem alignment_probability_of_information {D B : ℕ} {H : Type*} [Fintype H]
    (P : FiniteLaw ((Fin D → Fin 2) × H))
    (hlabels : P.fst = rademacherLaw D)
    (v : H → Fin B → Fin D → ℝ) (hv : ∀ h t, (∑ j, (v h t j) ^ 2) ≤ 1)
    (hB : 1 ≤ B) (hD : 512 * Real.log ((B : ℝ) + 2) + 2048 ≤ (D : ℝ))
    (hinfo : P.mutualInformation ≤ (D : ℝ) / 8000) :
    P.eventMass (alignmentEvent v ((5 / 32 : ℝ) * Real.sqrt (D : ℝ))) ≤ 1 / 8 := by
  let s : ℝ := 25 * (D : ℝ) / 2048 - Real.log (B : ℝ)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hB)
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hexp : Real.exp (-s) = (B : ℝ) * Real.exp (-25 * (D : ℝ) / 2048) := by
    have he : -s = Real.log (B : ℝ) + (-25 * (D : ℝ) / 2048) := by dsimp [s]; ring
    rw [he, Real.exp_add, Real.exp_log hBpos]
  have htail : (P.fst.product P.snd).eventMass
      (alignmentEvent v ((5 / 32 : ℝ) * Real.sqrt (D : ℝ))) ≤ Real.exp (-s) := by
    rw [hlabels, hexp]
    exact product_gate_alignment_bound P.snd v hv
  have htransfer := P.mutualInformation_event_transfer
    (alignmentEvent v ((5 / 32 : ℝ) * Real.sqrt (D : ℝ))) s htail
  have harith := informationDimension_contradiction hBR hD (show (1 : ℝ) ≤ 1 from le_rfl)
  have hs : 0 < s := by dsimp [s]; nlinarith [show (0 : ℝ) ≤ D by positivity]
  by_contra hp
  have hp' := lt_of_not_ge hp
  have hm := mul_lt_mul_of_pos_left hp' hs
  dsimp [s] at htransfer hm
  nlinarith

end NCConcave16991.DenseWeakHiding
