import NCConcave16991.DenseWeakAdaptiveInformation
import NCConcave16991.DenseWeakAdaptiveSequence
import NCConcave16991.DenseWeakInformationMap
import NCConcave16991.DenseWeakRademacher

/-! # Information accumulated by the actual finite adaptive bank experiment -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def bankLabels {n m D : ℕ} (bank : ColumnBank n m D) : Fin D → Fin 2 :=
  fun d ↦ (bank d).1

def labelTranscriptLaw {n m D r : ℕ} (hm : m ≤ n)
    (E : RowExperiment (Fin n) (Fin D) (Fin 2) r) :
    FiniteLaw ((Fin D → Fin 2) × (Fin r → Fin D → Fin 2)) :=
  (columnBankLaw n m D hm).map (fun bank ↦ (bankLabels bank,E.run columnBit bank))

theorem labelTranscriptLaw_fst_mass {n m D r : ℕ} (hm : m ≤ n)
    (E : RowExperiment (Fin n) (Fin D) (Fin 2) r) :
    (labelTranscriptLaw hm E).fst.mass = (rademacherLaw D).mass := by
  funext θ
  rw [labelTranscriptLaw, FiniteLaw.map_pair_fst_mass]
  change ((columnBankLaw n m D hm).map bankLabels).mass θ = _
  rw [show (bankLabels : ColumnBank n m D → Fin D → Fin 2) =
    (fun bank d ↦ (bank d).1) from rfl]
  rw [columnBank_label_map_mass]
  simp [rademacherLaw]

def nextRowJointLaw {n m D r : ℕ} (hm : m ≤ n)
    (E : RowExperiment (Fin n) (Fin D) (Fin 2) r)
    (nextRow : (Fin r → Fin D → Fin 2) → Fin n) :
    FiniteLaw ((Fin r → Fin D → Fin 2) × ((Fin D → Fin 2) × (Fin D → Fin 2))) :=
  (columnBankLaw n m D hm).map (fun bank ↦
    (E.run columnBit bank,(bankLabels bank,fun d ↦ columnBit (bank d) (nextRow (E.run columnBit bank)))))

theorem nextRowJoint_conditional_eq {n m D r : ℕ} (hm : m ≤ n)
    (E : RowExperiment (Fin n) (Fin D) (Fin 2) r)
    (nextRow : (Fin r → Fin D → Fin 2) → Fin n) (h : Fin r → Fin D → Fin 2)
    (hh : 0 < (nextRowJointLaw hm E nextRow).fst.mass h) :
    (nextRowJointLaw hm E nextRow).conditionalPair h hh =
      posteriorResponseLaw hm E h
        (by simpa only [nextRowJointLaw, FiniteLaw.map_pair_fst_mass] using hh) (nextRow h) := by
  let P := columnBankLaw n m D hm
  have hprob : 0 < P.eventMass {bank | E.run columnBit bank = h} := by
    simpa only [nextRowJointLaw, FiniteLaw.map_pair_fst_mass] using hh
  have hc := FiniteLaw.condition_map_congr_mass P {bank | E.run columnBit bank = h} hprob
    (fun bank ↦ (bankLabels bank,fun d ↦ columnBit (bank d) (nextRow (E.run columnBit bank))))
    (fun bank ↦ (bankLabels bank,fun d ↦ columnBit (bank d) (nextRow h)))
    (fun bank hb ↦ by rw [hb])
  apply FiniteLaw.eq_of_mass_eq
  funext z
  exact (FiniteLaw.conditionalPair_map_mass P (E.run columnBit)
    (fun bank ↦ (bankLabels bank,fun d ↦ columnBit (bank d) (nextRow (E.run columnBit bank)))) h hh z).trans
      (congrFun hc z)

theorem nextRow_information_increment {n m D r : ℕ} (hm : m ≤ n)
    (E : RowExperiment (Fin n) (Fin D) (Fin 2) r)
    (nextRow : (Fin r → Fin D → Fin 2) → Fin n) :
    (labelTranscriptLaw hm (E.extend nextRow)).mutualInformation -
        (labelTranscriptLaw hm E).mutualInformation =
      ∑ h, (nextRowJointLaw hm E nextRow).fst.mass h *
        (nextRowJointLaw hm E nextRow).conditionalPairInformation h := by
  let Q := nextRowJointLaw hm E nextRow
  have hOld : Q.labelHistory = labelTranscriptLaw hm E :=
    FiniteLaw.eq_of_mass_eq _ _ (FiniteLaw.triple_labelHistory_mass _ _ _ _)
  have hNew : Q.labelHistoryReply.mutualInformation =
      (labelTranscriptLaw hm (E.extend nextRow)).mutualInformation := by
    have he : Q.labelHistoryReply = (columnBankLaw n m D hm).map
        (fun bank ↦ (bankLabels bank,(E.run columnBit bank,
          fun d ↦ columnBit (bank d) (nextRow (E.run columnBit bank))))) :=
      FiniteLaw.eq_of_mass_eq _ _ (FiniteLaw.triple_labelHistoryReply_mass _ _ _ _)
    rw [he]
    symm
    have h := FiniteLaw.map_second_equiv_information (columnBankLaw n m D hm) bankLabels
      (fun bank ↦ (E.run columnBit bank,fun d ↦ columnBit (bank d) (nextRow (E.run columnBit bank))))
      (RowExperiment.snocEquiv r (Fin D → Fin 2))
    simpa only [labelTranscriptLaw, RowExperiment.snocEquiv, Equiv.coe_fn_mk,
      RowExperiment.run_extend] using h
  rw [← hNew, ← hOld]
  exact Q.history_information_increment

theorem nextRow_information_increment_le {n m D t r : ℕ} (hm : m ≤ n)
    (hparity : m % 2 = n % 2) (E : RowExperiment (Fin n) (Fin D) (Fin 2) t)
    (nextRow : (Fin t → Fin D → Fin 2) → Fin n) (htr : t ≤ r) (hrn : r < n)
    (hbudget : 8 * m + 9 * r ≤ n)
    (hfresh : ∀ h, 0 < (columnBankLaw n m D hm).eventMass {bank | E.run columnBit bank = h} →
      nextRow h ∉ E.observedRows h) :
    (labelTranscriptLaw hm (E.extend nextRow)).mutualInformation -
        (labelTranscriptLaw hm E).mutualInformation ≤
      (D : ℝ) * (32 / 63 : ℝ) * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 := by
  let Q := nextRowJointLaw hm E nextRow
  let C : ℝ := (D : ℝ) * (32 / 63 : ℝ) * ((m : ℝ) / ((n : ℝ) - r)) ^ 2
  have hb (h) (hh : 0 < Q.fst.mass h) : (Q.conditionalPair h hh).mutualInformation ≤ C := by
    have hp : 0 < (columnBankLaw n m D hm).eventMass {bank | E.run columnBit bank = h} := by
      simpa only [Q, nextRowJointLaw, FiniteLaw.map_pair_fst_mass] using hh
    rw [nextRowJoint_conditional_eq]
    have hb := posteriorResponseLaw_information_le hm hparity E h hp
      (by omega : 8 * m + 9 * t ≤ n) ⟨nextRow h,hfresh h hp⟩
    apply hb.trans
    dsimp [C]
    have htrR : (t : ℝ) ≤ r := by exact_mod_cast htr
    have hrnR : (r : ℝ) < n := by exact_mod_cast hrn
    have hd : (m : ℝ) / ((n : ℝ) - t) ≤ (m : ℝ) / ((n : ℝ) - r) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith)
    have hd0 : 0 ≤ (m : ℝ) / ((n : ℝ) - t) := div_nonneg (Nat.cast_nonneg _) (by linarith)
    gcongr
  rw [nextRow_information_increment]
  have hb' := Q.history_information_increment_le (fun _ ↦ C) hb
  rw [Q.history_information_increment] at hb'
  simpa only [← Finset.sum_mul, Q.fst.sum_one, one_mul] using hb'

/-- The complete actual adaptive transcript leaks at most r times the
one-row bound. The only freshness premise concerns actual positive-mass
histories, and posterior independence is proved from the static bank. -/
theorem adaptive_bank_information_le {n m D r : ℕ} (hm : m ≤ n)
    (hparity : m % 2 = n % 2)
    (nextRow : ∀ t : ℕ, (Fin t → Fin D → Fin 2) → Fin n)
    (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hfresh : ∀ t < r, ∀ h,
      0 < (columnBankLaw n m D hm).eventMass
        {bank | (RowExperiment.policyExperiment nextRow t).run columnBit bank = h} →
      nextRow t h ∉ (RowExperiment.policyExperiment nextRow t).observedRows h) :
    (labelTranscriptLaw hm (RowExperiment.policyExperiment nextRow r)).mutualInformation ≤
      (D : ℝ) * (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 := by
  let C : ℝ := (D : ℝ) * (32 / 63 : ℝ) * ((m : ℝ) / ((n : ℝ) - r)) ^ 2
  have hb (t : ℕ) (ht : t ≤ r) :
      (labelTranscriptLaw hm (RowExperiment.policyExperiment nextRow t)).mutualInformation ≤ (t : ℝ) * C := by
    induction t with
    | zero =>
        have hz := FiniteLaw.constant_reply_information (columnBankLaw n m D hm) bankLabels
          ((RowExperiment.policyExperiment nextRow 0).run columnBit)
        simpa only [labelTranscriptLaw, Nat.cast_zero, zero_mul, hz] using le_refl (0 : ℝ)
    | succ t ih =>
        have hi := ih (by omega)
        have hs := nextRow_information_increment_le hm hparity
          (RowExperiment.policyExperiment nextRow t) (nextRow t) (by omega : t ≤ r) hrn hbudget
          (hfresh t (by omega))
        change (labelTranscriptLaw hm (RowExperiment.policyExperiment nextRow (t + 1))).mutualInformation -
          (labelTranscriptLaw hm (RowExperiment.policyExperiment nextRow t)).mutualInformation ≤ C at hs
        rw [Nat.cast_add, Nat.cast_one]
        nlinarith only [hi,hs]
  have h := hb r le_rfl
  convert h using 1 <;> dsimp [C] <;> ring

end NCConcave16991.DenseWeakHiding
