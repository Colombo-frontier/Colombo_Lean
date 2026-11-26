import NCConcave16991.DenseSmoothFutureProbe
import NCConcave16991.DenseWeakStageBankLaw
import NCConcave16991.DenseWeakAdaptiveTotalInformation
import NCConcave16991.DenseWeakDimension

/-! # Actual static-bank probability of future-stage alignment -/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace NCConcave16991.DenseSmooth.Revelation

open DenseWeakHiding

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem signTable_insert_samePrefix {n m D T : ℕ} (hn : 0 < n) (hD : 0 < D)
    (hm : m ≤ n) (hp : m % 2 = n % 2) (j : Fin (T + 1))
    (a b : ColumnBank n m D) (others : StageBank n m D T) :
    SamePrefix (EuclideanSpace ℝ (Fin D)) n T ((m : ℝ) / n) j
      (signTable hn hD hm hp (Fin.insertNth j a others))
      (signTable hn hD hm hp (Fin.insertNth j b others)) := by
  intro l hl
  have he : (Fin.insertNth j a others : StageBank n m D (T + 1)) l =
      (Fin.insertNth j b others : StageBank n m D (T + 1)) l := by
    exact (Fin.insertNth_apply_below (α := fun _ ↦ ColumnBank n m D) hl a others).trans
      (Fin.insertNth_apply_below (α := fun _ ↦ ColumnBank n m D) hl b others).symm
  constructor
  · change normalizedSignVector (fun d ↦ hiddenSign ((Fin.insertNth (α := fun _ ↦ ColumnBank n m D) j a others l) d).1) = _
    rw [he]
    rfl
  · intro i
    change normalizedSignVector (fun d ↦ columnSign ((Fin.insertNth (α := fun _ ↦ ColumnBank n m D) j a others l) d).2.val i) = _
    rw [he]
    rfl

theorem columnBank_labels_law {n m D : ℕ} (hm : m ≤ n) :
    (columnBankLaw n m D hm).map bankLabels = rademacherLaw D := by
  apply FiniteLaw.eq_of_mass_eq
  funext θ
  rw [show (bankLabels : ColumnBank n m D → Fin D → Fin 2) = (fun b d ↦ (b d).1) from rfl,
    columnBank_label_map_mass]
  simp [rademacherLaw]

theorem columnBank_fixed_probe_tail {n m D : ℕ} (hm : m ≤ n)
    (v : EuclideanSpace ℝ (Fin D)) (hv : ‖v‖ ≤ 1) :
    (columnBankLaw n m D hm).eventMass {a |
      (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ signedSum (fun d ↦ v d) (bankLabels a)} ≤
      Real.exp (-25 * (D : ℝ) / 2048) := by
  have ht := rademacher_tail (fun d ↦ v d) (euclidean_sum_squares_le v hv)
    ((5 / 32 : ℝ) * Real.sqrt (D : ℝ)) (by positivity)
  rw [← columnBank_labels_law hm, FiniteLaw.map_eventMass] at ht
  have he : -((5 / 32 : ℝ) * Real.sqrt (D : ℝ)) ^ 2 / 2 = -25 * (D : ℝ) / 2048 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg D)]
    ring
  simpa only [he, Set.preimage, Set.mem_setOf_eq] using ht

variable {n m D T : ℕ} (hn : 0 < n) (hD : 0 < D) (hm : m ≤ n)
  (hp : m % 2 = n % 2) (hρ : 0 < (m : ℝ) / n)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy
    (Domain n T hn ((m : ℝ) / n) hρ) (n := n)
    (dx := primalDimension (EuclideanSpace ℝ (Fin D)) T) Ω)

theorem future_probe_stage_tail (seed : Ω) (N t : ℕ) (j : Fin (T + 1)) :
    (stageBankLaw n m D (T + 1) hm).eventMass {bank |
      (5 / 32 : ℝ) < ⟪signDirection bank j,
        futureProbe (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P seed
          (signTable hn hD hm hp bank) N t j⟫_ℝ} ≤
      Real.exp (-25 * (D : ℝ) / 2048) := by
  apply stageBank_coordinate_event_bound hm j
  intro others
  have hne : Nonempty (ColumnBank n m D) := by
    by_contra h
    haveI : IsEmpty (ColumnBank n m D) := not_nonempty_iff.mp h
    have hs := (columnBankLaw n m D hm).sum_one
    simp at hs
  let a0 : ColumnBank n m D := Classical.choice hne
  let v := futureProbe (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P seed
    (signTable hn hD hm hp (Fin.insertNth j a0 others)) N t j
  have hv : ‖v‖ ≤ 1 := futureProbe_norm_le _ _ _ _ _ _ _ _ _ _ _ _
  apply (FiniteLaw.eventMass_mono _ (fun a ha ↦ ?_)).trans (columnBank_fixed_probe_tail hm v hv)
  have hev := futureProbe_eq_of_prefix (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P
    seed (signTable hn hD hm hp (Fin.insertNth j a others))
    (signTable hn hD hm hp (Fin.insertNth j a0 others)) j
    (signTable_insert_samePrefix hn hD hm hp j a a0 others) N t
  change (5 / 32 : ℝ) < ⟪signDirection (Fin.insertNth j a others) j, _⟫_ℝ at ha
  rw [hev] at ha
  have hedir : signDirection (Fin.insertNth j a others) j =
      normalizedSignVector (fun d ↦ hiddenSign (bankLabels a d)) := by
    simp only [signDirection, bankLabels, Fin.insertNth_apply_same]
  rw [hedir, normalizedSignVector_inner] at ha
  have hs : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hh := mul_le_mul_of_nonneg_right ha.le hs.le
  change (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ signedSum (fun d ↦ v d) (bankLabels a)
  calc
    _ ≤ ((Real.sqrt (D : ℝ))⁻¹ * signedSum (fun d ↦ v d) (bankLabels a)) * Real.sqrt (D : ℝ) := hh
    _ = _ := by field_simp

theorem future_alignment_probability_le (seed : Ω) (N : ℕ) :
    (stageBankLaw n m D (T + 1) hm).eventMass {bank |
      ¬ NoFutureAlignment (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P seed
          (signTable hn hD hm hp bank) N} ≤
      ((N : ℝ) + 1) * (T + 1 : ℕ) * Real.exp (-25 * (D : ℝ) / 2048) := by
  let law := stageBankLaw n m D (T + 1) hm
  let E := fun tj : Fin (N + 1) × Fin (T + 1) ↦ {bank : StageBank n m D (T + 1) |
    (5 / 32 : ℝ) < ⟪signDirection bank tj.2,
      futureProbe (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P seed
        (signTable hn hD hm hp bank) N tj.1.val tj.2⟫_ℝ}
  have hsub : {bank | ¬ NoFutureAlignment (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P seed
      (signTable hn hD hm hp bank) N} ⊆ {bank | ∃ tj, bank ∈ E tj} := by
    intro bank hb
    simp only [NoFutureAlignment, not_forall, not_le] at hb
    obtain ⟨t,ht,j,hj⟩ := hb
    exact ⟨(⟨t,by omega⟩,j),hj⟩
  calc
    _ ≤ law.eventMass {bank | ∃ tj, bank ∈ E tj} := FiniteLaw.eventMass_mono law hsub
    _ ≤ ∑ tj, law.eventMass (E tj) := FiniteLaw.eventMass_exists_le law E
    _ ≤ ∑ _tj : Fin (N + 1) × Fin (T + 1), Real.exp (-25 * (D : ℝ) / 2048) :=
      Finset.sum_le_sum (fun tj _ ↦ future_probe_stage_tail hn hD hm hp hρ P seed N tj.1.val tj.2)
    _ = _ := by simp [Fintype.card_prod, Nat.cast_add, Nat.cast_mul]

theorem future_alignment_probability_small (seed : Ω) (N : ℕ)
    (hDim : D = alignmentDimension (N + 2) (T + 1)) :
    (stageBankLaw n m D (T + 1) hm).eventMass {bank |
      ¬ NoFutureAlignment (EuclideanSpace ℝ (Fin D)) n T hn ((m : ℝ) / n) hρ P seed
          (signTable hn hD hm hp bank) N} ≤ 1 / 128 := by
  apply (future_alignment_probability_le hn hD hm hp hρ P seed N).trans
  have ht := alignmentDimension_future_tail (N + 2) (T + 1)
  rw [← hDim] at ht
  push_cast at ht ⊢
  have he := Real.exp_pos (-25 * (D : ℝ) / 2048)
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  nlinarith

end NCConcave16991.DenseSmooth.Revelation
