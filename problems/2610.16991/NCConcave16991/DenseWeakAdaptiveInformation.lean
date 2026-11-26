import NCConcave16991.DenseWeakActualChannel
import NCConcave16991.DenseWeakAdaptiveColumn

/-! # Actual conditional information of one adaptively selected fresh bank row -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem map_vector_pair_mass {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
    (D : ℕ) (P : Fin D → FiniteLaw A) (f : Fin D → A → I) (g : Fin D → A → J)
    (z : (Fin D → I) × (Fin D → J)) :
    ((FiniteLaw.pi P).map (fun bank ↦ (fun d ↦ f d (bank d),fun d ↦ g d (bank d)))).mass z =
      (FiniteLaw.jointPi D (fun d ↦ (P d).map (fun a ↦ (f d a,g d a)))).mass z := by
  have he : {bank : Fin D → A |
        (fun d ↦ f d (bank d),fun d ↦ g d (bank d)) = z} =
      FiniteLaw.rectangle (fun d ↦ {a | (f d a,g d a) = (z.1 d,z.2 d)}) := by
    ext bank
    constructor
    · intro h d
      have h1 := congrFun (congrArg Prod.fst h) d
      have h2 := congrFun (congrArg Prod.snd h) d
      exact Prod.ext h1 h2
    · intro h
      exact Prod.ext (funext (fun d ↦ congrArg Prod.fst (h d)))
        (funext (fun d ↦ congrArg Prod.snd (h d)))
  have hm : (FiniteLaw.pi P).eventMass
      {bank | (fun d ↦ f d (bank d),fun d ↦ g d (bank d)) = z} =
      ∏ d, (P d).eventMass {a | (f d a,g d a) = (z.1 d,z.2 d)} := by
    rw [he, FiniteLaw.pi_rectangle_eventMass]
  exact hm

def posteriorResponseLaw {n m D r : ℕ} (hm : m ≤ n)
    (E : RowExperiment (Fin n) (Fin D) (Fin 2) r) (h : Fin r → Fin D → Fin 2)
    (hh : 0 < (columnBankLaw n m D hm).eventMass {bank | E.run columnBit bank = h})
    (j : Fin n) : FiniteLaw ((Fin D → Fin 2) × (Fin D → Fin 2)) :=
  ((columnBankLaw n m D hm).condition {bank | E.run columnBit bank = h} hh).map
    (fun bank ↦ (fun d ↦ (bank d).1,fun d ↦ columnBit (bank d) j))

/-- Given an arbitrary positive-probability actual adaptive transcript, one
more fresh row leaks at most D times the literal one-cell bound. -/
theorem posteriorResponseLaw_information_le {n m D r : ℕ} (hm : m ≤ n)
    (hparity : m % 2 = n % 2) (E : RowExperiment (Fin n) (Fin D) (Fin 2) r)
    (h : Fin r → Fin D → Fin 2)
    (hh : 0 < (columnBankLaw n m D hm).eventMass {bank | E.run columnBit bank = h})
    (hbudget : 8 * m + 9 * r ≤ n) (j : UnseenRows (E.observedRows h)) :
    (posteriorResponseLaw hm E h hh j.val).mutualInformation ≤
      (D : ℝ) * (32 / 63 : ℝ) * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 := by
  obtain ⟨bank₀,hbank₀⟩ : ∃ bank : ColumnBank n m D, E.run columnBit bank = h := by
    by_contra hn
    have hz : (columnBankLaw n m D hm).eventMass {bank | E.run columnBit bank = h} = 0 := by
      unfold FiniteLaw.eventMass
      apply Finset.sum_eq_zero
      intro bank _
      exact if_neg (fun hb ↦ hn ⟨bank,hb⟩)
    linarith
  let R := E.observedRows h
  let B := fun d ↦ (bank₀ d).2.val ∩ R
  have hcf (d : Fin D) : E.columnFibre (columnBit (n := n) (m := m)) h d =
      observationEvent (n := n) (m := m) R (B d) :=
    E.columnFibre_eq_observation h bank₀ hbank₀ d
  have hcols := (E.transcript_positive_iff columnBit (fun _ ↦ biasedColumnLaw n m hm) h).mp hh
  have hpos (d : Fin D) :
      0 < (biasedColumnLaw n m hm).eventMass (observationEvent R (B d)) := by
    simpa only [hcf] using hcols d
  have hpost : (columnBankLaw n m D hm).condition {bank | E.run columnBit bank = h} hh =
      FiniteLaw.pi (fun d ↦ (biasedColumnLaw n m hm).condition (observationEvent R (B d)) (hpos d)) := by
    apply FiniteLaw.eq_of_mass_eq
    funext bank
    have hp := E.posterior_mass_factor columnBit (fun _ ↦ biasedColumnLaw n m hm) h hh bank
    simpa only [hcf, columnBankLaw] using hp
  have heq : posteriorResponseLaw hm E h hh j.val =
      FiniteLaw.jointPi D (fun d ↦ observedCellLaw hm R (B d) (hpos d) j.val) := by
    unfold posteriorResponseLaw
    rw [hpost]
    apply FiniteLaw.eq_of_mass_eq
    funext z
    exact map_vector_pair_mass D _ (fun _ c ↦ c.1) (fun _ c ↦ columnBit c j.val) z
  have hRc : R.card ≤ r := E.observedRows_card h
  have hbR : 8 * m + 9 * R.card ≤ n := by omega
  have hrn : r < n := by
    have hj := j.val.isLt
    omega
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hRcR : (R.card : ℝ) ≤ r := by exact_mod_cast hRc
  have hrnR : (r : ℝ) < n := by exact_mod_cast hrn
  have hdiv : (m : ℝ) / ((n : ℝ) - R.card) ≤ (m : ℝ) / ((n : ℝ) - r) := by
    exact div_le_div_of_nonneg_left hm0 (by linarith) (by linarith)
  have hdiv0 : 0 ≤ (m : ℝ) / ((n : ℝ) - R.card) := div_nonneg hm0 (by linarith)
  rw [heq, FiniteLaw.jointPi_mutualInformation]
  calc
    _ ≤ ∑ _d : Fin D, (32 / 63 : ℝ) * ((m : ℝ) / ((n : ℝ) - R.card)) ^ 2 := by
      apply Finset.sum_le_sum
      intro d _
      exact observedCellLaw_mutualInformation_le hm hparity R (B d)
        (Finset.inter_subset_right) hbR (hpos d) j
    _ = (D : ℝ) * (32 / 63 : ℝ) * ((m : ℝ) / ((n : ℝ) - R.card)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ (D : ℝ) * (32 / 63 : ℝ) * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 := by
      gcongr

end NCConcave16991.DenseWeakHiding
