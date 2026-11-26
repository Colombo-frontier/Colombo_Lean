import HeavyTail.GaussianLowerGeometry
import HeavyTail.ProbabilityTools

/-! Finite-hypercube averaging for actual probability laws and arbitrary
measurable coordinate decoders, including the high-probability Hamming event. -/

open MeasureTheory
open scoped BigOperators
namespace HeavyTail.GaussianLower
noncomputable section

lemma gaussianFlip_involutive {k : ℕ} (j : Fin k) :
    Function.Involutive (fun v : Fin k → Bool ↦ gaussianFlip v j) := by
  intro v
  ext i
  by_cases hi : i = j
  · subst i
    simp [gaussianFlip]
  · simp [gaussianFlip, Function.update_of_ne hi]

def hypercubeBitError {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : (Fin k → Bool) → Measure Ω) (decode : Ω → Fin k → Bool)
    (v : Fin k → Bool) (j : Fin k) : ℝ := P v |>.real {ω | decode ω j ≠ v j}

def decodedHamming {Ω : Type*} {k : ℕ} (decode : Ω → Fin k → Bool)
    (v : Fin k → Bool) (ω : Ω) : ℝ := ∑ j, if decode ω j ≠ v j then 1 else 0

lemma decodedHamming_indicator {Ω : Type*} {k : ℕ} (decode : Ω → Fin k → Bool)
    (v : Fin k → Bool) : decodedHamming decode v =
      fun ω ↦ ∑ j, {ω | decode ω j ≠ v j}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  funext ω
  simp [decodedHamming, Set.indicator_apply]

theorem bitErrorSet_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    {decode : Ω → Fin k → Bool} (hd : ∀ j, Measurable (fun ω ↦ decode ω j))
    (v : Fin k → Bool) (j : Fin k) : MeasurableSet {ω | decode ω j ≠ v j} :=
  hd j (MeasurableSet.singleton (v j)).compl

theorem decodedHamming_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    {decode : Ω → Fin k → Bool} (hd : ∀ j, Measurable (fun ω ↦ decode ω j))
    (v : Fin k → Bool) : Measurable (decodedHamming decode v) := by
  exact Finset.measurable_sum _ fun j _ ↦
    Measurable.ite (bitErrorSet_measurable hd v j) measurable_const measurable_const

theorem decodedHamming_integrable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    {decode : Ω → Fin k → Bool} (hd : ∀ j, Measurable (fun ω ↦ decode ω j))
    (v : Fin k → Bool) (P : Measure Ω) [IsProbabilityMeasure P] :
    Integrable (decodedHamming decode v) P := by
  rw [decodedHamming_indicator]
  exact integrable_finset_sum _ fun j _ ↦
    (integrable_const (1 : ℝ) (μ := P)).indicator (bitErrorSet_measurable hd v j)

theorem decodedHamming_bound {Ω : Type*} {k : ℕ} (decode : Ω → Fin k → Bool)
    (v : Fin k → Bool) (ω : Ω) : decodedHamming decode v ω ≤ (k : ℝ) := by
  calc
    _ ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ by split_ifs <;> norm_num
    _ = k := by simp

theorem decodedHamming_integral {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : (Fin k → Bool) → Measure Ω) [∀ v, IsProbabilityMeasure (P v)]
    {decode : Ω → Fin k → Bool} (hd : ∀ j, Measurable (fun ω ↦ decode ω j))
    (v : Fin k → Bool) :
    (∫ ω, decodedHamming decode v ω ∂P v) = ∑ j, hypercubeBitError P decode v j := by
  rw [decodedHamming_indicator]
  rw [integral_finset_sum _ (fun j _ ↦
    (integrable_const (1 : ℝ) (μ := P v)).indicator (bitErrorSet_measurable hd v j))]
  apply Finset.sum_congr rfl
  intro j hj
  change (∫ ω, {ω | decode ω j ≠ v j}.indicator (fun _ ↦ (1 : ℝ)) ω ∂P v) = _
  rw [integral_indicator (bitErrorSet_measurable hd v j), integral_const]
  simp [hypercubeBitError]

theorem flipped_errorSet_compl {Ω : Type*} {k : ℕ} (decode : Ω → Fin k → Bool)
    (v : Fin k → Bool) (j : Fin k) :
    {ω | decode ω j ≠ gaussianFlip v j j} = {ω | decode ω j ≠ v j}ᶜ := by
  ext ω
  cases hv : v j <;> cases hd : decode ω j <;> simp [gaussianFlip, hv, hd]

/-- Pairwise testing bounds are averaged over the actual finite family. -/
theorem exists_hypercube_hamming_mean {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : (Fin k → Bool) → Measure Ω) [∀ v, IsProbabilityMeasure (P v)]
    {decode : Ω → Fin k → Bool} (hd : ∀ j, Measurable (fun ω ↦ decode ω j))
    (hpair : ∀ v j, (7 / 8 : ℝ) ≤ hypercubeBitError P decode v j +
      hypercubeBitError P decode (gaussianFlip v j) j) :
    ∃ v, (7 * (k : ℝ) / 16) ≤ ∫ ω, decodedHamming decode v ω ∂P v := by
  classical
  have hsum (j : Fin k) : (Fintype.card (Fin k → Bool) : ℝ) * (7 / 8 : ℝ) ≤
      2 * ∑ v : Fin k → Bool, hypercubeBitError P decode v j := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ ↦ hpair v j)
    let e : (Fin k → Bool) ≃ (Fin k → Bool) :=
      ⟨(fun v ↦ gaussianFlip v j), (fun v ↦ gaussianFlip v j),
        gaussianFlip_involutive j, gaussianFlip_involutive j⟩
    have he := e.sum_comp
      (fun v ↦ hypercubeBitError P decode v j)
    change (∑ v : Fin k → Bool, hypercubeBitError P decode (gaussianFlip v j) j) =
      ∑ v : Fin k → Bool, hypercubeBitError P decode v j at he
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h
    rw [he] at h
    linarith
  have hj := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hsum j)
  have htotal : (∑ _v : Fin k → Bool, 7 * (k : ℝ) / 16) ≤
      ∑ v : Fin k → Bool, ∫ ω, decodedHamming decode v ω ∂P v := by
    simp_rw [decodedHamming_integral P hd]
    rw [Finset.sum_comm]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum] at hj ⊢
    nlinarith only [hj]
  obtain ⟨v, hv, hvmean⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty htotal
  exact ⟨v, hvmean⟩

theorem exists_hypercube_hamming_probability {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (hk : 0 < k) (P : (Fin k → Bool) → Measure Ω) [∀ v, IsProbabilityMeasure (P v)]
    {decode : Ω → Fin k → Bool} (hd : ∀ j, Measurable (fun ω ↦ decode ω j))
    (hpair : ∀ v j, (7 / 8 : ℝ) ≤ hypercubeBitError P decode v j +
      hypercubeBitError P decode (gaussianFlip v j) j) :
    ∃ v, (1 / 4 : ℝ) ≤ (P v).real {ω | (k : ℝ) / 4 ≤ decodedHamming decode v ω} := by
  obtain ⟨v, hv⟩ := exists_hypercube_hamming_mean P hd hpair
  exact ⟨v, hamming_probability_lower (Nat.cast_pos.mpr hk)
    (decodedHamming_measurable hd v) (decodedHamming_integrable hd v (P v))
    (decodedHamming_bound decode v) hv⟩

end
end HeavyTail.GaussianLower
