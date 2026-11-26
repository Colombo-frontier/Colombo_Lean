import SecondOrder.BalancedHoeffding

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

theorem sign_sum_eq_counts {I : Type*} [Fintype I] (w : I → Bool) :
    (∑ i, signValue (w i)) =
      (Fintype.card {i // w i = true} : ℝ)-(Fintype.card {i // w i = false} : ℝ) := by
  rw [← Fintype.sum_fiberwise' w signValue]
  simp [Fintype.sum_bool, signValue, sub_eq_add_neg]

theorem sign_sum_zero_iff_balanced {I : Type*} [Fintype I] {m : ℕ}
    (hI : Fintype.card I = 2*m) (w : I → Bool) :
    (∑ i, signValue (w i)) = 0 ↔ ∀ b : Bool, Fintype.card {i // w i = b} = m := by
  have hc := Fintype.card_congr (Equiv.sigmaFiberEquiv w)
  simp only [Fintype.card_sigma, Fintype.sum_bool, hI] at hc
  rw [sign_sum_eq_counts]
  constructor
  · intro he
    have hr : (Fintype.card {i // w i = true} : ℝ) =
        (Fintype.card {i // w i = false} : ℝ) := by linarith
    have hn : Fintype.card {i // w i = true} = Fintype.card {i // w i = false} := by exact_mod_cast hr
    intro b
    cases b <;> omega
  · intro h
    rw [h true, h false, sub_self]

/-- The original zero-sum sign subset in D=2m ordinary coordinates. -/
abbrev BalancedVector (m : ℕ) := {w : Fin (2*m) → Bool // (∑ i, signValue (w i)) = 0}

def pairIndexEquiv (m : ℕ) : PairIndex m ≃ Fin (2*m) :=
  Fintype.equivOfCardEq (by simp [PairIndex, Fintype.card_prod, Nat.mul_comm])

def balancedVectorEquiv (m : ℕ) : BalancedSigns m ≃ BalancedVector m where
  toFun w := ⟨fun i => w.1 ((pairIndexEquiv m).symm i), by
    rw [Equiv.sum_comp (pairIndexEquiv m).symm (fun i => signValue (w.1 i))]
    exact balancedSigns_sum_zero w⟩
  invFun w := ⟨fun i => w.1 (pairIndexEquiv m i), by
    apply (sign_sum_zero_iff_balanced (by simp [PairIndex, Nat.mul_comm]) _).mp
    rw [Equiv.sum_comp (pairIndexEquiv m) (fun i => signValue (w.1 i))]
    exact w.property⟩
  left_inv w := by apply Subtype.ext; funext i; simp
  right_inv w := by apply Subtype.ext; funext i; simp

instance balancedVector_nonempty (m : ℕ) : Nonempty (BalancedVector m) :=
  ⟨balancedVectorEquiv m (balancedBase m)⟩

def balancedVectorLaw (m : ℕ) : Measure (BalancedVector m) :=
  (PMF.uniformOfFintype (BalancedVector m)).toMeasure

instance balancedVectorLaw_probability (m : ℕ) : IsProbabilityMeasure (balancedVectorLaw m) := by
  unfold balancedVectorLaw
  infer_instance

def balancedVectorSum {m : ℕ} (a : Fin (2*m) → ℝ) (w : BalancedVector m) : ℝ :=
  ∑ i, a i*signValue (w.1 i)

theorem balancedVectorSum_equiv {m : ℕ} (a : Fin (2*m) → ℝ) (w : BalancedSigns m) :
    balancedVectorSum a (balancedVectorEquiv m w) =
      balancedSignSum (fun i => a (pairIndexEquiv m i)) w := by
  have he := Equiv.sum_comp (pairIndexEquiv m)
    (fun i => a i*signValue (w.1 ((pairIndexEquiv m).symm i)))
  simpa only [Equiv.symm_apply_apply] using he.symm

/-- The balanced-sign Hoeffding lemma on precisely the manuscript's
uniform zero-sum subset of {-1,1}^D, with D=2m. -/
theorem balancedVector_hoeffding {m : ℕ} {a : Fin (2*m) → ℝ}
    (ha : ∀ i, |a i| ≤ 1) {t : ℝ} (ht : 0 < t) :
    balancedVectorLaw m {w | t ≤ |balancedVectorSum a w|} ≤
      ENNReal.ofReal (2*Real.exp (-t^2/(4*(2*m:ℕ)))) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  change (PMF.uniformOfFintype (BalancedVector m)).toMeasure.real _ ≤ _
  rw [uniformMeasure_real_indicator]
  change uniformMean (fun w : BalancedVector m => if t ≤ |balancedVectorSum a w| then (1:ℝ) else 0) ≤ _
  rw [← uniformMean_equiv (balancedVectorEquiv m) (fun w => if t ≤ |balancedVectorSum a w| then (1:ℝ) else 0)]
  simp only [balancedVectorSum_equiv]
  have hb := balancedSignSum_hoeffding_real (fun i => ha (pairIndexEquiv m i)) ht
  rw [balancedSignLaw_real_indicator] at hb
  convert hb using 1 <;> push_cast <;> ring

end
end SecondOrder
