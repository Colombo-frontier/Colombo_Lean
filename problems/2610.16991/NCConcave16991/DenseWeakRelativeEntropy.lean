import NCConcave16991.DenseWeakInformationChain
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-! # Actual finite relative entropy and its variational inequality -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

variable {I : Type*} [Fintype I]

def relativeEntropy (P Q : FiniteLaw I) : ℝ :=
  ∑ i, P.mass i * (Real.log (P.mass i) - Real.log (Q.mass i))

def SupportedBy (P Q : FiniteLaw I) : Prop := ∀ i, 0 < P.mass i → 0 < Q.mass i

theorem relativeEntropy_nonneg (P Q : FiniteLaw I) (hs : P.SupportedBy Q) :
    0 ≤ P.relativeEntropy Q := by
  have hpoint (i : I) : P.mass i - Q.mass i ≤
      P.mass i * (Real.log (P.mass i) - Real.log (Q.mass i)) := by
    by_cases hp : P.mass i = 0
    · simp only [hp, zero_sub, zero_mul]
      exact neg_nonpos.mpr (Q.nonneg i)
    · have hp0 := lt_of_le_of_ne (P.nonneg i) (Ne.symm hp)
      have hq0 := hs i hp0
      have hlog := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hq0 hp0)) hp0.le
      rw [Real.log_div hq0.ne' hp] at hlog
      have hdiv : P.mass i * (Q.mass i / P.mass i - 1) = Q.mass i - P.mass i := by
        field_simp
      rw [hdiv] at hlog
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ hpoint i)
  simpa only [Finset.sum_sub_distrib, P.sum_one, Q.sum_one, sub_self, relativeEntropy] using hsum

def exponentialMoment (Q : FiniteLaw I) (f : I → ℝ) : ℝ := ∑ i, Q.mass i * Real.exp (f i)

theorem exponentialMoment_pos (Q : FiniteLaw I) (f : I → ℝ) : 0 < Q.exponentialMoment f := by
  have hpos : ∃ i, 0 < Q.mass i := by
    by_contra h
    have hz (i : I) : Q.mass i = 0 := le_antisymm
      (le_of_not_gt (fun hp ↦ h ⟨i, hp⟩)) (Q.nonneg i)
    have ho := Q.sum_one
    simp only [hz, Finset.sum_const_zero] at ho
    norm_num at ho
  obtain ⟨i, hi⟩ := hpos
  exact (mul_pos hi (Real.exp_pos _)).trans_le
    (Finset.single_le_sum (fun j _ ↦ mul_nonneg (Q.nonneg j) (Real.exp_pos _).le) (Finset.mem_univ i))

def exponentialTilt (Q : FiniteLaw I) (f : I → ℝ) : FiniteLaw I where
  mass := fun i ↦ Q.mass i * Real.exp (f i) / Q.exponentialMoment f
  nonneg := fun i ↦ div_nonneg (mul_nonneg (Q.nonneg i) (Real.exp_pos _).le)
    (Q.exponentialMoment_pos f).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (Q.exponentialMoment_pos f).ne'

theorem exponentialTilt_support (P Q : FiniteLaw I) (hs : P.SupportedBy Q) (f : I → ℝ) :
    P.SupportedBy (Q.exponentialTilt f) := fun i hi ↦
  div_pos (mul_pos (hs i hi) (Real.exp_pos _)) (Q.exponentialMoment_pos f)

theorem relativeEntropy_tilt (P Q : FiniteLaw I) (hs : P.SupportedBy Q) (f : I → ℝ) :
    P.relativeEntropy (Q.exponentialTilt f) =
      P.relativeEntropy Q - (∑ i, P.mass i * f i) + Real.log (Q.exponentialMoment f) := by
  have he (i : I) :
      P.mass i * (Real.log (P.mass i) - Real.log ((Q.exponentialTilt f).mass i)) =
      P.mass i * (Real.log (P.mass i) - Real.log (Q.mass i)) -
        P.mass i * f i + P.mass i * Real.log (Q.exponentialMoment f) := by
    by_cases hp : P.mass i = 0
    · simp only [hp, zero_mul, sub_self, add_zero]
    · have hp0 := lt_of_le_of_ne (P.nonneg i) (Ne.symm hp)
      have hq0 := hs i hp0
      simp only [exponentialTilt, Real.log_div (mul_pos hq0 (Real.exp_pos _)).ne'
        (Q.exponentialMoment_pos f).ne', Real.log_mul hq0.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
  unfold relativeEntropy
  rw [Finset.sum_congr rfl (fun i _ ↦ he i), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_one, one_mul]

theorem relativeEntropy_variational (P Q : FiniteLaw I) (hs : P.SupportedBy Q) (f : I → ℝ) :
    (∑ i, P.mass i * f i) ≤ P.relativeEntropy Q + Real.log (Q.exponentialMoment f) := by
  have h := relativeEntropy_nonneg P (Q.exponentialTilt f) (exponentialTilt_support P Q hs f)
  rw [relativeEntropy_tilt P Q hs f] at h
  linarith

end NCConcave16991.DenseWeakHiding.FiniteLaw
