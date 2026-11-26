import Bilevel.ChiBoundedChainScaled
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Concrete selector disjointness for the revised bounded chain. The first
jet is included; higher jet bounds are not assumed or asserted here. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential

theorem selector_zero_of_mask_zero {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hm : tailMask i z=0) : selector n i z=0 := by
  revert hm
  refine Fin.cases (by exact id) (fun j => ?_) i
  intro hm
  simp [selector,hm]

theorem selector_earlier_zero {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i<j) (hj : selector n j z≠0) : selector n i z=0 := by
  revert hij hj
  refine Fin.cases (by intro hi;exact False.elim (Fin.not_lt_zero i hi)) (fun k => ?_) j
  intro hik hk
  have he : evenGate (z k.castSucc)≠0 := by
    intro he
    apply hk
    simp [selector,he]
  have hlarge : 1/2≤|z k.castSucc| := by
    by_contra hb
    exact he (evenGate_zero (le_of_lt (lt_of_not_ge hb)))
  apply selector_zero_of_mask_zero
  apply tailMask_zero_of_large_coordinate i k.castSucc z _ hlarge
  change i.val≤k.val
  change i.val<k.val+1 at hik
  omega

theorem selector_unique {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hi : selector n i z≠0) (hj : selector n j z≠0) : i=j := by
  rcases lt_trichotomy i j with hij|hij|hji
  · exact False.elim (hi (selector_earlier_zero i j z hij hj))
  · exact hij
  · exact False.elim (hj (selector_earlier_zero j i z hji hi))

theorem selectorDerivative_zero_of_zero {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hi : selector n i z=0) : selectorDerivative n i z=0 := by
  have hm : IsLocalMin (selector n i) z := by
    apply Filter.Eventually.of_forall
    intro w
    rw [hi]
    exact (selector_range n i w).1
  exact hm.hasFDerivAt_eq_zero (selector_hasFDerivAt n i z)

theorem selector_firstJet_unique {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hi : selector n i z≠0 ∨ selectorDerivative n i z≠0)
    (hj : selector n j z≠0 ∨ selectorDerivative n j z≠0) : i=j := by
  apply selector_unique i j z
  · rcases hi with hi|hi
    · exact hi
    · exact fun he => hi (selectorDerivative_zero_of_zero i z he)
  · rcases hj with hj|hj
    · exact hj
    · exact fun he => hj (selectorDerivative_zero_of_zero j z he)

theorem selector_active_tail_small {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hi : selector n i z≠0) (j : Fin (n+1)) (hij : i≤j) : |z j|<1/2 := by
  by_contra hb
  exact hi (selector_zero_of_mask_zero i z
    (tailMask_zero_of_large_coordinate i j z hij (le_of_not_gt hb)))

theorem selector_firstJet_last_small {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hi : selector n i z≠0 ∨ selectorDerivative n i z≠0) : |z (Fin.last n)|<1/2 := by
  apply selector_active_tail_small i z _ (Fin.last n) (Fin.le_last i)
  rcases hi with hi|hi
  · exact hi
  · exact fun he => hi (selectorDerivative_zero_of_zero i z he)

theorem selector_sum_le_one (n : ℕ) (z : Space n) :
    ∑ i : Fin (n+1),selector n i z≤1 := by
  classical
  by_cases he : ∃ i : Fin (n+1),selector n i z≠0
  · obtain ⟨i,hi⟩ := he
    have hs : (∑ j : Fin (n+1),selector n j z)=selector n i z := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_contra hj
        exact hji (selector_unique j i z hj hi)
      · simp
    rw [hs]
    exact (selector_range n i z).2
  · have hs : ∀ i : Fin (n+1),selector n i z=0 := by simpa using he
    simp only [hs,Finset.sum_const_zero]
    norm_num

theorem residual_abs_bound (n : ℕ) (z : Space n) :
    |residual n z|≤Real.sqrt (Real.exp 1)*Real.sqrt (2*Real.pi) := by
  let B := Real.sqrt (Real.exp 1)*Real.sqrt (2*Real.pi)
  have hB : 0≤B := by positivity
  rw [abs_of_nonpos (residual_nonpos n z)]
  calc
    -residual n z=∑ i : Fin (n+1),selector n i z*phi (z i) := by
      simp [residual,residualTerm,Finset.sum_neg_distrib]
    _ ≤ ∑ i : Fin (n+1),selector n i z*B :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (phi_bounded _) (selector_range n i z).1)
    _ = (∑ i : Fin (n+1),selector n i z)*B := (Finset.sum_mul ..).symm
    _ ≤ B := by nlinarith [selector_sum_le_one n z]

end Bilevel.ChiBoundedChain
