import SecondOrder.ScalarJetEquality
import SecondOrder.ReverseSelectorInterior

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bernoulliDensity_jetEq {p q : ι → E → ℝ} {x : E}
    (h : ∀ i, ScalarJetEq (p i) (q i) x) (w : ι → Bool) :
    ScalarJetEq (fun y => bernoulliDensity (fun i => p i y) w)
      (fun y => bernoulliDensity (fun i => q i y) w) x := by
  apply ScalarJetEq.prod
  intro i _
  cases w i
  · exact (ScalarJetEq.refl (f := fun _ : E => (1:ℝ)) contDiff_const x).sub (h i)
  · exact h i

theorem bernoulliMixture_jetEq {p q : ι → E → ℝ} {V W : (ι → Bool) → E → ℝ} {x : E}
    (hp : ∀ i, ScalarJetEq (p i) (q i) x) (hV : ∀ w, ScalarJetEq (V w) (W w) x) :
    ScalarJetEq (bernoulliMixture p V) (bernoulliMixture q W) x := by
  exact ScalarJetEq.sum Finset.univ (fun w _ => (bernoulliDensity_jetEq hp w).mul (hV w))

theorem reverseBlockSelector_jetEq {n : ℕ} {p q : Fin n → E → ℝ}
    {V W : ℕ → HomogeneousBlocks (Fin n) E → ℝ} {x : HomogeneousBlocks (Fin n) E}
    (hp : ∀ i, ScalarJetEq (p i) (q i) (x i))
    (hV : ∀ j ≤ n, ScalarJetEq (V j) (W j) x) :
    ScalarJetEq (reverseBlockSelector p V) (reverseBlockSelector q W) x := by
  rw [reverseBlockSelector_eq_mixture, reverseBlockSelector_eq_mixture]
  exact bernoulliMixture_jetEq (fun i => (hp i).comp_linear (blockProj (E := E) i))
    (fun w => hV _ (lastSuccess_le w))

/-- Retain the first k gates and replace every later gate by the zero function. -/
def prefixGates {n : ℕ} (p : Fin n → E → ℝ) (k : ℕ) (i : Fin n) : E → ℝ :=
  if i.val<k then p i else fun _ => 0

theorem prefixGates_contDiff {n : ℕ} (p : Fin n → E → ℝ) (k : ℕ) {r : WithTop ℕ∞}
    (hp : ∀ i, ContDiff ℝ r (p i)) (i : Fin n) : ContDiff ℝ r (prefixGates p k i) := by
  unfold prefixGates
  split_ifs
  · exact hp i
  · exact contDiff_const

theorem prefixGates_jetEq {n : ℕ} (p : Fin n → E → ℝ) (k : ℕ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (x : HomogeneousBlocks (Fin n) E)
    (hflat : ∀ i, k ≤ i.val → ScalarJetEq (p i) (fun _ => 0) (x i)) (i : Fin n) :
    ScalarJetEq (p i) (prefixGates p k i) (x i) := by
  unfold prefixGates
  split_ifs with hi
  · exact ScalarJetEq.refl (hp i) (x i)
  · exact hflat i (Nat.le_of_not_gt hi)

end
end SecondOrder
