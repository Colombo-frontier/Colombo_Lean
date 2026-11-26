import SecondOrder.DependentConservativeSelector
import SecondOrder.SelectorJetEquality

open scoped Classical

namespace SecondOrder
noncomputable section
variable {n : ℕ} {E : Fin n → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

theorem dependentReverseSelector_jetEq {p q : (i : Fin n) → E i → ℝ}
    {V W : ℕ → PiLp 2 E → ℝ} {x : PiLp 2 E}
    (hp : ∀ i, ScalarJetEq (p i) (q i) (x i))
    (hV : ∀ j ≤ n, ScalarJetEq (V j) (W j) x) :
    ScalarJetEq (dependentReverseSelector p V) (dependentReverseSelector q W) x := by
  rw [dependentReverseSelector_eq_mixture, dependentReverseSelector_eq_mixture]
  exact bernoulliMixture_jetEq (fun i => (hp i).comp_linear (dependentBlockProj (E := E) i))
    (fun w => hV _ (lastSuccess_le w))

def dependentPrefixGates (p : (i : Fin n) → E i → ℝ) (k : ℕ) (i : Fin n) : E i → ℝ :=
  if i.val<k then p i else fun _ => 0

theorem dependentPrefixGates_contDiff (p : (i : Fin n) → E i → ℝ) (k : ℕ)
    {r : WithTop ℕ∞} (hp : ∀ i, ContDiff ℝ r (p i)) (i : Fin n) :
    ContDiff ℝ r (dependentPrefixGates p k i) := by
  unfold dependentPrefixGates
  split_ifs
  · exact hp i
  · exact contDiff_const

theorem dependentPrefixGates_jetEq (p : (i : Fin n) → E i → ℝ) (k : ℕ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (x : PiLp 2 E)
    (hflat : ∀ i, k ≤ i.val → ScalarJetEq (p i) (fun _ => 0) (x i)) (i : Fin n) :
    ScalarJetEq (p i) (dependentPrefixGates p k i) (x i) := by
  unfold dependentPrefixGates
  split_ifs with hi
  · exact ScalarJetEq.refl (hp i) (x i)
  · exact hflat i (Nat.le_of_not_gt hi)

end
end SecondOrder
