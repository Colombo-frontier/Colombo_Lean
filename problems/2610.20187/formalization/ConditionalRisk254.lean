import SequentialRisk254
import ProductMarginal254

noncomputable section
open scoped BigOperators
namespace Paper254

def binarySquare (x : ℝ) (y : Bool) : ℝ := (x-(if y then 1 else -1))^2/2

theorem binarySquare_expectation (x θ : ℝ) (hθ : |θ| ≤ 1) :
    (∑ y : Bool, (bernoulliWeights θ hθ).weight y*(binarySquare x y-binarySquare θ y)) = (x-θ)^2/2 := by
  simp [bernoulliWeights,binarySquare]
  ring

def roundExcess {T : ℕ} (t : Fin T) (X : (Fin t.val → Bool) → ℝ)
    (θ : ℝ) (ω : Fin T → Bool) : ℝ :=
  binarySquare (X (prefixRestriction (Nat.le_of_lt t.isLt) ω)) (ω t)-binarySquare θ (ω t)

theorem conditional_square_risk {T : ℕ} (t : Fin T)
    (p : Fin T → ProbabilityWeights Bool) (θ : ℝ) (hθ : |θ| ≤ 1)
    (ht : p t = bernoulliWeights θ hθ) (X : (Fin t.val → Bool) → ℝ) :
    finiteExpectation (productWeights p) (roundExcess t X θ) =
      finiteExpectation (productWeights (fun i : Fin t.val => p ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩))
        (fun ω => (X ω-θ)^2)/2 := by
  let h := Nat.succ_le_of_lt t.isLt
  let pp := fun i : Fin (t.val+1) => p ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
  let F := fun v : Fin (t.val+1) → Bool =>
    binarySquare (X (fun i => v i.castSucc)) (v (Fin.last t.val))-binarySquare θ (v (Fin.last t.val))
  have hm := product_marginal_prefix T (t.val+1) h p F
  change finiteExpectation (productWeights p) (roundExcess t X θ) = finiteExpectation (productWeights pp) F at hm
  rw [hm, product_expectation_last]
  change (∑ v : Fin t.val → Bool, (productWeights (fun i => pp i.castSucc)).weight v*
    ∑ y : Bool, (pp (Fin.last t.val)).weight y*F (Fin.snoc v y)) = _
  have hlast : pp (Fin.last t.val) = bernoulliWeights θ hθ := ht
  rw [hlast]
  dsimp only [F]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  simp_rw [binarySquare_expectation]
  unfold finiteExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  change _ = (productWeights (fun i => pp i.castSucc)).weight v*(X v-θ)^2/2
  ring

end Paper254
#print axioms Paper254.conditional_square_risk
