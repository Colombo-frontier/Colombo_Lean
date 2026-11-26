import Aggregation254

noncomputable section
open scoped BigOperators
namespace Paper254

structure ProbabilityWeights (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ j, 0 ≤ weight j
  total : ∑ j, weight j = 1

theorem ProbabilityWeights.exists_positive {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) :
    ∃ j, 0 < p.weight j := by
  by_contra hn
  push_neg at hn
  have hz : ∑ j, p.weight j ≤ 0 := Finset.sum_nonpos (fun j _ => hn j)
  rw [p.total] at hz
  norm_num at hz

theorem ProbabilityWeights.weight_le_one {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (j : ι) : p.weight j ≤ 1 := by
  classical
  rw [← p.total]
  exact Finset.single_le_sum (fun k _ => p.nonneg k) (Finset.mem_univ j)

def ProbabilityWeights.exponential {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (lam : ℝ) (loss : ι → ℝ) : ProbabilityWeights ι := by
  let j := p.exists_positive.choose
  have hj : 0 < p.weight j := p.exists_positive.choose_spec
  have hZ := exponentialNormalizer_pos lam p.weight loss p.nonneg j hj
  refine ⟨exponentialUpdate lam p.weight loss, fun k => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (p.nonneg k) (Real.exp_pos _).le) hZ.le
  · simp only [exponentialUpdate, ← Finset.sum_div]
    exact div_self (ne_of_gt hZ)

def ProbabilityWeights.prunedMixtureMass {ι : Type*} [Fintype ι]
    (p prior : ProbabilityWeights ι) (α : ℝ) (live : Finset ι) (j : ι) : ℝ := by
  classical
  exact if j ∈ live then (1-α)*p.weight j+α*prior.weight j else 0

theorem ProbabilityWeights.prunedMixture_nonneg {ι : Type*} [Fintype ι]
    (p prior : ProbabilityWeights ι) (α : ℝ) (ha : 0 ≤ α) (hb : α ≤ 1)
    (live : Finset ι) (j : ι) : 0 ≤ p.prunedMixtureMass prior α live j := by
  classical
  unfold prunedMixtureMass
  split_ifs
  · exact add_nonneg (mul_nonneg (by linarith) (p.nonneg j)) (mul_nonneg ha (prior.nonneg j))
  · rfl

theorem ProbabilityWeights.prunedMixture_total_le {ι : Type*} [Fintype ι]
    (p prior : ProbabilityWeights ι) (α : ℝ) (ha : 0 ≤ α) (hb : α ≤ 1)
    (live : Finset ι) : ∑ j, p.prunedMixtureMass prior α live j ≤ 1 := by
  classical
  calc
    _ ≤ ∑ j, ((1-α)*p.weight j+α*prior.weight j) := by
      apply Finset.sum_le_sum
      intro j _
      unfold prunedMixtureMass
      split_ifs
      · rfl
      · exact add_nonneg (mul_nonneg (by linarith) (p.nonneg j)) (mul_nonneg ha (prior.nonneg j))
    _ = 1 := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, p.total, prior.total]; ring

theorem ProbabilityWeights.prunedMixture_total_pos {ι : Type*} [Fintype ι]
    (p prior : ProbabilityWeights ι) (α : ℝ) (ha : 0 < α) (hb : α ≤ 1)
    (live : Finset ι) (hprior : ∀ j, 0 < prior.weight j → j ∈ live) :
    0 < ∑ j, p.prunedMixtureMass prior α live j := by
  classical
  obtain ⟨j, hj⟩ := prior.exists_positive
  have hm : 0 < p.prunedMixtureMass prior α live j := by
    rw [prunedMixtureMass, if_pos (hprior j hj)]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (p.nonneg j)) (mul_pos ha hj)
  exact lt_of_lt_of_le hm (Finset.single_le_sum
    (fun k _ => p.prunedMixture_nonneg prior α ha.le hb live k) (Finset.mem_univ j))

def ProbabilityWeights.pruneShare {ι : Type*} [Fintype ι]
    (p prior : ProbabilityWeights ι) (α : ℝ) (ha : 0 < α) (hb : α ≤ 1)
    (live : Finset ι) (hprior : ∀ j, 0 < prior.weight j → j ∈ live) : ProbabilityWeights ι := by
  let a := p.prunedMixtureMass prior α live
  have htotal : 0 < ∑ j, a j := p.prunedMixture_total_pos prior α ha hb live hprior
  refine ⟨fun j => a j/(∑ k, a k), fun j => ?_, ?_⟩
  · exact div_nonneg (p.prunedMixture_nonneg prior α ha.le hb live j) htotal.le
  · rw [← Finset.sum_div, div_self (ne_of_gt htotal)]

theorem ProbabilityWeights.pruneShare_survival {ι : Type*} [Fintype ι]
    (p prior : ProbabilityWeights ι) (α : ℝ) (ha : 0 < α) (hb : α ≤ 1)
    (live : Finset ι) (hprior : ∀ j, 0 < prior.weight j → j ∈ live) (j : ι) (hj : j ∈ live) :
    (1-α)*p.weight j ≤ (p.pruneShare prior α ha hb live hprior).weight j := by
  have hmass := pruning_increases_mass (p.prunedMixtureMass prior α live j)
    (∑ k, p.prunedMixtureMass prior α live k)
    (p.prunedMixture_nonneg prior α ha.le hb live j)
    (p.prunedMixture_total_pos prior α ha hb live hprior)
    (p.prunedMixture_total_le prior α ha.le hb live)
  change _ ≤ p.prunedMixtureMass prior α live j/(∑ k, p.prunedMixtureMass prior α live k)
  exact le_trans (by simp only [prunedMixtureMass, if_pos hj]; nlinarith [prior.nonneg j]) hmass

theorem ProbabilityWeights.pruneShare_birth {ι : Type*} [Fintype ι]
    (p prior : ProbabilityWeights ι) (α : ℝ) (ha : 0 < α) (hb : α ≤ 1)
    (live : Finset ι) (hprior : ∀ j, 0 < prior.weight j → j ∈ live) (j : ι) (hj : j ∈ live) :
    α*prior.weight j ≤ (p.pruneShare prior α ha hb live hprior).weight j := by
  have hmass := pruning_increases_mass (p.prunedMixtureMass prior α live j)
    (∑ k, p.prunedMixtureMass prior α live k)
    (p.prunedMixture_nonneg prior α ha.le hb live j)
    (p.prunedMixture_total_pos prior α ha hb live hprior)
    (p.prunedMixture_total_le prior α ha.le hb live)
  change _ ≤ p.prunedMixtureMass prior α live j/(∑ k, p.prunedMixtureMass prior α live k)
  exact le_trans (by simp only [prunedMixtureMass, if_pos hj]; nlinarith [p.nonneg j]) hmass

end Paper254
#print axioms Paper254.ProbabilityWeights.pruneShare_birth
#print axioms Paper254.ProbabilityWeights.pruneShare_survival
