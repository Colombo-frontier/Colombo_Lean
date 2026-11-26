import HiddenRisk254
import ConditionalRisk254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem finiteExpectation_nonneg {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (F : ι → ℝ) (hF : ∀ i, 0 ≤ F i) : 0 ≤ finiteExpectation p F :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (p.nonneg i) (hF i))

theorem finiteExpectation_div {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (F : ι → ℝ) (c : ℝ) : finiteExpectation p (fun i => F i/c) = finiteExpectation p F/c := by
  unfold finiteExpectation
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]

theorem finiteExpectation_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ProbabilityWeights ι) (F : κ → ι → ℝ) :
    finiteExpectation p (fun i => ∑ k, F k i) = ∑ k, finiteExpectation p (F k) := by
  unfold finiteExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

def experimentRoundRisk {κ : Type*} [Fintype κ] [DecidableEq κ] {T : ℕ}
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin T → κ) (t : Fin T)
    (X : (Fin t.val → Bool) → ℝ) : ℝ :=
  finiteExpectation (uniformFinite (κ → Bool)) (fun s =>
    finiteExpectation (productWeights (fun r => signObservation θ hθ s (query r)))
      (roundExcess t X (signedMean θ (s (query t)))))

theorem experimentRoundRisk_eq {κ : Type*} [Fintype κ] [DecidableEq κ] {T : ℕ}
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin T → κ) (t : Fin T)
    (X : (Fin t.val → Bool) → ℝ) :
    experimentRoundRisk θ hθ query t X =
      finiteExpectation (uniformFinite (κ → Bool))
        (hiddenRisk t.val θ hθ (fun i => query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩) (query t) X)/2 := by
  unfold experimentRoundRisk
  rw [← finiteExpectation_div]
  apply congrArg (finiteExpectation (uniformFinite (κ → Bool)))
  funext s
  exact conditional_square_risk t _ (signedMean θ (s (query t)))
    (by simpa only [signedMean_abs] using hθ) rfl X

theorem experimentRoundRisk_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ] {T : ℕ}
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin T → κ) (t : Fin T)
    (X : (Fin t.val → Bool) → ℝ) : 0 ≤ experimentRoundRisk θ hθ query t X := by
  rw [experimentRoundRisk_eq]
  apply div_nonneg _ (by norm_num)
  apply finiteExpectation_nonneg
  intro s
  apply finiteExpectation_nonneg
  intro ω
  exact sq_nonneg _

theorem experimentRoundRisk_lower {κ : Type*} [Fintype κ] [DecidableEq κ] {T : ℕ}
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin T → κ) (t : Fin T)
    (X : (Fin t.val → Bool) → ℝ)
    (hinfo : (∑ i : Fin t.val, if query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩ = query t then θ^2 else 0) ≤ 1/32) :
    θ^2/4 ≤ experimentRoundRisk θ hθ query t X := by
  rw [experimentRoundRisk_eq]
  have hh := hidden_sign_estimation_risk t.val θ hθ
    (fun i => query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩) (query t) hinfo X
  linarith

theorem experiment_total_lower {κ : Type*} [Fintype κ] [DecidableEq κ] {T : ℕ}
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin T → κ)
    (X : (t : Fin T) → (Fin t.val → Bool) → ℝ) (good : Finset (Fin T))
    (hinfo : ∀ t ∈ good, (∑ i : Fin t.val, if query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩ = query t then θ^2 else 0) ≤ 1/32) :
    (good.card : ℝ)*θ^2/4 ≤
      finiteExpectation (uniformFinite (κ → Bool)) (fun s =>
        finiteExpectation (productWeights (fun r => signObservation θ hθ s (query r)))
          (fun ω => ∑ t : Fin T, roundExcess t (X t) (signedMean θ (s (query t))) ω)) := by
  simp_rw [finiteExpectation_sum]
  change _ ≤ ∑ t : Fin T, experimentRoundRisk θ hθ query t (X t)
  have hgood := Finset.sum_le_sum (fun t ht => experimentRoundRisk_lower θ hθ query t (X t) (hinfo t ht))
  have hall : (∑ t ∈ good, experimentRoundRisk θ hθ query t (X t)) ≤
      ∑ t : Fin T, experimentRoundRisk θ hθ query t (X t) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      (fun t _ _ => experimentRoundRisk_nonneg θ hθ query t (X t))
  have hc : (∑ _t ∈ good, θ^2/4) = (good.card : ℝ)*θ^2/4 := by simp; ring
  rw [hc] at hgood
  exact hgood.trans hall

end Paper254
#print axioms Paper254.experiment_total_lower
