import BernoulliAffinity254

noncomputable section
open scoped BigOperators
namespace Paper254

def signedMean (θ : ℝ) (b : Bool) : ℝ := if b then θ else -θ

theorem signedMean_abs (θ : ℝ) (b : Bool) : |signedMean θ b| = |θ| := by
  cases b <;> simp [signedMean]

theorem signedMean_not (θ : ℝ) (b : Bool) : signedMean θ (!b) = -signedMean θ b := by
  cases b <;> simp [signedMean]

theorem signedMean_sq (θ : ℝ) (b : Bool) : (signedMean θ b)^2 = θ^2 := by
  cases b <;> simp [signedMean]

def flipSign {κ : Type*} [DecidableEq κ] (g : κ) (s : κ → Bool) : κ → Bool :=
  Function.update s g (!s g)

theorem flipSign_involutive {κ : Type*} [DecidableEq κ] (g : κ) : Function.Involutive (flipSign g) := by
  intro s
  funext k
  by_cases hk : k = g
  · subst k
    simp [flipSign]
  · simp [flipSign,hk]

theorem affinity_self {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) : finiteAffinity p p = 1 := by
  unfold finiteAffinity
  simp_rw [← sq, Real.sq_sqrt (p.nonneg _)]
  exact p.total

theorem product_one_sub_sum {κ : Type*} (s : Finset κ) (a : κ → ℝ)
    (ha : ∀ k ∈ s, 0 ≤ a k ∧ a k ≤ 1) :
    1-∑ k ∈ s, (1-a k) ≤ ∏ k ∈ s, a k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    have hk0 := ha k (Finset.mem_insert_self _ _)
    have hs := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    have hn : 0 ≤ ∑ j ∈ s, (1-a j) := Finset.sum_nonneg (fun j hj => by
      have hj' := ha j (Finset.mem_insert_of_mem hj); linarith)
    rw [Finset.sum_insert hk, Finset.prod_insert hk]
    have hm := mul_le_mul_of_nonneg_left hs hk0.1
    nlinarith [mul_nonneg hn (show 0 ≤ 1-a k by linarith)]

def signObservation {κ : Type*} (θ : ℝ) (hθ : |θ| ≤ 1)
    (s : κ → Bool) (g : κ) : ProbabilityWeights Bool :=
  bernoulliWeights (signedMean θ (s g)) (by simpa only [signedMean_abs] using hθ)

theorem sign_flip_affinity {κ : Type*} [DecidableEq κ]
    (θ : ℝ) (hθ : |θ| ≤ 1) (s : κ → Bool) (g k : κ) :
    finiteAffinity (signObservation θ hθ s k) (signObservation θ hθ (flipSign g s) k) =
      if k = g then Real.sqrt (1-θ^2) else 1 := by
  by_cases hk : k = g
  · subst k
    rw [if_pos rfl]
    unfold signObservation
    simp only [flipSign, Function.update_self, signedMean_not]
    rw [bernoulli_affinity, signedMean_sq]
  · rw [if_neg hk]
    have he : signObservation θ hθ (flipSign g s) k = signObservation θ hθ s k := by
      simp [signObservation,flipSign,hk]
    rw [he,affinity_self]

theorem hidden_sign_prefix_affinity {κ : Type*} [DecidableEq κ] (n : ℕ)
    (θ : ℝ) (hθ : |θ| ≤ 1) (s : κ → Bool) (g : κ) (query : Fin n → κ) :
    1-(∑ t : Fin n, if query t = g then θ^2 else 0) ≤
      finiteAffinity (productWeights (fun t => signObservation θ hθ s (query t)))
        (productWeights (fun t => signObservation θ hθ (flipSign g s) (query t))) := by
  rw [product_affinity]
  simp_rw [sign_flip_affinity]
  let a := fun t : Fin n => if query t = g then Real.sqrt (1-θ^2) else 1
  have hhθ := abs_le.mp hθ
  have hs0 := Real.sqrt_nonneg (1-θ^2)
  have hs1 : Real.sqrt (1-θ^2) ≤ 1 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1-θ^2 by nlinarith)
    nlinarith [sq_nonneg θ]
  have hprod := product_one_sub_sum Finset.univ a (by
    intro t _
    dsimp [a]
    split_ifs <;> constructor <;> first | assumption | norm_num)
  have hsum : (∑ t, (1-a t)) ≤ ∑ t : Fin n, if query t = g then θ^2 else 0 := by
    apply Finset.sum_le_sum
    intro t _
    dsimp [a]
    split_ifs
    · linarith [bernoulli_affinity_lower θ hθ]
    · norm_num
  change _ ≤ ∏ t, a t
  linarith

end Paper254
#print axioms Paper254.hidden_sign_prefix_affinity
