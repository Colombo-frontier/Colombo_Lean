import SecondOrder.HessianC21
import SecondOrder.ConservativeFeatures

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

theorem bernoulliMixture_boundedC21 {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p : ι → H → ℝ) (V : (ι → Bool) → H → ℝ)
    (hp : ∀ i, BoundedC21 (p i)) (hV : ∀ w, BoundedC21 (V w)) :
    BoundedC21 (bernoulliMixture p V) := by
  apply boundedC21_finset_sum
  intro w _
  apply BoundedC21.mul _ (hV w)
  apply boundedC21_finset_prod
  intro i _
  cases w i
  · exact (boundedC21_const 1).sub (hp i)
  · exact hp i

theorem dependentReverseSelector_boundedC21 {n : ℕ} {E : Fin n → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
    (p : (i : Fin n) → E i → ℝ) (V : ℕ → PiLp 2 E → ℝ)
    (hp : ∀ i, BoundedC21 (p i)) (hV : ∀ k ≤ n, BoundedC21 (V k)) :
    BoundedC21 (dependentReverseSelector p V) := by
  rw [dependentReverseSelector_eq_mixture]
  exact bernoulliMixture_boundedC21 _ _
    (fun i => (hp i).comp_linear (dependentBlockProj (E := E) i))
    (fun w => hV _ (lastSuccess_le w))

variable {T m : ℕ} {E : Fin (T+1) → Type*} {Θ : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

theorem conservativePayload_boundedC21 (W S : (i : Fin (T+1)) → E i → ℝ)
    (hW : ∀ i, BoundedC21 (W i)) (hS : ∀ i, BoundedC21 (S i)) (j : ℕ) :
    BoundedC21 (conservativePayload W S j) := by
  by_cases hj : j<T+1
  · unfold conservativePayload
    simp only [dif_pos hj]
    exact (((hS ⟨j,hj⟩).sub (hW ⟨j,hj⟩)).comp_linear
      (dependentBlockProj (E := E) (⟨j,hj⟩ : Fin (T+1)))).const_mul _
  · have he : conservativePayload W S j = fun _ => (0:ℝ) := by
      funext x
      simp only [conservativePayload,dif_neg hj]
    rw [he]
    exact boundedC21_const 0

theorem conservativePopulation_boundedC21 (reg : PiLp 2 E → ℝ)
    (W p : (i : Fin (T+1)) → E i → ℝ)
    (hreg : BoundedC21 reg) (hW : ∀ i, BoundedC21 (W i)) (hp : ∀ i, BoundedC21 (p i)) :
    BoundedC21 (conservativePopulation reg W p) := by
  apply BoundedC21.add
  · exact hreg.add ((hW 0).comp_linear (dependentBlockProj (E := E) (0 : Fin (T+1))))
  · apply boundedC21_finset_sum
    intro i _
    exact (((hp i.castSucc).comp_linear (dependentBlockProj (E := E) i.castSucc)).mul
      ((hW i.succ).comp_linear (dependentBlockProj (E := E) i.succ))).const_mul 2

theorem conservativeChain_boundedC21 (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ)
    (hreg : BoundedC21 reg) (hW : ∀ i, BoundedC21 (W i))
    (hS : ∀ i, BoundedC21 (S i)) (hp : ∀ i, BoundedC21 (p i)) :
    BoundedC21 (conservativeChain reg W S p) :=
  (conservativePopulation_boundedC21 reg W p hreg hW hp).add
    (dependentReverseSelector_boundedC21 p _ hp (fun j _ => conservativePayload_boundedC21 W S hW hS j))

/-- A public regularizer need only be globally C²,¹. Its values and its
first two derivatives need not be globally bounded. -/
theorem conservativeChain_c21 (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ)
    (hreg : ScalarC21 reg) (hW : ∀ i, BoundedC21 (W i))
    (hS : ∀ i, BoundedC21 (S i)) (hp : ∀ i, BoundedC21 (p i)) :
    ScalarC21 (conservativeChain reg W S p) := by
  have he : conservativeChain reg W S p = fun x => reg x+conservativeChain (fun _ => 0) W S p x := by
    funext x
    simp only [conservativeChain,conservativePopulation,zero_add]
    ring
  rw [he]
  exact hreg.add (conservativeChain_boundedC21 (fun _ => 0) W S p (boundedC21_const 0) hW hS hp).toScalarC21

theorem conservativeTruncatedChain_c21 (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ)
    (hreg : ScalarC21 reg) (hW : ∀ i, BoundedC21 (W i))
    (hS : ∀ i, BoundedC21 (S i)) (hp : ∀ i, BoundedC21 (p i)) (k : ℕ) :
    ScalarC21 (conservativeTruncatedChain reg W S p k) := by
  apply conservativeChain_c21 reg W S _ hreg hW hS
  intro i
  unfold dependentPrefixGates
  split_ifs
  · exact hp i
  · exact boundedC21_const 0

namespace ConservativeFeatureData

theorem population_boundedC21 (D : ConservativeFeatureData T m E Θ)
    (h0 : ∀ i, BoundedC21 (D.offset i)) (hφ : ∀ i a, BoundedC21 (D.feature i a))
    (i : Fin (T+1)) (θ : Θ) : BoundedC21 (D.population i θ) :=
  (h0 i).add (boundedC21_finset_sum _ _ (fun a _ => (hφ i a).const_mul _))

theorem sample_boundedC21 (D : ConservativeFeatureData T m E Θ)
    (h0 : ∀ i, BoundedC21 (D.offset i)) (hφ : ∀ i a, BoundedC21 (D.feature i a))
    (i : Fin (T+1)) {R : ℝ} (z : Fin m → SignedCoefficient R) : BoundedC21 (D.sample i z) :=
  (h0 i).add (boundedC21_finset_sum _ _ (fun a _ => (hφ i a).const_mul _))

/-- Every realization of the actual fixed-array sampled loss is globally C²,¹. -/
theorem loss_c21 (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ScalarC21 reg) (h0 : ∀ i, BoundedC21 (D.offset i))
    (hφ : ∀ i a, BoundedC21 (D.feature i a)) (hgate : ∀ i θ, BoundedC21 (gate i θ))
    {R : ℝ} (z : Fin (T+1) → Fin m → SignedCoefficient R) : ScalarC21 (D.loss reg gate θ z) :=
  conservativeChain_c21 reg _ _ _ hreg (fun i => D.population_boundedC21 h0 hφ i (θ i))
    (fun i => D.sample_boundedC21 h0 hφ i (z i)) (fun i => hgate i (θ i))

theorem truncatedLoss_c21 (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ScalarC21 reg) (h0 : ∀ i, BoundedC21 (D.offset i))
    (hφ : ∀ i a, BoundedC21 (D.feature i a)) (hgate : ∀ i θ, BoundedC21 (gate i θ))
    {R : ℝ} (z : Fin (T+1) → Fin m → SignedCoefficient R) (k : ℕ) :
    ScalarC21 (D.truncatedLoss reg gate θ z k) :=
  conservativeTruncatedChain_c21 reg _ _ _ hreg (fun i => D.population_boundedC21 h0 hφ i (θ i))
    (fun i => D.sample_boundedC21 h0 hφ i (z i)) (fun i => hgate i (θ i)) k

end ConservativeFeatureData
end
end SecondOrder
