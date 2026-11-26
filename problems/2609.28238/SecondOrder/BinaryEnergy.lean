import SecondOrder.BinaryNodes
import SecondOrder.MixedSigns

open MeasureTheory
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def paddedNode {L M : ℕ} (i : Fin L × Fin M) : BinaryNode L := (i.1,i.2.val)

theorem completedNode_index_lt {L M : ℕ} (i : BinaryNode L) (hi : nodeRight i ≤ M) : i.2 < M := by
  have hp0 : 0 < 2^i.1.val := by positivity
  have hp : 1 ≤ 2^i.1.val := hp0
  dsimp [nodeRight] at hi
  nlinarith

theorem sum_completedNodes_finite {A : Type*} [AddCommMonoid A] {L M n : ℕ}
    (hn : n ≤ M) (f : BinaryNode L → A) :
    (∑ i ∈ completedNodes L n, f i) =
      ∑ i : Fin L × Fin M, if nodeRight (paddedNode i) ≤ n then f (paddedNode i) else 0 := by
  symm
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => paddedNode i)
  · intro i hi
    exact (mem_completedNodes _).mpr (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    apply Prod.ext
    · exact congrArg (fun k : BinaryNode L => k.1) hij
    · apply Fin.ext
      exact congrArg (fun k : BinaryNode L => k.2) hij
  · intro i hi
    have hh := (mem_completedNodes i).mp hi
    let j : Fin L × Fin M := (i.1,⟨i.2,completedNode_index_lt i (hh.trans hn)⟩)
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · exact hh
    · rfl
  · intro i hi
    rfl

theorem mem_dyadicBlock_interval {L M : ℕ} (i : Fin L × Fin M) (k : Fin M) :
    k ∈ dyadicBlock M i.1.val i.2 ↔
      nodeLeft (paddedNode i) ≤ k.val ∧ k.val < nodeRight (paddedNode i) := by
  have hp : 0 < 2^i.1.val := by positivity
  simp only [dyadicBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.div_eq_iff hp, nodeLeft, nodeRight, paddedNode]
  rw [Nat.add_mul, one_mul]
  omega

/-- A completed direct chord is the sum of its physical moves. -/
theorem dyadicBlock_telescopes {E : Type*} [AddCommGroup E] {L M : ℕ}
    (x : ℕ → E) (i : Fin L × Fin M) (hi : nodeRight (paddedNode i) ≤ M) :
    (∑ k ∈ dyadicBlock M i.1.val i.2, (x (k.val+1)-x k.val)) =
      x (nodeRight (paddedNode i))-x (nodeLeft (paddedNode i)) := by
  have hsum : (∑ k ∈ dyadicBlock M i.1.val i.2, (x (k.val+1)-x k.val)) =
      ∑ t ∈ Finset.Ico (nodeLeft (paddedNode i)) (nodeRight (paddedNode i)), (x (t+1)-x t) := by
    apply Finset.sum_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_Ico.mpr ((mem_dyadicBlock_interval i k).mp hk)
    · intro k hk j hj hkj
      exact Fin.ext hkj
    · intro t ht
      have ht' := Finset.mem_Ico.mp ht
      refine ⟨⟨t,ht'.2.trans_le hi⟩,?_,rfl⟩
      exact (mem_dyadicBlock_interval _ _).mpr ht'
    · intro k hk
      rfl
  rw [hsum]
  exact Finset.sum_Ico_sub x (nodeLeft_lt_right (paddedNode i)).le

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure Ω}

/-- Energy of precisely the nodes generated before a random capped end time.
The time is allowed to depend on the whole trajectory; selection is dominated
before expectation, without conditioning on future completion. -/
theorem completed_chord_energy (M L q : ℕ) (N : Ω → ℕ) (hN : Measurable N)
    (hcap : ∀ w, N w ≤ M) (x : Ω → ℕ → E) (a m : Fin M → Ω → E)
    (hx : ∀ w k, x w (k.val+1)-x w k.val = a k w+m k w)
    (ha : ∀ k, Integrable (a k) μ) (hm : ∀ k, Integrable (m k) μ)
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) μ)
    (hm2 : ∀ k, Integrable (fun w => ‖m k w‖^2) μ)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (ho : ∀ i j, i ≠ j → (∫ w, ⟪m i w,m j w⟫_ℝ ∂μ) = 0) :
    (∫ w, ∑ i ∈ completedNodes L (N w), ‖x w (nodeRight i)-x w (nodeLeft i)‖^2 ∂μ) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂μ)+(∫ w, ∑ k, ‖m k w‖^2 ∂μ)) := by
  have he (w : Ω) : (∑ i ∈ completedNodes L (N w), ‖x w (nodeRight i)-x w (nodeLeft i)‖^2) =
      ∑ i : Fin L × Fin M, if nodeRight (paddedNode i) ≤ N w then
        ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+m k w)‖^2 else 0 := by
    rw [sum_completedNodes_finite (hcap w)]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hh : nodeRight (paddedNode i) ≤ N w
    · rw [if_pos hh, if_pos hh, ← dyadicBlock_telescopes (x w) i (hh.trans (hcap w))]
      simp_rw [hx]
    · rw [if_neg hh, if_neg hh]
  simp_rw [he]
  exact integral_selected_dyadic_energy M L q a m (fun w i => nodeRight (paddedNode i) ≤ N w)
    (fun i => measurableSet_le measurable_const hN) ha hm ha2 hm2 hs ho

theorem completed_chord_energy_fresh_signs [IsProbabilityMeasure μ]
    (M L q : ℕ) (N : (Ω × (Fin M → Bool)) → ℕ) (hN : Measurable N)
    (hcap : ∀ w, N w ≤ M) (x : (Ω × (Fin M → Bool)) → ℕ → E)
    (a : Fin M → (Ω × (Fin M → Bool)) → E)
    (v : Ω → (i : Fin M) → (Fin i.val → Bool) → E)
    (hx : ∀ w k, x w (k.val+1)-x w k.val = a k w+mixedInnovation v k w)
    (ha : ∀ k, Integrable (a k) (μ.prod (signLaw M)))
    (hm : ∀ k, Integrable (mixedInnovation v k) (μ.prod (signLaw M)))
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) (μ.prod (signLaw M)))
    (hm2 : ∀ k, Integrable (fun w => ‖mixedInnovation v k w‖^2) (μ.prod (signLaw M)))
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q) :
    (∫ w, ∑ i ∈ completedNodes L (N w), ‖x w (nodeRight i)-x w (nodeLeft i)‖^2
      ∂μ.prod (signLaw M)) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂μ.prod (signLaw M))+
        (∫ w, ∑ k, ‖mixedInnovation v k w‖^2 ∂μ.prod (signLaw M))) :=
  completed_chord_energy M L q N hN hcap x a (mixedInnovation v) hx ha hm ha2 hm2 hs
    (mixedInnovation_orthogonal v hm hm2)

end
end SecondOrder
