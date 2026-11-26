import RandomizedExperiment254
import PaddedSign254
import BlockSchedule254

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Paper254

/-- Fully constructed block-hypercube hard instance. The scalar premises
are precisely the norm, information, horizon, and movement budgets. -/
theorem block_hypercube_lower {d T m K n : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) (hK : 0 < K) (hn : 0 < n) (horizon : K*(n*m) ≤ T)
    (θ a P : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 1/2)
    (hnorm : (m : ℝ)*θ^2 ≤ a^2) (hinfo : (n : ℝ)*θ^2 ≤ 1/32) (hmove : 2*a*K ≤ P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → OnlineLearner (ballDomain d) T) (hA : SeedMeasurable A) :
    ∃ (s : Fin T → Fin d × Bool) (v : Fin T → (ballDomain d).carrier),
      pathLength v ≤ P ∧ ((K*(n*m) : ℕ) : ℝ)*θ^2/4 ≤ ∫ ω, regret (A ω) (hardSequence s) v ∂μ := by
  classical
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hball : (m : ℝ)*θ^2 ≤ 1/4 := by nlinarith
  have habs : |θ| ≤ 1 := by
    apply abs_le.mpr
    have hh := mul_nonneg (show 0 ≤ (m : ℝ)-1 by linarith) (sq_nonneg θ)
    constructor <;> nlinarith
  let b := fun t : Fin T => blockIndex K n m hK t.val
  let j := fun t : Fin T => (⟨t.val%m,Nat.mod_lt t.val hm⟩ : Fin m)
  let query := fun t : Fin T => (b t,j t)
  let coordinate := fun t : Fin T => (⟨(j t).val, Nat.lt_of_lt_of_le (j t).isLt hmd⟩ : Fin d)
  let vec := fun s : Fin K × Fin m → Bool => fun k : Fin K =>
    paddedSignInBall hmd θ hball (fun i => s (k,i))
  let u := fun s : Fin K × Fin m → Bool => fun t : Fin T => vec s (b t)
  let good := (Finset.univ : Finset (Fin T)).filter (fun t => t.val < K*(n*m))
  have hu : ∀ s t, (u s t).val (coordinate t) = signedMean θ (s (query t)) := by
    intro s t
    change (if hj : (j t).val < m then signedMean θ (s (b t,⟨(j t).val,hj⟩)) else 0) = _
    simp only [dif_pos (j t).isLt]
    rfl
  have hpath : ∀ s, pathLength (u s) ≤ P := by
    intro s
    have hh := monotone_block_path_bound (vec s) b
      (fun _ _ h => blockIndex_monotone K n m hK h) a ha
      (fun k => paddedSign_norm_bound hmd θ a ha hnorm (fun i => s (k,i)))
    exact hh.trans hmove
  have hc : good.card = K*(n*m) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le horizon
  have hi : ∀ t ∈ good, (∑ i : Fin t.val, if query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩ = query t then θ^2 else 0) ≤ 1/32 := by
    intro t ht
    have htt : t.val < K*(n*m) := (Finset.mem_filter.mp ht).2
    have he : ∀ i : Fin t.val, query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩ = query t ↔
        i.val/(n*m) = t.val/(n*m) ∧ i.val%m = t.val%m := by
      intro i
      simp only [query, Prod.mk.injEq, Fin.ext_iff, b, j]
      rw [blockIndex_before_end K n m i.val hK hn hm (Nat.lt_trans i.isLt htt),
        blockIndex_before_end K n m t.val hK hn hm htt]
    simp_rw [he]
    exact (block_mod_information m n t.val hm hn θ).trans hinfo
  obtain ⟨s,v,hp,hr⟩ := randomized_hard_experiment_lower μ θ habs query coordinate A hA u hu P hpath good hi
  rw [hc] at hr
  exact ⟨s,v,hp,hr⟩

end Paper254
#print axioms Paper254.block_hypercube_lower
