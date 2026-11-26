import RandomizedExperiment254
import SignVector254

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Paper254

/-- The stationary dimension lower bound, including arbitrary measurable
learner randomness and an oblivious deterministic hard instance. -/
theorem static_dimension_lower {d T : ℕ} (hd : 0 < d) (hT : d^2 ≤ T)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → OnlineLearner (ballDomain d) T) (hA : SeedMeasurable A) :
    ∃ (s : Fin T → Fin d × Bool) (v : Fin T → (ballDomain d).carrier),
      pathLength v = 0 ∧ (d : ℝ)/256 ≤ ∫ ω, regret (A ω) (hardSequence s) v ∂μ := by
  classical
  let θ : ℝ := 1/(8*Real.sqrt (d : ℝ))
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt := Real.sq_sqrt hd0.le
  have hsqrtpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd0
  have hsignal : (d : ℝ)*θ^2 = 1/64 := by
    dsimp [θ]
    field_simp
    nlinarith
  have hθball : (d : ℝ)*θ^2 ≤ 1/4 := by linarith
  have hθ : |θ| ≤ 1 := by
    apply abs_le.mpr
    have hh := mul_nonneg (show 0 ≤ (d : ℝ)-1 by linarith) (sq_nonneg θ)
    constructor <;> nlinarith
  let query : Fin T → Fin d := fun t => ⟨t.val%d,Nat.mod_lt t.val hd⟩
  let u := fun s : Fin d → Bool => fun _t : Fin T => signVectorInBall θ hθball s
  let good := (Finset.univ : Finset (Fin T)).filter (fun t => t.val < d^2)
  have hgood : good.card = d^2 := by
    change ((Finset.univ : Finset (Fin T)).filter (fun t => t.val < d^2)).card = _
    rw [← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le hT
  have hinfo : ∀ t ∈ good, (∑ i : Fin t.val, if query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩ = query t then θ^2 else 0) ≤ 1/32 := by
    intro t ht
    have htt := (Finset.mem_filter.mp ht).2
    have hcount := prefix_mod_information d d t.val hd (by nlinarith) (t.val%d) θ
    simp only [query,Fin.mk.injEq]
    linarith
  obtain ⟨s,v,hpath,hreg⟩ := randomized_hard_experiment_lower μ θ hθ query query A hA u
    (by intro s t; rfl) 0 (by intro s; simp [u,pathLength_constant]) good hinfo
  refine ⟨s,v,le_antisymm hpath (pathLength_nonneg v),?_⟩
  rw [hgood] at hreg
  norm_num only [Nat.cast_pow] at hreg
  have hh := congrArg (fun x : ℝ => (d : ℝ)*x/4) hsignal
  nlinarith

end Paper254
#print axioms Paper254.static_dimension_lower
