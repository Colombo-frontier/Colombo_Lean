import LowerScaleParameters254
import EffectiveRoot254

noncomputable section
open MeasureTheory
namespace Paper254

theorem effective_dimension_lower {d T m : ℕ} (hm : 0 < m) (hmd : m ≤ d) (hT : 0 < T)
    (P : ℝ) (hP : 0 ≤ P) (hlo : 4*m/Real.sqrt T ≤ P) (hhi : P ≤ T/(8*(m : ℝ)^2))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → OnlineLearner (ballDomain d) T) (hA : SeedMeasurable A) :
    ∃ (s : Fin T → Fin d × Bool) (v : Fin T → (ballDomain d).carrier),
      pathLength v ≤ P ∧ unloggedRate m T P/2048 ≤ ∫ ω, regret (A ω) (hardSequence s) v ∂μ := by
  let r := ((T : ℝ)*P^2/(m : ℝ)^2)^(1/3 : ℝ)
  obtain ⟨hr,hbudget,hbalance,hrate⟩ := effective_root_conditions m T hm hT P hP hlo hhi
  obtain ⟨hK,hn,hfit,hfill,hKlo,hKhi,hKm2⟩ := lower_block_integer_parameters m T hm r hr hbudget
  let K := ⌊r⌋₊
  let n := T/(K*m)
  have hpath : (K : ℝ)^3*(m : ℝ)^2 ≤ T*P^2 := by
    have hc : (K : ℝ)^3 ≤ r^3 := by
      have h0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have hh := mul_nonneg (show 0 ≤ r-K by linarith)
        (show 0 ≤ r^2+r*K+(K : ℝ)^2 by positivity)
      nlinarith
    have hm' := mul_le_mul_of_nonneg_right hc (sq_nonneg (m : ℝ))
    linarith
  obtain ⟨θ,a,ha,ha2,hnorm,hinfo,hmove,hvalue⟩ := lower_block_signal m T K n hm hT hK hfit hfill hKm2 P hP hpath
  obtain ⟨s,v,hp,hreg⟩ := block_hypercube_lower hm hmd hK hn hfit θ a P ha ha2 hnorm hinfo hmove μ A hA
  refine ⟨s,v,hp,?_⟩
  have hm' := mul_le_mul_of_nonneg_right hKlo (Nat.cast_nonneg m (α := ℝ))
  rw [hrate]
  linarith

end Paper254
#print axioms Paper254.effective_dimension_lower
