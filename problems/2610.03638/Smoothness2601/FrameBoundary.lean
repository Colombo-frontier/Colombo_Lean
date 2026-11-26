import Smoothness2601.FrameResponse

/-! The same deferred-prefix locality for the boundary construction, where
the upper gradient carries the Bernoulli frontier and the lower oracle is exact. -/
noncomputable section
namespace Smoothness2601.FrameBoundary
open FrameTruncation ExtensiveChain Bilevel.PrimitiveGeometry
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def reply (R M s scale m q : ℝ) {n : ℕ} (U : Fin (n+1) → E)
    (query : Adaptive.Query E ℝ) (coin : Bool) : Joint E ℝ :=
  if query.1 then pack 0 (m*query.2.2) else
    pack (s • gradient (extensiveProfile R M U) (scale⁻¹ • query.2.1)+
      (if coin then q⁻¹ else 0) • (s • gradient (frontierProfile R U) (scale⁻¹ • query.2.1))) 0

theorem reply_local (R M s scale m q : ℝ) {n : ℕ} (U : Fin (n+1) → E)
    (k : ℕ) (query : Adaptive.Query E ℝ) (coin : Bool)
    (htail : ∀ i : Fin (n+1), k ≤ i.val →
      |⟪U i,Bilevel.RadialWrapper.compress R (scale⁻¹ • query.2.1)⟫| ≤ 1/16) :
    reply R M s scale m q U query coin =
      reply R M s scale m q (clip U (min (n+1) (k+if coin then 1 else 0))) query coin := by
  rw [clip_min]
  cases coin
  · simp [reply,extensive_profile_clip R M U k _ htail]
  · have hA := extensive_profile_clip R M U (k+1) (scale⁻¹ • query.2.1)
      (fun i hi => htail i (by omega))
    have hB := frontier_profile_clip R U k (scale⁻¹ • query.2.1) htail
    simp [reply,hA,hB.2]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem reply_measurable (R M s scale m q : ℝ) (n : ℕ) :
    Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      reply R M s scale m q p.1 p.2.1 p.2.2) := by
  have hx : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      scale⁻¹ • p.2.1.2.1) := by fun_prop
  have hy : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) => p.2.1.2.2) := by fun_prop
  have hz := measurable_fst.prodMk hx
  have hA := (extensive_gradient_joint_continuous (E := E) R M n).measurable.comp hz
  have hB := (frontier_gradient_joint_continuous (E := E) R n).measurable.comp hz
  have hcoin : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      if p.2.2 then q⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then q⁻¹ else (0:ℝ))).comp
      (measurable_snd.comp measurable_snd)
  have hlow : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      pack (0:E) (m*p.2.1.2.2)) :=
    (packLinear (X := E) (Y := ℝ)).continuous.measurable.comp
      (measurable_const.prodMk (measurable_const.mul hy))
  have hup : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      pack (s • gradient (extensiveProfile R M p.1) (scale⁻¹ • p.2.1.2.1)+
        (if p.2.2 then q⁻¹ else 0) • (s • gradient (frontierProfile R p.1) (scale⁻¹ • p.2.1.2.1))) (0:ℝ)) :=
    (packLinear (X := E) (Y := ℝ)).continuous.measurable.comp
      (((measurable_const.smul hA).add (hcoin.smul (measurable_const.smul hB))).prodMk measurable_const)
  exact Measurable.ite
    (measurableSet_singleton true |>.preimage (measurable_fst.comp (measurable_fst.comp measurable_snd))) hlow hup

end Smoothness2601.FrameBoundary
