import Smoothness2601.FrameTruncation
import Smoothness2601.WrappedProfiles
import Smoothness2601.SineOracle
import Smoothness2601.SineScaling

/-! The actual finite-frame oracle response, defined also on clipped frames.
Its measurability and locality are proved from the constructed smooth profiles. -/
noncomputable section
namespace Smoothness2601.FrameTruncation
open ExtensiveChain Bilevel.PrimitiveGeometry
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def frameIsometry {n : ℕ} (U : Fin (n+1) → E) (hU : Orthonormal ℝ U) :
    ExtensiveChain.Space n →ₗᵢ[ℝ] E :=
  (synthesis U).toLinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal
    (by simpa only [Function.comp_def,ContinuousLinearMap.coe_coe,
          OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,synthesis_single] using hU)

omit [CompleteSpace E] in
theorem frameIsometry_apply {n : ℕ} (U : Fin (n+1) → E) (hU : Orthonormal ℝ U)
    (z : ExtensiveChain.Space n) : frameIsometry U hU z = synthesis U z := rfl

omit [CompleteSpace E] in
theorem frameIsometry_single {n : ℕ} (U : Fin (n+1) → E) (hU : Orthonormal ℝ U)
    (i : Fin (n+1)) : frameIsometry U hU (EuclideanSpace.single i 1) = U i := synthesis_single U i

theorem frameProjection_isometry {n : ℕ} (U : Fin (n+1) → E) (hU : Orthonormal ℝ U) :
    frameProjection (frameIsometry U hU) = coordinates U := rfl

theorem coordinates_joint_continuous (n : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × E => coordinates p.1 p.2) := by
  have he : (fun p : (Fin (n+1) → E) × E => coordinates p.1 p.2) =
      (fun p => ∑ i : Fin (n+1), ⟪p.1 i,p.2⟫ • EuclideanSpace.single i 1) := by
    funext p
    ext j
    change _ = (EuclideanSpace.proj (𝕜 := ℝ) j)
      (∑ i : Fin (n+1), ⟪p.1 i,p.2⟫ • EuclideanSpace.single i 1)
    simp [coordinates_apply,map_sum,EuclideanSpace.single_apply]
  rw [he]
  exact continuous_finset_sum _ fun i _ =>
    (((continuous_apply i).comp continuous_fst).inner continuous_snd).smul continuous_const

omit [CompleteSpace E] in
theorem synthesis_joint_continuous (n : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × ExtensiveChain.Space n => synthesis p.1 p.2) := by
  simp only [synthesis_apply]
  exact continuous_finset_sum _ fun i _ =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_snd).smul
      ((continuous_apply i).comp continuous_fst)

theorem carriedGradient_joint_continuous (R : ℝ) {n : ℕ}
    (g : ExtensiveChain.Space n → ExtensiveChain.Space n) (hg : Continuous g) :
    Continuous (fun p : (Fin (n+1) → E) × E =>
      RadialWrapper.carriedGradient R (coordinates p.1) g p.2) := by
  have hc := (Bilevel.RadialWrapper.compress_contDiff (E := E) R 0).continuous
  have hz := (coordinates_joint_continuous (E := E) n).comp
    (continuous_fst.prodMk (hc.comp continuous_snd))
  have hs := (synthesis_joint_continuous (E := E) n).comp
    (continuous_fst.prodMk (hg.comp hz))
  have hd := (Bilevel.RadialWrapper.compressDerivative_contDiff (E := E) R 0).continuous
  simpa only [RadialWrapper.carriedGradient,coordinates,ContinuousLinearMap.adjoint_adjoint]
    using (hd.comp continuous_snd).clm_apply hs

theorem extensive_profile_gradient (R M : ℝ) {n : ℕ} (U : Fin (n+1) → E) (w : E) :
    gradient (extensiveProfile R M U) w =
      RadialWrapper.wrappedGradient R (1/16) (coordinates U) (gradient (extensive M)) w :=
  (RadialWrapper.wrapped_hasGradientAt R (1/16) (coordinates U) (extensive M)
    (gradient (extensive M)) (fun z => (extensive_hasFDerivAt M z).differentiableAt.hasGradientAt) w).gradient

theorem frontier_profile_gradient (R : ℝ) {n : ℕ} (U : Fin (n+1) → E) (w : E) :
    gradient (frontierProfile R U) w =
      RadialWrapper.carriedGradient R (coordinates U) (gradient Cutoffs.frontier) w :=
  (RadialWrapper.carried_hasGradientAt R (coordinates U) Cutoffs.frontier
    (gradient Cutoffs.frontier) (fun z => (Cutoffs.actual_frontier_differentiable z).1.hasGradientAt) w).gradient

theorem extensive_gradient_joint_continuous (R M : ℝ) (n : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × E => gradient (extensiveProfile R M p.1) p.2) := by
  simp only [extensive_profile_gradient,RadialWrapper.wrappedGradient]
  exact (carriedGradient_joint_continuous R _
    (HardProfiles.gradient_differentiable ((extensive_contDiff M n).of_le
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top))).continuous).add
      (continuous_const.smul continuous_snd)

theorem frontier_gradient_joint_continuous (R : ℝ) (n : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × E => gradient (frontierProfile R p.1) p.2) := by
  simp only [frontier_profile_gradient]
  exact carriedGradient_joint_continuous R _
    (HardProfiles.gradient_differentiable (frontier_contDiff.of_le
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top))).continuous

theorem frontier_joint_continuous (R : ℝ) (n : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × E => frontierProfile R p.1 p.2) :=
  frontier_contDiff.continuous.comp
    ((coordinates_joint_continuous (E := E) n).comp (continuous_fst.prodMk
      ((Bilevel.RadialWrapper.compress_contDiff R 0).continuous.comp continuous_snd)))

def reply (R M amp scale c m a h q : ℝ) {n : ℕ} (U : Fin (n+1) → E)
    (query : Adaptive.Query E ℝ) (coin : Bool) : Joint E ℝ :=
  if query.1 then
    pack 0 (m*query.2.2)+(if coin then q⁻¹ else 0) •
      pack ((-m*a*h*Real.sin (query.2.2/h)) •
        (scale⁻¹ • gradient (frontierProfile R U) (scale⁻¹ • query.2.1)))
        ((-m*a*Real.cos (query.2.2/h))*frontierProfile R U (scale⁻¹ • query.2.1))
  else pack ((amp/scale) • gradient (extensiveProfile R M U) (scale⁻¹ • query.2.1)) c

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem clip_min {n : ℕ} (U : Fin (n+1) → E) (k : ℕ) :
    clip U (min (n+1) k) = clip U k := by
  funext i
  simp only [clip,lt_min_iff,i.isLt,true_and]

theorem reply_local (R M amp scale c m a h q : ℝ) {n : ℕ} (U : Fin (n+1) → E)
    (k : ℕ) (query : Adaptive.Query E ℝ) (coin : Bool)
    (htail : ∀ i : Fin (n+1), k ≤ i.val →
      |⟪U i,Bilevel.RadialWrapper.compress R (scale⁻¹ • query.2.1)⟫| ≤ 1/16) :
    reply R M amp scale c m a h q U query coin =
      reply R M amp scale c m a h q (clip U (min (n+1) (k+if coin then 1 else 0))) query coin := by
  rw [clip_min]
  cases coin
  · simp [reply,extensive_profile_clip R M U k _ htail]
  · have hA := extensive_profile_clip R M U (k+1) (scale⁻¹ • query.2.1)
      (fun i hi => htail i (by omega))
    have hB := frontier_profile_clip R U k (scale⁻¹ • query.2.1) htail
    simp [reply,hA,hB.1,hB.2]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem reply_measurable (R M amp scale c m a h q : ℝ) (n : ℕ) :
    Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      reply R M amp scale c m a h q p.1 p.2.1 p.2.2) := by
  have hx : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      scale⁻¹ • p.2.1.2.1) := by fun_prop
  have hy : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) => p.2.1.2.2) := by fun_prop
  have hz := measurable_fst.prodMk hx
  have hA := (extensive_gradient_joint_continuous (E := E) R M n).measurable.comp hz
  have hB := (frontier_joint_continuous (E := E) R n).measurable.comp hz
  have hgB := (frontier_gradient_joint_continuous (E := E) R n).measurable.comp hz
  have hcoin : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      if p.2.2 then q⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then q⁻¹ else (0:ℝ))).comp
      (measurable_snd.comp measurable_snd)
  have hlow : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      pack 0 (m*p.2.1.2.2)+(if p.2.2 then q⁻¹ else 0) •
        pack ((-m*a*h*Real.sin (p.2.1.2.2/h)) •
          (scale⁻¹ • gradient (frontierProfile R p.1) (scale⁻¹ • p.2.1.2.1)))
          ((-m*a*Real.cos (p.2.1.2.2/h))*frontierProfile R p.1 (scale⁻¹ • p.2.1.2.1))) := by
    apply Measurable.add
    · exact (packLinear (X := E) (Y := ℝ)).continuous.measurable.comp
        (measurable_const.prodMk (measurable_const.mul hy))
    · apply hcoin.smul
      exact (packLinear (X := E) (Y := ℝ)).continuous.measurable.comp
        (((measurable_const.mul (Real.continuous_sin.measurable.comp (hy.div_const h))).smul
          (measurable_const.smul hgB)).prodMk
          ((measurable_const.mul (Real.continuous_cos.measurable.comp (hy.div_const h))).mul hB))
  have hup : Measurable (fun p : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      pack ((amp/scale) • gradient (extensiveProfile R M p.1) (scale⁻¹ • p.2.1.2.1)) c) :=
    (packLinear (X := E) (Y := ℝ)).continuous.measurable.comp
      ((measurable_const.smul hA).prodMk measurable_const)
  exact Measurable.ite
    (measurableSet_singleton true |>.preimage (measurable_fst.comp (measurable_fst.comp measurable_snd))) hlow hup

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem reply_eq_scaled_sample {n : ℕ} (U : Fin (n+1) → E) (hU : Orthonormal ℝ U)
    {amp scale : ℝ} (ha : 0 ≤ amp) (hs : 0 < scale) {b : Budgets}
    (S : ((HardProfiles.profiles (frameIsometry U hU)).scaled ha hs).Calibration b)
    (q : ℝ) (query : Adaptive.Query E ℝ) (coin : Bool) :
    reply (chainRadius HardProfiles.radiusConstant n) chainAmplitude amp scale
      S.c S.m S.a S.h q U query coin =
    FreshBernoulli.sample (((HardProfiles.profiles (frameIsometry U hU)).scaled ha hs).population S)
      (fun query => ((HardProfiles.profiles (frameIsometry U hU)).scaled ha hs).signal S.m S.a S.h
        (pack query.2.1 query.2.2)) q query coin := by
  let F := (HardProfiles.profiles (frameIsometry U hU)).scaled ha hs
  rcases query with ⟨flag,x,y⟩
  cases flag
  · rw [FreshBernoulli.sample_upper]
    rfl
  · rw [FreshBernoulli.sample_lower]
    have hb : Adaptive.trueGradient (F.population S) (true,(x,y))-
        F.signal S.m S.a S.h (pack x y) = pack 0 (S.m*y) := by
      change SineGeometry.lowerGradient F.B F.gB S.m S.a S.h (pack x y)-
        F.signal S.m S.a S.h (pack x y) = _
      rw [F.lowerGradient_decompose]
      exact add_sub_cancel_right _ _
    change _ = BernoulliOracle.response q
      (Adaptive.trueGradient (F.population S) (true,(x,y))-F.signal S.m S.a S.h (pack x y))
      (F.signal S.m S.a S.h (pack x y)) coin
    rw [hb]
    rfl

end Smoothness2601.FrameTruncation
