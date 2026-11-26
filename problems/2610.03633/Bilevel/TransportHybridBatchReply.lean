import Bilevel.TransportPhysicalBatchLower
import Bilevel.EndpointTransportHybridFormula

/-! The original hybrid lower reply splits into its prebatch partial-
conjugate gradient and a public linear readout of one frozen Hessian batch.
No inverse query is transported by this readout. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open PrimitiveGeometry PartialLegendre EndpointTransportResponse TransportRound TransportNetwork
set_option maxHeartbeats 900000
variable {E U V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def publicHybridCoupling (n D : ℕ) (c₀ cend : ℝ) :
    HybridOuter E U D →L[ℝ] HybridVariables U V n D :=
  hybridCoupling c₀ cend (fun _ => LinearIsometryEquiv.refl ℝ (Block D))

omit [CompleteSpace E] [CompleteSpace U] [CompleteSpace V] in
theorem hybridCoupling_public {n D : ℕ} (c₀ cend : ℝ) (z : Latent (n+1) D) :
    (hybridCoupling c₀ cend (physicalRotations z) : HybridOuter E U D →L[ℝ] HybridVariables U V n D)=
      publicHybridCoupling n D c₀ cend := by
  ext x
  rw [hybridCoupling_apply,endpointCoupling_public]
  rfl

def physicalHybridProjection (n D : ℕ) : HybridVariables U V n D →L[ℝ] Physical n D :=
  jointSndLinear.comp jointFstLinear

def physicalHybridInsertion (n D : ℕ) : Physical n D →L[ℝ] HybridVariables U V n D :=
  packLinear.comp ((packLinear.comp ((0 : Physical n D →L[ℝ] U).prod
    (ContinuousLinearMap.id ℝ (Physical n D)))).prod 0)

def hybridLinearReadout (n D : ℕ) (m c₀ cend : ℝ) :
    (Joint (HybridOuter E U D) (HybridVariables U V n D) × Physical n D) →L[ℝ]
      Joint (HybridOuter E U D) (HybridVariables U V n D) :=
  let Z := Joint (HybridOuter E U D) (HybridVariables U V n D)
  let x : (Z × Physical n D) →L[ℝ] HybridOuter E U D :=
    jointFstLinear.comp (ContinuousLinearMap.fst ℝ Z (Physical n D))
  let y : (Z × Physical n D) →L[ℝ] HybridVariables U V n D :=
    jointSndLinear.comp (ContinuousLinearMap.fst ℝ Z (Physical n D))
  let h : (Z × Physical n D) →L[ℝ] Physical n D := ContinuousLinearMap.snd ℝ Z (Physical n D)
  let C : HybridOuter E U D →L[ℝ] HybridVariables U V n D := publicHybridCoupling n D c₀ cend
  packLinear.comp ((-C.adjoint.comp y).prod
    ((physicalHybridInsertion n D).comp (h-m • (physicalHybridProjection n D).comp y)-C.comp x))

theorem hybridLinearReadout_apply {n D : ℕ} (m c₀ cend : ℝ)
    (w : Joint (HybridOuter E U D) (HybridVariables U V n D)) (h : Physical n D) :
    hybridLinearReadout n D m c₀ cend (w,h)=
      pack (-(publicHybridCoupling n D c₀ cend).adjoint w.snd)
        (pack (pack (0:U) (h-m • w.snd.fst.snd)) (0:V)-publicHybridCoupling n D c₀ cend w.fst) := rfl

theorem hybridLinearReadout_actual {n D : ℕ} (m δ c₀ cend : ℝ) (z : Latent (n+1) D)
    (w : Joint (HybridOuter E U D) (HybridVariables U V n D)) :
    hybridLinearReadout n D m c₀ cend (w,physicalHessian δ (physicalRotations z) w.snd.fst.snd)=
      ChiQuadratic.hessian (ChiHybrid.correction (hybridHessian m δ (physicalRotations z)) m)
        (hybridCoupling c₀ cend (physicalRotations z)) w := by
  rw [hybridLinearReadout_apply,ChiQuadratic.hessian_apply,hybrid_correction_apply,hybridCoupling_public]

theorem hybridLinearReadout_batch {n D a p : ℕ} (m δ c₀ cend : ℝ)
    (g : Generators (n+1) D a) (q : Queries (n+1) D p) (z : Latent (n+1) D) (i : Fin p)
    (w : Joint (HybridOuter E U D) (HybridVariables U V n D))
    (hq : physical (fun v => q v i)=w.snd.fst.snd) :
    hybridLinearReadout n D m c₀ cend (w,batchHessian δ q (batch (augment g q) z) i)=
      ChiQuadratic.hessian (ChiHybrid.correction (hybridHessian m δ (physicalRotations z)) m)
        (hybridCoupling c₀ cend (physicalRotations z)) w := by
  rw [batchHessian_actual,hq]
  exact hybridLinearReadout_actual m δ c₀ cend z w

theorem hybridLower_gradient_from_batch {n D a p : ℕ} (m δ c₀ cend : ℝ)
    (z : Latent (n+1) D)
    (P : Joint (HybridOuter E U D) (HybridVariables U V n D) → ℝ)
    {K : NNReal} {G : Joint (HybridOuter E U D) (HybridVariables U V n D) →
      Joint (HybridOuter E U D) (HybridVariables U V n D)}
    (hG : LipschitzWith K G) (hK : K<1) (hP : ∀ w,HasGradientAt P (G w) w)
    (g : Generators (n+1) D a) (q : Queries (n+1) D p) (i : Fin p)
    (w : Joint (HybridOuter E U D) (HybridVariables U V n D))
    (hq : physical (fun v => q v i)=w.snd.fst.snd) :
    gradient (hybridLower hG hK P m
      (ChiHybrid.correction (hybridHessian m δ (physicalRotations z)) m)
      (hybridCoupling c₀ cend (physicalRotations z))) w=
        m • jointGradient hG hK w+
          hybridLinearReadout n D m c₀ cend (w,batchHessian δ q (batch (augment g q) z) i) := by
  rw [hybridLower_gradient hG hK P hP m _ _
    (ChiHybrid.correction_symmetric _ m (hybridHessian_symmetric m δ (physicalRotations z))),
    hybridLinearReadout_batch m δ c₀ cend g q z i w hq]

end Bilevel.TransportHierarchy
