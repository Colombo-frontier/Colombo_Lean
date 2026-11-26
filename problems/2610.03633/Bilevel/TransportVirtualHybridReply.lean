import Bilevel.ParametricPartialConjugate
import Bilevel.ParametricGradientMeasurable
import Bilevel.TransportHybridBatchReply

/-! Total Borel evaluation of the physical hybrid full lower reply. The
nonlinear conjugate term uses only a prebatch parameter and original
query; the quadratic correction uses the one frozen transport batch.
Exactness needs contraction only at the selected parameter. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open PrimitiveGeometry PartialLegendre EndpointTransportResponse TransportRound TransportNetwork EuclideanGaussian
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {A E U V : Type*} [MeasurableSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {n D a p : ℕ}

abbrev HybridQuery (E U V : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n D : ℕ) :=
  Joint (HybridOuter E U D) (HybridVariables U V n D)

abbrev FrozenBatch (n D a p : ℕ) :=
  Queries (n+1) D p × (Fin ((n+1)*(a+p)+(n+1)*(a+p)) → Space D)

variable [MeasurableSpace (HybridQuery E U V n D)] [BorelSpace (HybridQuery E U V n D)]
  [SecondCountableTopology (HybridQuery E U V n D)]
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]

def virtualHybridReply (G : A → HybridQuery E U V n D → HybridQuery E U V n D)
    (m δ c₀ cend : ℝ) (i : Fin p)
    (z : (A × HybridQuery E U V n D) × FrozenBatch n D a p) : HybridQuery E U V n D :=
  m • ParametricPartialConjugate.gradientReply G z.1+
    hybridLinearReadout n D m c₀ cend (z.1.2,batchHessian δ z.2.1 z.2.2 i)

theorem virtualHybridReply_measurable
    (G : A → HybridQuery E U V n D → HybridQuery E U V n D)
    (hG : Measurable (fun z : A × HybridQuery E U V n D => G z.1 z.2))
    (m δ c₀ cend : ℝ) (i : Fin p) :
    Measurable (virtualHybridReply (a:=a) G m δ c₀ cend i) := by
  have hpre := (ParametricPartialConjugate.gradientReply_measurable G hG).comp
    (measurable_fst : Measurable (fun z : (A × HybridQuery E U V n D) × FrozenBatch n D a p => z.1))
  have hb := (batchHessian_measurable (n:=n) (D:=D) (m:=a) δ i).comp
    (measurable_snd : Measurable (fun z : (A × HybridQuery E U V n D) × FrozenBatch n D a p => z.2))
  have hr := (hybridLinearReadout (E:=E) (U:=U) (V:=V) n D m c₀ cend).continuous.measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk hb)
  exact (hpre.const_smul m).add hr

omit [MeasurableSpace A] [MeasurableSpace (HybridQuery E U V n D)]
  [BorelSpace (HybridQuery E U V n D)] [SecondCountableTopology (HybridQuery E U V n D)]
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)] in
theorem virtualHybridReply_actual
    (G : A → HybridQuery E U V n D → HybridQuery E U V n D)
    (parameter : A) {K : NNReal} (hK : K < 1) (hG : LipschitzWith K (G parameter))
    (P : HybridQuery E U V n D → ℝ) (hP : ∀ w,HasGradientAt P (G parameter w) w)
    (m δ c₀ cend : ℝ) (z : Latent (n+1) D)
    (g : Generators (n+1) D a) (q : Queries (n+1) D p) (i : Fin p)
    (w : HybridQuery E U V n D) (hq : physical (fun v => q v i)=w.snd.fst.snd) :
    virtualHybridReply G m δ c₀ cend i ((parameter,w),(q,batch (augment g q) z)) =
      gradient (hybridLower hG hK P m
        (ChiHybrid.correction (hybridHessian m δ (physicalRotations z)) m)
        (hybridCoupling c₀ cend (physicalRotations z))) w := by
  rw [virtualHybridReply,ParametricPartialConjugate.gradientReply_eq_jointGradient G parameter hK hG]
  exact (hybridLower_gradient_from_batch m δ c₀ cend z P hG hK hP g q i w hq).symm

def virtualJointReply (upper G : A → HybridQuery E U V n D → HybridQuery E U V n D)
    (m δ c₀ cend : ℝ) (i : Fin p)
    (z : (A × HybridQuery E U V n D) × FrozenBatch n D a p) :
    HybridQuery E U V n D × HybridQuery E U V n D :=
  (upper z.1.1 z.1.2,virtualHybridReply G m δ c₀ cend i z)

theorem virtualJointReply_measurable
    (upper G : A → HybridQuery E U V n D → HybridQuery E U V n D)
    (hupper : Measurable (fun z : A × HybridQuery E U V n D => upper z.1 z.2))
    (hG : Measurable (fun z : A × HybridQuery E U V n D => G z.1 z.2))
    (m δ c₀ cend : ℝ) (i : Fin p) :
    Measurable (virtualJointReply (a:=a) upper G m δ c₀ cend i) :=
  (hupper.comp measurable_fst).prodMk (virtualHybridReply_measurable G hG m δ c₀ cend i)

section Scalar
variable [TopologicalSpace A] [OpensMeasurableSpace A]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]

theorem scalarVirtualJointReply_measurable (f P : A → HybridQuery E U V n D → ℝ)
    (hf : Continuous (Function.uncurry f)) (hP : Continuous (Function.uncurry P))
    (m δ c₀ cend : ℝ) (i : Fin p) :
    Measurable (virtualJointReply (a:=a) (fun parameter => gradient (f parameter))
      (fun parameter => gradient (P parameter)) m δ c₀ cend i) :=
  virtualJointReply_measurable _ _ (ParametricGradient.gradient_measurable f hf)
    (ParametricGradient.gradient_measurable P hP) m δ c₀ cend i
end Scalar

end Bilevel.TransportHierarchy
