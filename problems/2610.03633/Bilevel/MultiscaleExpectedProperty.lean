import Bilevel.MultiscaleCompilerBorel
import Bilevel.MultiscaleRateProperty

/-! Actual original-call property for every Borel adaptive algorithm and
private seed, with arbitrary output and infinite-call executions allowed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.MultiscaleMean
open SingleFrameSource ChiHierarchyIndex ChiHierarchyExecution ChiHierarchyHaar CompensatedMean BorelAdaptive
variable {n D : ℕ}

theorem inner_expected_property (P : Parameters (E:=EuclideanGaussian.Space D) n)
    (p ε cap : ℝ) (hp : 0<p) (hp1 : p≤1) (hε : 0<ε) (hcap : 0≤cap)
    (hsmall : P.R*Real.sqrt cap≤P.signalResolution/2)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D)
    (N r : ℕ) (b : ℝ)
    (hmax : ((n+1:ℕ):ℝ)/(16*p)≤(N:ℝ)) (hb : 0<b) (hb2 : b≤2)
    (hdim : (2*(N*batchSize (counts n) 0 1)+1)+(N*batchSize (counts n) 0 1)+(r+1)≤D)
    (hproduct : ((N*batchSize (counts n) 0 1:ℕ):ℝ)*(((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ)*b)≤1/2)
    (henergy : 2*((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ)*b≤cap)
    (hbudget : ((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ≥0∞)*
      GenieProtocol.failurePerQuery (totalColumns (counts n) 0) r b≤1/8)
    (hbarrier : ∀ a x,
      |WrappedChain.coordinates n P.R (frame hD a (Sum.inl ())) ((P.L/P.μ) • x) (Fin.last n)|<P.β →
        8*ε≤ innerFrameLoss P hD a x) :
    InnerRateProperty.{u,v} P hD p hp1 ε (((n+1:ℕ):ℝ)/(512*p)) := by
  intro instM instB Private State instP instS alg initial hi ρ instρ hacc
  exact inner_expected_queries P p ε cap hp hp1 hε hcap hsmall hD
    (innerEvaluate_measurable P p) (innerFrameReply_measurable P p hD) (innerFrameLoss_measurable P hD)
    N r b hmax hb hb2 hdim hproduct henergy hbudget hbarrier alg initial hi ρ hacc

end Bilevel.MultiscaleMean
