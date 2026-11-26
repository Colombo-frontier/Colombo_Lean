import Bilevel.MultiscaleFrameCompiler
import Bilevel.ChiSourceAbsoluteExpected

/-! The same actual single-frame Bernoulli execution gives the expected
query lower bound. Remaining inputs are scalar analytic calibration,
joint Borel identities, and a public numerical observer dimension budget. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.MultiscaleMean
open SingleFrameSource ChiHierarchyIndex ChiHierarchyExecution ChiHierarchyHaar CompensatedMean BorelAdaptive

variable {n D : ℕ}
  [MeasurableSpace (LowerSpace (EuclideanGaussian.Space D))]
  [BorelSpace (LowerSpace (EuclideanGaussian.Space D))]
  {Private State : Type*} [MeasurableSpace Private] [MeasurableSpace State]

theorem inner_expected_queries (P : Parameters (E:=EuclideanGaussian.Space D) n)
    (p ε cap : ℝ) (hp : 0<p) (hp1 : p≤1) (hε : 0<ε) (hcap : 0≤cap)
    (hsmall : P.R*Real.sqrt cap≤P.signalResolution/2)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D)
    (he : Measurable (fun z : InnerQuery (EuclideanGaussian.Space D) ×
      (SingleFrameSource.Store n (EuclideanGaussian.Space D) ×
        (SingleFrameSource.Store n (EuclideanGaussian.Space D) × Bool)) =>
      innerEvaluate P p z.1 z.2.1 z.2.2.1 z.2.2.2))
    (hr : Measurable (fun z : Orientations (counts n) 0 D × (InnerQuery (EuclideanGaussian.Space D) × Bool) =>
      innerFrameReply P p hD z.1 z.2.1 z.2.2))
    (hloss : Measurable (Function.uncurry (innerFrameLoss P hD)))
    (N r : ℕ) (b : ℝ)
    (hmax : ((n+1:ℕ):ℝ)/(16*p)≤(N:ℝ)) (hb : 0<b) (hb2 : b≤2)
    (hdim : (2*(N*batchSize (counts n) 0 1)+1)+(N*batchSize (counts n) 0 1)+(r+1)≤D)
    (hproduct : ((N*batchSize (counts n) 0 1:ℕ):ℝ)*(((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ)*b)≤1/2)
    (henergy : 2*((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ)*b≤cap)
    (hbudget : ((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ≥0∞)*
      GenieProtocol.failurePerQuery (totalColumns (counts n) 0) r b≤1/8)
    (hbarrier : ∀ a x,
      |WrappedChain.coordinates n P.R (frame hD a (Sum.inl ())) ((P.L/P.μ) • x) (Fin.last n)|<P.β →
        8*ε≤ innerFrameLoss P hD a x)
    (alg : Program State (InnerQuery (EuclideanGaussian.Space D)) (InnerReply (EuclideanGaussian.Space D))
      (EuclideanGaussian.Space D))
    (initial : Private → State) (hi : Measurable initial) (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (haccuracy : ∀ a,(∫⁻ z,ENNReal.ofReal (Function.uncurry (innerFrameLoss P hD)
      (seededStopped alg (innerFrameReply P p hD) initial (a,z)))
      ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))≤ENNReal.ofReal ε) :
    ∃ a : Orientations (counts n) 0 D,
      ENNReal.ofReal (((n+1:ℕ):ℝ)/(512*p))≤
        ∫⁻ z,seededCalls alg (innerFrameReply P p hD) initial (a,z)
          ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)) := by
  let point : EuclideanGaussian.Space D → EuclideanGaussian.Space D := fun x => (P.L/P.μ) • x
  have hm : Measurable point := by
    change Measurable (fun x : EuclideanGaussian.Space D => (P.L/P.μ) • x)
    exact measurable_const.smul measurable_id
  have hs : P.R*Real.sqrt cap≤P.β/8 := by
    have hh := P.signalResolution_small
    linarith [P.β_pos]
  have hN : (ChiTreeProgress.capacity (counts n) 1 0:ℕ)/(16*p)≤(N:ℝ) := by
    simpa only [capacity_eq] using hmax
  have hlocal := sourceGood_reply_from_energy (hD:=hD) alg (innerEvaluate P p) he
    innerVector innerVector_measurable (macroTerminal P.R point)
    (macroTerminal_measurable P.R point hm) initial (innerFrameReply P p hD) cap
    (innerFrame_reply_from_energy P p cap hD hcap hsmall)
  have hh := expected_queries_of_source_replies_abs (counts n) 0 D 1 hD alg
    (innerEvaluate P p) he (fun k z => innerVector k z.1)
    (fun k => (innerVector_measurable k).comp measurable_fst)
    P.R P.β cap (P.β_pos.trans_le P.β_le_R) P.β_pos hcap hs
    point hm initial hi (innerFrameReply P p hD) hr
    (Function.uncurry (innerFrameLoss P hD)) hloss (fun z => norm_nonneg _)
    ρ p ε hp hp1 hε N r b hN hb hb2 hdim hproduct henergy hbudget
    (fun m _ z hz t ht _ => hlocal m z hz t ht) hbarrier haccuracy
  simpa only [Nat.zero_add,capacity_eq] using hh

end Bilevel.MultiscaleMean
