import Bilevel.ChiSourceCappedBarrier
import Bilevel.BorelAdaptiveExpectedInformation

/-! A single fixed-dimensional source prior gives an expected lower bound
for the actual original adaptive program, including infinite executions.
Only deterministic source reply/barrier certificates remain to instantiate;
observer and activation probabilities are derived from their actual laws. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian

variable {Private S Q O Y : Type*} [MeasurableSpace Private] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

theorem expected_queries_of_source_replies
    (counts : ℕ → ℕ) (J D m : ℕ)
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ l,Measurable (queries l))
    (R width cap : ℝ) (hR : 0<R) (hw : 0<width) (hcap : 0≤cap) (hsmall : R*Real.sqrt cap≤width/8)
    (point : Y → Space D) (hpoint : Measurable point) (initial : Private → S) (hi : Measurable initial)
    (original : Orientations counts J D → Q → Bool → O)
    (hr : Measurable (fun p : Orientations counts J D × (Q × Bool) => original p.1 p.2.1 p.2.2))
    (loss : Orientations counts J D × Y → ℝ) (hloss : Measurable loss) (hpos : ∀ z,0≤loss z)
    (ρ : Measure Private) [IsProbabilityMeasure ρ] (p ε : ℝ) (hp0 : 0<p) (hp1 : p≤1) (hε : 0<ε)
    (N r : ℕ) (b : ℝ)
    (hmax : (ChiTreeProgress.capacity counts (J+1) 0:ℕ)/(16*p)≤(N:ℝ))
    (hb : 0<b) (hb2 : b≤2)
    (hdim : (2*(N*batchSize counts J m)+1)+(N*batchSize counts J m)+(r+1)≤D)
    (hproduct : ((N*batchSize counts J m:ℕ):ℝ)*(((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b)≤1/2)
    (henergy : 2*((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b≤cap)
    (hbudget : ((2*(N*batchSize counts J m)+1:ℕ):ℝ≥0∞)*
      GenieProtocol.failurePerQuery (totalColumns counts J) r b≤1/8)
    (hlocal : ∀ n≤N,∀ z : Sample (Orientations counts J D) Private Bool,
      seedGood counts J D m hD A evaluate he queries hq (macroTerminal R point)
        (macroTerminal_measurable R point hpoint) initial n cap z → ∀ t<n,
      let s := run counts J A evaluate (columns hD z.1) (initial z.2.1) z.2.2 t
      A.halt s.1=false → original z.1 (A.query s.1) (z.2.2 t)=
        (response counts J evaluate (columns hD z.1) (A.query s.1,s.2) (z.2.2 t)).1)
    (hbarrier : ∀ a y,WrappedChain.coordinates (counts 0) R (frame hD a (Sum.inl ()))
      (point y) (Fin.last (counts 0))<width → 8*ε≤loss (a,y))
    (haccuracy : ∀ a,(∫⁻ s,ENNReal.ofReal (loss (seededStopped A original initial (a,s)))
      ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))≤ENNReal.ofReal ε) :
    ∃ a : Orientations counts J D,
      ENNReal.ofReal ((ChiTreeProgress.capacity counts (J+1) 0:ℕ)/(512*p))≤
        ∫⁻ s,seededCalls A original initial (a,s) ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)) := by
  let bad := fun n : ℕ => {z : Sample (Orientations counts J D) Private Bool |
    ¬seedGood counts J D m hD A evaluate he queries hq (macroTerminal R point)
      (macroTerminal_measurable R point hpoint) initial n cap z}
  let activation := fun n : ℕ => {z : Sample (Orientations counts J D) Private Bool |
    seedActivation counts J D hD A evaluate initial n (ChiTreeProgress.capacity counts (J+1) 0) z}
  have hinfo : ∀ n : ℕ,(n:ℝ)≤(ChiTreeProgress.capacity counts (J+1) 0:ℕ)/(16*p) →
      MeasurableSet (bad n) ∧ MeasurableSet (activation n) ∧
      ((law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real (bad n)≤1/8 ∧
      ((law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real (activation n)≤1/16 ∧
      (∀ᵐ z ∂(law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))),
        z∉bad n → z∉activation n → 8*ε≤loss (seededCapped A original initial n z)) := by
    intro n hn
    have hnN : n≤N := Nat.cast_le.mp (hn.trans hmax)
    refine ⟨(seedGood_measurable counts J D m hD A evaluate he queries hq (macroTerminal R point)
      (macroTerminal_measurable R point hpoint) initial hi n cap).compl,
      seedActivation_measurable counts J D hD A evaluate he initial hi n (ChiTreeProgress.capacity counts (J+1) 0),
      seedGood_failure_eighth counts J D m hD A evaluate he queries hq (macroTerminal R point)
        (macroTerminal_measurable R point hpoint) initial ρ hi p hp1 N n r hnN b cap hb hb2 hdim hproduct henergy hbudget,
      seedActivation_failure counts J D hD A evaluate initial ρ p hp0 hp1 n
        (ChiTreeProgress.capacity counts (J+1) 0) (ChiTreeProgress.capacity_pos counts (J+1) 0) hn,?_⟩
    exact Filter.Eventually.of_forall (fun z hg ha =>
      capped_barrier_on_good counts J D m hD A evaluate he queries hq R width cap point hpoint initial original loss ε
        hR hw hcap hsmall n z (not_not.mp hg) ha (hlocal n hnN z (not_not.mp hg)) (hbarrier z.1))
  obtain ⟨a,_,ha⟩ := fixed_instance_expected_seededCalls A original hr initial hi (law counts J D)
    (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))) (fun _ => True)
    (Filter.Eventually.of_forall (fun _ => trivial)) loss
    (hloss.comp (seededStopped_measurable A original hr initial hi)) hpos
    (ChiTreeProgress.capacity counts (J+1) 0) (ChiTreeProgress.capacity_pos counts (J+1) 0)
    p ε hp0 hε bad activation hinfo (fun a _ => haccuracy a)
  exact ⟨a,ha⟩

end Bilevel.ChiHierarchyHaar
