import Bilevel.ChiSourceTerminalMacro
import Bilevel.ChiSourceSeededEvents
import Bilevel.ChiSourceExecutionCoupling
import Bilevel.BorelAdaptivePrior
import Bilevel.MultiscaleRisk

/-! Same-run assembly of the source observer, Bernoulli activation, and
an actual capped original reply sequence. The remaining hypotheses are
deterministic: exact local full replies and the source macro-blind loss
barrier. No information-event probability is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian

variable {Private S Q O Y : Type*} [MeasurableSpace Private] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
variable (counts : ℕ → ℕ) (J D m : ℕ)
  (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
  (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
  (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
    evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ l,Measurable (queries l))
  (R width cap : ℝ) (point : Y → Space D) (hp : Measurable point) (initial : Private → S)
  (original : Orientations counts J D → Q → Bool → O)
  (loss : Orientations counts J D × Y → ℝ) (ε : ℝ)

omit [MeasurableSpace Private] in
theorem capped_barrier_on_good (hR : 0<R) (hw : 0<width) (hcap : 0≤cap)
    (hsmall : R*Real.sqrt cap≤width/8) (N : ℕ) (p : Sample (Orientations counts J D) Private Bool)
    (hgood : seedGood counts J D m hD A evaluate he queries hq (macroTerminal R point)
      (macroTerminal_measurable R point hp) initial N cap p)
    (hact : ¬seedActivation counts J D hD A evaluate initial N (ChiTreeProgress.capacity counts (J+1) 0) p)
    (hlocal : ∀ t<N,
      let z := run counts J A evaluate (columns hD p.1) (initial p.2.1) p.2.2 t
      A.halt z.1=false → original p.1 (A.query z.1) (p.2.2 t)=
        (response counts J evaluate (columns hD p.1) (A.query z.1,z.2) (p.2.2 t)).1)
    (hbarrier : ∀ y,WrappedChain.coordinates (counts 0) R (frame hD p.1 (Sum.inl ()))
      (point y) (Fin.last (counts 0))<width → 8*ε≤loss (p.1,y)) :
    8*ε≤loss (seededCapped A original initial N p) := by
  have hcount : (run counts J A evaluate (columns hD p.1) (initial p.2.1) p.2.2 N).2.1<
      ChiTreeProgress.capacity counts (J+1) 0 := Nat.lt_of_not_ge hact
  have hlast := sourceGood_macro_last hD A evaluate he queries hq R width cap hR hw hcap hsmall
    point hp (fun c : Private × (ℕ → Bool) => initial c.1) Prod.snd N (p.2,p.1) hgood hcount
  have heq := original_output_eq_of_local counts J A (fun _ => original p.1) evaluate (columns hD p.1)
    (initial p.2.1) p.2.2 N hlocal
  have hre (n : ℕ) : BorelAdaptive.run A (fun _ : FiniteColumns counts J (Space D) => original p.1)
      (columns hD p.1) p.2.2 (initial p.2.1) n=
      BorelAdaptive.run A original p.1 p.2.2 (initial p.2.1) n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [BorelAdaptive.run,ih,BorelAdaptive.step]
  rw [hre] at heq
  change 8*ε≤loss (p.1,A.output (BorelAdaptive.run A original p.1 p.2.2 (initial p.2.1) N))
  rw [show A.output (BorelAdaptive.run A original p.1 p.2.2 (initial p.2.1) N)=
      A.output (run counts J A evaluate (columns hD p.1) (initial p.2.1) p.2.2 N).1 from heq]
  exact hbarrier _ hlast

theorem capped_barrier_probability (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (hi : Measurable initial) (p : ℝ) (hp0 : 0<p) (hp1 : p≤1)
    (N n r : ℕ) (hn : n≤N) (b : ℝ) (hR : 0<R) (hw : 0<width) (hcap : 0≤cap)
    (hsmall : R*Real.sqrt cap≤width/8) (hb : 0<b) (hb2 : b≤2)
    (hdim : (2*(N*batchSize counts J m)+1)+(N*batchSize counts J m)+(r+1)≤D)
    (hproduct : ((N*batchSize counts J m:ℕ):ℝ)*(((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b)≤1/2)
    (henergy : 2*((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b≤cap)
    (hbudget : ((2*(N*batchSize counts J m)+1:ℕ):ℝ≥0∞)*
      GenieProtocol.failurePerQuery (totalColumns counts J) r b≤1/8)
    (horizon : (n:ℝ)≤(ChiTreeProgress.capacity counts (J+1) 0:ℕ)/(16*p))
    (hlocal : ∀ z : Sample (Orientations counts J D) Private Bool,
      seedGood counts J D m hD A evaluate he queries hq (macroTerminal R point)
        (macroTerminal_measurable R point hp) initial n cap z → ∀ t<n,
      let s := run counts J A evaluate (columns hD z.1) (initial z.2.1) z.2.2 t
      A.halt s.1=false → original z.1 (A.query s.1) (z.2.2 t)=
        (response counts J evaluate (columns hD z.1) (A.query s.1,s.2) (z.2.2 t)).1)
    (hbarrier : ∀ a y,WrappedChain.coordinates (counts 0) R (frame hD a (Sum.inl ()))
      (point y) (Fin.last (counts 0))<width → 8*ε≤loss (a,y)) :
    13/16≤((law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real
      {z | 8*ε≤loss (seededCapped A original initial n z)} := by
  let bad : Set (Sample (Orientations counts J D) Private Bool) :=
    {z | ¬seedGood counts J D m hD A evaluate he queries hq (macroTerminal R point)
      (macroTerminal_measurable R point hp) initial n cap z}
  let activation : Set (Sample (Orientations counts J D) Private Bool) :=
    {z | seedActivation counts J D hD A evaluate initial n (ChiTreeProgress.capacity counts (J+1) 0) z}
  have hm := (seedGood_measurable counts J D m hD A evaluate he queries hq (macroTerminal R point)
    (macroTerminal_measurable R point hp) initial hi n cap).compl
  have ha := seedActivation_measurable counts J D hD A evaluate he initial hi n (ChiTreeProgress.capacity counts (J+1) 0)
  have hb' := seedGood_failure_eighth counts J D m hD A evaluate he queries hq (macroTerminal R point)
    (macroTerminal_measurable R point hp) initial ρ hi p hp1 N n r hn b cap hb hb2 hdim hproduct henergy hbudget
  have ha' := seedActivation_failure counts J D hD A evaluate initial ρ p hp0 hp1 n
    (ChiTreeProgress.capacity counts (J+1) 0) (ChiTreeProgress.capacity_pos counts (J+1) 0) horizon
  have hg := MultiscaleRisk.good_probability
    ((law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))))
    bad activation hm ha hb' ha'
  apply hg.trans
  apply measureReal_mono
  intro z hz
  have hgood : seedGood counts J D m hD A evaluate he queries hq (macroTerminal R point)
      (macroTerminal_measurable R point hp) initial n cap z := by
    by_contra hh
    exact hz (Or.inl hh)
  have hact : ¬seedActivation counts J D hD A evaluate initial n (ChiTreeProgress.capacity counts (J+1) 0) z :=
    fun hh => hz (Or.inr hh)
  exact capped_barrier_on_good counts J D m hD A evaluate he queries hq R width cap point hp initial original loss ε
    hR hw hcap hsmall n z hgood hact (hlocal z hgood) (hbarrier z.1)
  all_goals exact measure_ne_top _ _

end Bilevel.ChiHierarchyHaar
