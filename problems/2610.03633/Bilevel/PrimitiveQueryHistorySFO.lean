import Bilevel.PrimitiveQueryModel
import Bilevel.HistorySFOFull
import Bilevel.FreshOracleKernelMoments

/-! The actual fresh original-SFO instance as a history kernel. The two
full vectors retain their joint seed and are split only after sampling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry Stateful
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

def Instance.pairSample (q : G.X × G.Y) (c : I.Seed) : G.Reply :=
  I.reply () (pack q.1 q.2) c

theorem Instance.pairSample_measurable :
    Measurable (fun z : (G.X × G.Y) × I.Seed => I.pairSample z.1 z.2) := by
  have he : Measurable (fun z : (G.X × G.Y) × I.Seed =>
      (pack z.1.1 z.1.2,z.2)) :=
    (packLinear.continuous.measurable.comp measurable_fst).prodMk measurable_snd
  exact (I.upper.sample_measurable.prodMk I.lower.sample_measurable).comp he

theorem Instance.pairSample_seed_measurable (q : G.X × G.Y) : Measurable (I.pairSample q) :=
  I.pairSample_measurable.comp (measurable_const.prodMk measurable_id)

def Instance.pairKernel : Kernel ((G.X × G.Y) × Unit) G.Reply :=
  KernelMap.dependent (Kernel.const ((G.X × G.Y) × Unit) I.law)
    (fun z => I.pairSample z.1.1 z.2)

theorem Instance.pairKernel_map_measurable :
    Measurable (fun z : ((G.X × G.Y) × Unit) × I.Seed => I.pairSample z.1.1 z.2) :=
  I.pairSample_measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

instance Instance.pairKernel_markov : IsMarkovKernel I.pairKernel :=
  KernelMap.dependent_markov _ _ I.pairKernel_map_measurable

theorem Instance.pairKernel_apply (q : G.X × G.Y) (h : Unit) :
    I.pairKernel (q,h)=I.law.map (I.pairSample q) := by
  exact KernelMap.dependent_apply _ _ I.pairKernel_map_measurable (q,h)

def Instance.fullResponse (q : G.X × G.Y) (c : I.Seed) : FullResponse G.X G.Y :=
  splitResponse (I.pairSample q c)

theorem Instance.fullResponse_measurable :
    Measurable (fun z : (G.X × G.Y) × I.Seed => I.fullResponse z.1 z.2) :=
  splitResponse_measurable.comp I.pairSample_measurable

def Instance.historySFO : Stateful.HistorySFO
    (Query:=G.X × G.Y) (History:=Unit) (X:=G.X) (Y:=G.Y) σf σg :=
  Stateful.HistorySFO.ofFullVectorKernel I.pairKernel
    (fun q => I.upper.truth (pack q.1 q.2)) (fun q => I.lower.truth (pack q.1 q.2))
    (I.upper.truth_measurable.comp packLinear.continuous.measurable)
    (I.lower.truth_measurable.comp packLinear.continuous.measurable) σf σg
    (I.upper.kernel_good I.pairKernel I.pairSample I.pairSample_seed_measurable I.pairKernel_apply
      (fun q => pack q.1 q.2) Prod.fst measurable_fst (fun _ _ => rfl))
    (I.lower.kernel_good I.pairKernel I.pairSample I.pairSample_seed_measurable I.pairKernel_apply
      (fun q => pack q.1 q.2) Prod.snd measurable_snd (fun _ _ => rfl))
    (fun _ => ()) measurable_const

theorem Instance.historySFO_law (q : G.X × G.Y) :
    I.historySFO.law (q,())=I.law.map (I.fullResponse q) := by
  change (I.pairKernel.map splitResponse) (q,())=_
  rw [Kernel.map_apply _ splitResponse_measurable,I.pairKernel_apply,
    Measure.map_map splitResponse_measurable (I.pairSample_seed_measurable q)]
  rfl

theorem Instance.historySFO_update (z : ((G.X × G.Y) × Unit) × FullResponse G.X G.Y) :
    I.historySFO.update z=() := rfl

theorem Instance.historySFO_fx_truth (q : G.X × G.Y) :
    I.historySFO.fx.truth q=I.primitive.fx q.1 q.2 := by
  change (I.upper.truth (pack q.1 q.2)).fst=_
  rw [I.upper_truth]
  rfl

theorem Instance.historySFO_fy_truth (q : G.X × G.Y) :
    I.historySFO.fy.truth q=I.primitive.fy q.1 q.2 := by
  change (I.upper.truth (pack q.1 q.2)).snd=_
  rw [I.upper_truth]
  rfl

theorem Instance.historySFO_gx_truth (q : G.X × G.Y) :
    I.historySFO.gx.truth q=I.primitive.gx q.1 q.2 := by
  change (I.lower.truth (pack q.1 q.2)).fst=_
  rw [I.lower_truth]
  rfl

theorem Instance.historySFO_gy_truth (q : G.X × G.Y) :
    I.historySFO.gy.truth q=I.primitive.gy q.1 q.2 := by
  change (I.lower.truth (pack q.1 q.2)).snd=_
  rw [I.lower_truth]
  rfl

theorem Instance.historySFO_reads (o : FullResponse G.X G.Y) :
    I.historySFO.fx.read o=o.1.1 ∧ I.historySFO.fy.read o=o.1.2 ∧
    I.historySFO.gx.read o=o.2.1 ∧ I.historySFO.gy.read o=o.2.2 := ⟨rfl,rfl,rfl,rfl⟩

end Bilevel.PrimitiveQuery
