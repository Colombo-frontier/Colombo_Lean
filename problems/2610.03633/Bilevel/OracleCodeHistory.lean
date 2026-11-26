import Bilevel.OracleCodeRead

/-! The same public causal syntax under arbitrary history-dependent laws.
Every call samples the full response kernel at the actual query and history,
then applies the hidden history update. Pure code cannot inspect that history.
This is a compositional kernel semantics; its arbitrary-program execution
bridge is a separate theorem, not an assumption of this definition. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode.History
open Stateful
set_option autoImplicit false
variable {Q O A B C H : Space}

def call (K : Kernel (Q × H) O) [IsMarkovKernel K]
    (update : (Q × H) × O → H) (hu : Measurable update) : Procedure Q H O where
  law := KernelMap.dependent K (fun z => (z.2,update z,1))
  markov := KernelMap.dependent_markov _ _
    (measurable_snd.prodMk (hu.prodMk measurable_const))

def denote (K : Kernel (Q × H) O) [IsMarkovKernel K]
    (update : (Q × H) × O → H) (hu : Measurable update) :
    {A B : Space} → Code Q O A B → Procedure A H B
  | _,_,.pure f hf => Procedure.pure f hf
  | _,_,.call => call K update hu
  | _,_,.bind p q => (denote K update hu p).bind (denote K update hu q)
  | _,_,.reparam p f hf => (denote K update hu p).reparam f hf
  | _,_,.choose p n hn => Procedure.choose (fun i => denote K update hu (p i)) n hn

theorem denote_map (K : Kernel (Q × H) O) [IsMarkovKernel K]
    (update : (Q × H) × O → H) (hu : Measurable update)
    (p : Code Q O A B) (f : prod A B → C) (hf : Measurable f) :
    denote K update hu (OracleCode.map p f hf) = (denote K update hu p).map f hf := rfl

theorem procedure_ext (p q : Procedure A H B) (h : p.law=q.law) : p=q := by
  cases p
  cases q
  cases h
  rfl

theorem call_law (K : Kernel (Q × H) O) [IsMarkovKernel K]
    (update : (Q × H) × O → H) (hu : Measurable update) (q : Q) (h : H) :
    (call K update hu).law (q,h)=(K (q,h)).map (fun o => (o,update ((q,h),o),1)) :=
  KernelMap.dependent_apply _ _ (measurable_snd.prodMk (hu.prodMk measurable_const)) _

theorem denote_read_law (K : Kernel (Q × H) O) [IsMarkovKernel K]
    (update : (Q × H) × O → H) (hu : Measurable update)
    (r : O → B) (hr : Measurable r) (q : Q) (h : H) :
    (denote K update hu (read r hr)).law (q,h)=
      (K (q,h)).map (fun o => (r o,update ((q,h),o),1)) := by
  rw [read,denote_map,Procedure.map_law]
  change ((call K update hu).law (q,h)).map (fun z => (r z.1,z.2))=_
  rw [call_law]
  have hm : Measurable (fun o : O => (o,update ((q,h),o),(1:ℕ))) :=
    measurable_id.prodMk ((hu.comp (measurable_const.prodMk measurable_id)).prodMk measurable_const)
  have hn : Measurable (fun z : Outcome O H => (r z.1,z.2)) :=
    (hr.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map hn hm]
  rfl

variable {E : Space} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E] {σ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
theorem denote_read_eq
    (Z : HistoryOracle (Query:=Q) (History:=H) (Obs:=O) (E:=E) σ) :
    denote Z.law Z.update Z.update_measurable (read Z.read Z.read_measurable)=Z.call := by
  apply procedure_ext
  ext z s hs
  rw [denote_read_law,HistoryOracle.call_law]

end Bilevel.OracleCode.History
