import Bilevel.BorelAdaptiveCalls

/-! Actual/virtual transcript coupling for a Borel adaptive algorithm.
The virtual oracle carries additional disclosed data, returns a full oracle
reply, and updates that data. Equality of the local full replies on a blind
event implies equality of every algorithm state and capped output before
the first failure. The source-specific local reply identity remains explicit. -/
noncomputable section
open MeasureTheory
namespace Bilevel.BorelAdaptive

variable {S Q O Y I C D : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace C] [MeasurableSpace D]

def virtualStep (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (i : I) (c : C) (s : S × D) : S × D :=
  if A.halt s.1 then s else
    let reply := observe i (A.query s.1) c s.2
    (A.update (s.1,reply.1),reply.2)

def virtualRun (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (i : I) (draws : ℕ → C) (initial : S × D) : ℕ → S × D
  | 0 => initial
  | n+1 => virtualStep A observe i (draws n) (virtualRun A observe i draws initial n)

theorem virtualStep_measurable (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (ho : Measurable (fun p : I × (Q × (C × D)) => observe p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Measurable (fun p : (I × C) × (S × D) => virtualStep A observe p.1.1 p.1.2 p.2) := by
  have hs : Measurable (fun p : (I × C) × (S × D) => p.2.1) := measurable_fst.comp measurable_snd
  have hh := (A.halt_measurable.comp hs) (measurableSet_singleton true)
  have hr := ho.comp ((measurable_fst.comp measurable_fst).prodMk
    ((A.query_measurable.comp hs).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))))
  exact measurable_snd.ite hh
    ((A.update_measurable.comp (hs.prodMk (measurable_fst.comp hr))).prodMk (measurable_snd.comp hr))

theorem virtualRun_measurable (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (ho : Measurable (fun p : I × (Q × (C × D)) => observe p.1 p.2.1 p.2.2.1 p.2.2.2)) (n : ℕ) :
    Measurable (fun p : Sample I (S × D) C => virtualRun A observe p.1 p.2.2 p.2.1 n) := by
  induction n with
  | zero => exact measurable_fst.comp measurable_snd
  | succ n ih =>
    exact (virtualStep_measurable A observe ho).comp
      ((measurable_fst.prodMk ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd))).prodMk ih)

def BlindRun (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (Good : I → Q → C → D → Prop) (p : Sample I (S × D) C) (n : ℕ) : Prop :=
  ∀ t<n, let s := virtualRun A observe p.1 p.2.2 p.2.1 t
    A.halt s.1=false → Good p.1 (A.query s.1) (p.2.2 t) s.2

theorem blindRun_measurable (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (ho : Measurable (fun p : I × (Q × (C × D)) => observe p.1 p.2.1 p.2.2.1 p.2.2.2))
    (Good : I → Q → C → D → Prop)
    (hG : MeasurableSet {p : I × (Q × (C × D)) | Good p.1 p.2.1 p.2.2.1 p.2.2.2}) (n : ℕ) :
    MeasurableSet {p : Sample I (S × D) C | BlindRun A observe Good p n} := by
  have ht (t : ℕ) : MeasurableSet {p : Sample I (S × D) C |
      A.halt (virtualRun A observe p.1 p.2.2 p.2.1 t).1≠false ∨
      Good p.1 (A.query (virtualRun A observe p.1 p.2.2 p.2.1 t).1) (p.2.2 t)
        (virtualRun A observe p.1 p.2.2 p.2.1 t).2} := by
    have hs := virtualRun_measurable A observe ho t
    have hh := ((A.halt_measurable.comp (measurable_fst.comp hs)) (measurableSet_singleton false)).compl
    have hg := (measurable_fst.prodMk ((A.query_measurable.comp (measurable_fst.comp hs)).prodMk
      (((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_snd.comp hs)))) hG
    exact hh.union hg
  have hm := MeasurableSet.iInter (fun t : Fin n => ht t)
  convert hm using 1
  ext p
  simp only [BlindRun,Set.mem_setOf_eq,Set.mem_iInter]
  constructor
  · intro h t
    exact (imp_iff_not_or).mp (h t t.isLt)
  · intro h t ht
    exact (imp_iff_not_or).mpr (h ⟨t,ht⟩)

omit [MeasurableSpace I] [MeasurableSpace C] [MeasurableSpace D] in
theorem run_eq_virtual_of_blind (A : Program S Q O Y)
    (response : I → Q → C → O) (observe : I → Q → C → D → O × D)
    (Good : I → Q → C → D → Prop)
    (hlocal : ∀ i q c d,Good i q c d → response i q c=(observe i q c d).1)
    (p : Sample I (S × D) C) (n : ℕ) (hgood : BlindRun A observe Good p n) :
    run A response p.1 p.2.2 p.2.1.1 n=(virtualRun A observe p.1 p.2.2 p.2.1 n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : BlindRun A observe Good p n := fun t ht => hgood t (by omega)
    rw [run,virtualRun,ih hp]
    let s := virtualRun A observe p.1 p.2.2 p.2.1 n
    change step A response p.1 (p.2.2 n) s.1=(virtualStep A observe p.1 (p.2.2 n) s).1
    by_cases hh : A.halt s.1=true
    · simp [step,virtualStep,hh]
    · have hf : A.halt s.1=false := Bool.eq_false_of_not_eq_true hh
      have hg := hgood n (by omega) hf
      have he : response p.1 (A.query s.1) (p.2.2 n)=
          (observe p.1 (A.query s.1) (p.2.2 n) s.2).1 := hlocal _ _ _ _ hg
      simp only [step,virtualStep,hf,Bool.false_eq_true,if_false,he]

def virtualOutput (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (n : ℕ) (p : Sample I (S × D) C) : Y :=
  A.output (virtualRun A observe p.1 p.2.2 p.2.1 n).1

theorem virtualOutput_measurable (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (ho : Measurable (fun p : I × (Q × (C × D)) => observe p.1 p.2.1 p.2.2.1 p.2.2.2)) (n : ℕ) :
    Measurable (virtualOutput A observe n) :=
  A.output_measurable.comp (measurable_fst.comp (virtualRun_measurable A observe ho n))

omit [MeasurableSpace I] [MeasurableSpace C] [MeasurableSpace D] in
theorem cappedOutput_eq_virtual (A : Program S Q O Y)
    (response : I → Q → C → O) (observe : I → Q → C → D → O × D)
    (Good : I → Q → C → D → Prop)
    (hlocal : ∀ i q c d,Good i q c d → response i q c=(observe i q c d).1)
    (p : Sample I (S × D) C) (n : ℕ) (hgood : BlindRun A observe Good p n) :
    cappedOutput A response n (p.1,(p.2.1.1,p.2.2))=virtualOutput A observe n p :=
  congrArg A.output (run_eq_virtual_of_blind A response observe Good hlocal p n hgood)

end Bilevel.BorelAdaptive
