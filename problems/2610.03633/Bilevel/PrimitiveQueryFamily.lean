import Bilevel.PrimitiveQueryModel
import Bilevel.BorelAdaptiveReplyCongruence

/-! Packaging a constructed hard family does not change its original reply,
loss, private seed, stopping rule, or expected cost. Geometry and sample law
are fixed for the whole family before choosing an algorithm. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry BorelAdaptive
set_option autoImplicit false

structure Family (G : Geometry) (Index Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (μ L ρ Δ R₀ σf σg : ℝ) where
  primitive : Index → Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ
  response : ∀ i,(primitive i).Response
  gap : ∀ i,Nonempty ((primitive i).GapCertificate (response i) 0 Δ)
  initialization : ∀ i,‖(response i).y 0‖≤R₀
  upper : Index → FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) ν σf
  lower : Index → FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) ν σg
  upper_truth : ∀ i q,(upper i).truth q=pack ((primitive i).fx q.fst q.snd) ((primitive i).fy q.fst q.snd)
  lower_truth : ∀ i q,(lower i).truth q=pack ((primitive i).gx q.fst q.snd) ((primitive i).gy q.fst q.snd)

variable {G : Geometry} {Index Seed : Type} [MeasurableSpace Seed]
  {ν : Measure Seed} [IsProbabilityMeasure ν] {μ L ρ Δ R₀ σf σg : ℝ}
  (F : Family G Index Seed ν μ L ρ Δ R₀ σf σg)

def Family.instance (i : Index) : Instance G μ L ρ Δ R₀ σf σg where
  primitive := F.primitive i
  response := F.response i
  gap := Classical.choice (F.gap i)
  initialization := F.initialization i
  Seed := Seed
  law := ν
  upper := F.upper i
  lower := F.lower i
  upper_truth := F.upper_truth i
  lower_truth := F.lower_truth i

def Family.reply (i : Index) (q : G.Query) (c : Seed) : G.Reply :=
  ((F.upper i).sample q c,(F.lower i).sample q c)

def Family.loss (i : Index) (x : G.X) : ℝ :=
  ‖gradient ((F.primitive i).hyperobjective (F.response i)) x‖

def Family.RateProperty (ε rate : ℝ) : Prop :=
  ∀ A : Algorithm G,
    (∀ i, (∫⁻ z,ENNReal.ofReal (F.loss i (seededStopped A.program F.reply A.start (i,z)).2)
      ∂A.privateLaw.prod (IndependentStream.law ν))≤ENNReal.ofReal ε) →
    ∃ i,ENNReal.ofReal rate≤∫⁻ z,seededCalls A.program F.reply A.start (i,z)
      ∂A.privateLaw.prod (IndependentStream.law ν)

theorem Family.cost_eq (A : Algorithm G) (i : Index) :
    (F.instance i).cost A=∫⁻ z,seededCalls A.program F.reply A.start (i,z)
      ∂A.privateLaw.prod (IndependentStream.law ν) := by
  apply lintegral_congr
  intro z
  exact seededCalls_reply_congr A.program (F.instance i).reply F.reply () i (fun _ _ => rfl) A.start z

theorem Family.risk_eq (A : Algorithm G) (i : Index) :
    (F.instance i).risk A=(∫⁻ z,ENNReal.ofReal (F.loss i (seededStopped A.program F.reply A.start (i,z)).2)
      ∂A.privateLaw.prod (IndependentStream.law ν)) := by
  apply lintegral_congr
  intro z
  change ENNReal.ofReal (F.loss i (seededStopped A.program (F.instance i).reply A.start ((),z)).2)=_
  rw [seededStopped_reply_congr A.program (F.instance i).reply F.reply () i (fun _ _ => rfl)]

def Hardness (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε rate : ℝ) : Prop :=
  ∀ A : Solver,Accurate C ε A →
    ∃ (G : Geometry) (I : Instance G μ L ρ Δ R₀ σf σg),C G I ∧ ENNReal.ofReal rate≤I.cost (A G)

theorem Family.hardness (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε rate : ℝ)
    (hC : ∀ i,C G (F.instance i)) (hRate : F.RateProperty ε rate) : Hardness C ε rate := by
  intro A hA
  obtain ⟨i,hi⟩ := hRate (A G) (fun i => by
    rw [← F.risk_eq (A G) i]
    exact hA G (F.instance i) (hC i))
  exact ⟨G,F.instance i,hC i,(F.cost_eq (A G) i).symm ▸ hi⟩

theorem Hardness.minimax {C : InstanceClass μ L ρ Δ R₀ σf σg} {ε rate : ℝ}
    (h : Hardness C ε rate) : ENNReal.ofReal rate≤Complexity C ε :=
  lower_of_hard_instance C ε (ENNReal.ofReal rate) h

theorem Hardness.mono {C : InstanceClass μ L ρ Δ R₀ σf σg} {ε rate rate' : ℝ}
    (h : Hardness C ε rate) (hr : rate'≤rate) : Hardness C ε rate' := by
  intro A hA
  obtain ⟨G,I,hI,hi⟩ := h A hA
  exact ⟨G,I,hI,(ENNReal.ofReal_le_ofReal hr).trans hi⟩

theorem Hardness.enlarge_class {C C' : InstanceClass μ L ρ Δ R₀ σf σg} {ε rate : ℝ}
    (h : Hardness C ε rate) (hCC' : ∀ G I,C G I → C' G I) : Hardness C' ε rate := by
  intro A hA
  obtain ⟨G,I,hI,hi⟩ := h A (fun G I hI => hA G I (hCC' G I hI))
  exact ⟨G,I,hCC' G I hI,hi⟩

end Bilevel.PrimitiveQuery
