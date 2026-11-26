import Bilevel.TransportControllerEdgePolicy

/-! Heterogeneous Borel edge machines. Memory types may change after an
action, while the physical paired transcript is carried without reset.
This permits a finite controller with growing generator arrays to compile
to the actual fixed-edge posterior theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportGeneratorStore TransportEdgePosterior
open TransportControllerEdge

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

structure Memory : Type (u+1) where
  carrier : Type u
  [measurableSpace : MeasurableSpace carrier]
attribute [instance] Memory.measurableSpace
instance : CoeSort Memory.{u} (Type u) := ⟨Memory.carrier⟩
abbrev Memory.of (H : Type u) [MeasurableSpace H] : Memory.{u} := ⟨H⟩
abbrev State (H : Memory.{u}) (D m : ℕ) := H × TransportControllerPairedStore.State D m

def forwardState {H K : Memory.{u}} {D m : ℕ} (q : State H D m → Space D)
    (respond : State H D m × Space D → K) (s : State H D m) (y : Space D) : State K D (m+1) :=
  (respond (s,y),TransportControllerPairedStore.insert s.2 (q s) y)

def reverseState {H K : Memory.{u}} {D m : ℕ} (q : State H D m → Space D)
    (respond : State H D m × Space D → K) (s : State H D m) (x : Space D) : State K D (m+1) :=
  (respond (s,x),TransportControllerPairedStore.insert s.2 x (q s))

theorem forwardState_measurable {H K : Memory.{u}} {D m : ℕ}
    (q : State H D m → Space D) (hq : Measurable q)
    (respond : State H D m × Space D → K) (hr : Measurable respond) :
    Measurable (fun p : State H D m × Space D => forwardState q respond p.1 p.2) :=
  hr.prodMk ((TransportControllerPairedStore.insert_measurable D m).comp
    ((measurable_snd.comp measurable_fst).prodMk ((hq.comp measurable_fst).prodMk measurable_snd)))

theorem reverseState_measurable {H K : Memory.{u}} {D m : ℕ}
    (q : State H D m → Space D) (hq : Measurable q)
    (respond : State H D m × Space D → K) (hr : Measurable respond) :
    Measurable (fun p : State H D m × Space D => reverseState q respond p.1 p.2) :=
  hr.prodMk ((TransportControllerPairedStore.insert_measurable D m).comp
    ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk (hq.comp measurable_fst))))

inductive Machine (D d : ℕ) (B : Memory.{u}) (k : ℕ) : Memory.{u} → ℕ → ℕ → Type (u+1)
  | halt {H : Memory.{u}} (finish : State H D k → B) (hf : Measurable finish) : Machine D d B k H k 0
  | check {H : Memory.{u}} {m h : ℕ} (W v : State H D m → Fin d → Space D)
      (hW : Measurable W) (hv : Measurable v) (next : Machine D d B k H m h) :
      Machine D d B k H m (h+1)
  | forward {H K : Memory.{u}} {m h : ℕ} (q : State H D m → Space D) (hq : Measurable q)
      (respond : State H D m × Space D → K) (hr : Measurable respond)
      (next : Machine D d B k K (m+1) h) : Machine D d B k H m (h+1)
  | reverse {H K : Memory.{u}} {m h : ℕ} (q : State H D m → Space D) (hq : Measurable q)
      (respond : State H D m × Space D → K) (hr : Measurable respond)
      (next : Machine D d B k K (m+1) h) : Machine D d B k H m (h+1)
  | adapt {H K : Memory.{u}} {m h : ℕ} (update : State H D m → K) (hu : Measurable update)
      (next : Machine D d B k K m h) : Machine D d B k H m h

def compile {D d k : ℕ} {B : Memory.{u}} :
    {H : Memory.{u}} → {m h : ℕ} → Machine D d B k H m h → State H D m → Program D (State B D k) h
  | _,_,_,.halt finish _,s => .halt (finish s,s.2)
  | _,_,_,.check W v _ _ next,s => .check (span (W s))
      (span (TransportControllerPairedStore.fresh s.2 (v s))) (compile next s)
  | _,_,_,.forward q _ respond _ next,s => .forward (q s) (fun y => compile next (forwardState q respond s y))
  | _,_,_,.reverse q _ respond _ next,s => .reverse (q s) (fun x => compile next (reverseState q respond s x))
  | _,_,_,.adapt update _ next,s => compile next (update s,s.2)

def failure {D d k : ℕ} {B : Memory.{u}} :
    {H : Memory.{u}} → {m h : ℕ} → Machine D d B k H m h → State H D m → OrthogonalHaar.Group D → Prop
  | _,_,_,.halt _ _,_,_ => False
  | _,_,_,.check W v _ _ next,s,O =>
      angleBad (span (W s)) (span (TransportControllerPairedStore.fresh s.2 (v s))) O ∨ failure next s O
  | _,_,_,.forward q _ respond _ next,s,O => failure next (forwardState q respond s (O • q s)) O
  | _,_,_,.reverse q _ respond _ next,s,O => failure next (reverseState q respond s (O⁻¹ • q s)) O
  | _,_,_,.adapt update _ next,s,O => failure next (update s,s.2) O

def value {D d k : ℕ} {B : Memory.{u}} :
    {H : Memory.{u}} → {m h : ℕ} → Machine D d B k H m h → State H D m → OrthogonalHaar.Group D → State B D k
  | _,_,_,.halt finish _,s,_ => (finish s,s.2)
  | _,_,_,.check _ _ _ _ next,s,O => value next s O
  | _,_,_,.forward q _ respond _ next,s,O => value next (forwardState q respond s (O • q s)) O
  | _,_,_,.reverse q _ respond _ next,s,O => value next (reverseState q respond s (O⁻¹ • q s)) O
  | _,_,_,.adapt update _ next,s,O => value next (update s,s.2) O

theorem compile_value {D d k m h : ℕ} {B H : Memory.{u}} (P : Machine D d B k H m h)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    TransportNetwork.EdgeProgram.eval (erase (compile P s)) O=value P s O := by
  induction P with
  | halt finish hf => rfl
  | check W v hW hv next ih => exact ih s
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | adapt update hu next ih => exact ih _

theorem compile_failure {D d k m h : ℕ} {B H : Memory.{u}} (P : Machine D d B k H m h)
    (s : State H D m) (O : OrthogonalHaar.Group D) : bad (compile P s) O ↔ failure P s O := by
  induction P with
  | halt finish hf => rfl
  | check W v hW hv next ih => exact or_congr_right (ih s)
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | adapt update hu next ih => exact ih _

theorem failure_measurable {D d k m h : ℕ} {B H : Memory.{u}} (P : Machine D d B k H m h) :
    MeasurableSet {p : State H D m × OrthogonalHaar.Group D | failure P p.1 p.2} := by
  induction P with
  | halt finish hf => exact MeasurableSet.empty
  | check W v hW hv next ih =>
    exact (TransportControllerPairedStore.fresh_angle_measurable _ (measurable_snd.comp measurable_fst)
      _ (hv.comp measurable_fst) _ (hW.comp measurable_fst) _ measurable_snd).union ih
  | forward q hq respond hr next ih =>
    have ha : Measurable (fun p : State _ D _ × OrthogonalHaar.Group D => p.2 • q p.1) :=
      measurable_snd.smul (hq.comp measurable_fst)
    exact (((forwardState_measurable q hq respond hr).comp (measurable_fst.prodMk ha)).prodMk measurable_snd) ih
  | reverse q hq respond hr next ih =>
    have ha : Measurable (fun p : State _ D _ × OrthogonalHaar.Group D => p.2⁻¹ • q p.1) :=
      measurable_snd.inv.smul (hq.comp measurable_fst)
    exact (((reverseState_measurable q hq respond hr).comp (measurable_fst.prodMk ha)).prodMk measurable_snd) ih
  | adapt update hu next ih =>
    exact (((hu.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd) ih

theorem value_measurable {D d k m h : ℕ} {B H : Memory.{u}} (P : Machine D d B k H m h) :
    Measurable (fun p : State H D m × OrthogonalHaar.Group D => value P p.1 p.2) := by
  induction P with
  | halt finish hf => exact (hf.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)
  | check W v hW hv next ih => exact ih
  | forward q hq respond hr next ih =>
    have ha : Measurable (fun p : State _ D _ × OrthogonalHaar.Group D => p.2 • q p.1) :=
      measurable_snd.smul (hq.comp measurable_fst)
    exact ih.comp (((forwardState_measurable q hq respond hr).comp (measurable_fst.prodMk ha)).prodMk measurable_snd)
  | reverse q hq respond hr next ih =>
    have ha : Measurable (fun p : State _ D _ × OrthogonalHaar.Group D => p.2⁻¹ • q p.1) :=
      measurable_snd.inv.smul (hq.comp measurable_fst)
    exact ih.comp (((reverseState_measurable q hq respond hr).comp (measurable_fst.prodMk ha)).prodMk measurable_snd)
  | adapt update hu next ih =>
    exact ih.comp (((hu.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd)

theorem compile_regular {D d k m h : ℕ} {B H : Memory.{u}} (P : Machine D d B k H m h)
    (s : State H D m) : Regular (compile P s) := by
  induction P with
  | halt finish hf => trivial
  | check W v hW hv next ih => exact ih s
  | forward q hq respond hr next ih =>
    refine ⟨?_,fun y => ih (forwardState q respond s y)⟩
    have hm : Measurable (fun p : Space D × OrthogonalHaar.Group D => (forwardState q respond s p.1,p.2)) :=
      (((forwardState_measurable q hq respond hr).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have hh := hm (failure_measurable next)
    simpa only [Set.mem_preimage,Set.mem_setOf_eq,← compile_failure] using hh
  | reverse q hq respond hr next ih =>
    refine ⟨?_,fun y => ih (reverseState q respond s y)⟩
    have hm : Measurable (fun p : Space D × OrthogonalHaar.Group D => (reverseState q respond s p.1,p.2)) :=
      (((reverseState_measurable q hq respond hr).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have hh := hm (failure_measurable next)
    simpa only [Set.mem_preimage,Set.mem_setOf_eq,← compile_failure] using hh
  | adapt update hu next ih => exact ih _

theorem compile_valid {D d k m h : ℕ} {B H : Memory.{u}} (P : Machine D d B k H m h)
    (s : State H D m) : Valid d (compile P s) (TransportControllerPairedStore.pairs s.2) := by
  induction P with
  | halt finish hf => trivial
  | check W v hW hv next ih =>
    exact ⟨TransportControllerPairedStore.fresh_perp _ _,span_rank_le _,span_rank_le _,ih s⟩
  | forward q hq respond hr next ih =>
    have hh := fun y => ih (forwardState q respond s y)
    simpa only [forwardState,TransportControllerPairedStore.pairs_insert] using hh
  | reverse q hq respond hr next ih =>
    have hh := fun y => ih (reverseState q respond s y)
    simpa only [reverseState,TransportControllerPairedStore.pairs_insert] using hh
  | adapt update hu next ih => exact ih _

theorem machine_angle_failure {D d k m h : ℕ} {B H : Memory.{u}} (P : Machine D d B k H m h)
    (s : State H D m) (r : ℕ) (hr : 0<r) (hD : m+h+r≤D)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range (TransportControllerPairedStore.pairs s.2)) μ)
    (hL : ∀ᵐ O ∂μ, Supports (TransportControllerPairedStore.pairs s.2) O) :
    μ {O | failure P s O} ≤ (h:ℝ≥0∞)*budget d r := by
  have hd : Module.finrank ℝ (range (TransportControllerPairedStore.pairs s.2))+h+r≤D := by
    rw [TransportControllerPairedStore.range_pairs]
    have hh := span_rank_le s.2.2
    omega
  have hh := finite_angle_failure (compile P s) d r hr (TransportControllerPairedStore.pairs s.2) hd μ hμ hL
    (compile_regular P s) (compile_valid P s)
  simpa only [compile_failure] using hh

end Bilevel.TransportControllerMachine
