import Bilevel.TransportControllerPairedStore

/-! Borel edge policies with invisible fresh-angle monitors. The actual
paired transcript is extended after every forward or reverse response.
Monitor regularity and perpendicular-domain legality are proved from the
finite generator implementation, not supplied as probability hypotheses. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.TransportControllerEdgePolicy
open EuclideanGaussian OrthogonalAction TransportGeneratorStore TransportEdgePosterior
open TransportControllerEdge

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

abbrev State (H : Type*) (D m : ℕ) := H × TransportControllerPairedStore.State D m

def afterForward {H : Type*} {D m : ℕ} (q : State H D m → Space D)
    (respond : State H D m × Space D → H) (s : State H D m) (y : Space D) : State H D (m+1) :=
  (respond (s,y),TransportControllerPairedStore.insert s.2 (q s) y)

def afterReverse {H : Type*} {D m : ℕ} (q : State H D m → Space D)
    (respond : State H D m × Space D → H) (s : State H D m) (x : Space D) : State H D (m+1) :=
  (respond (s,x),TransportControllerPairedStore.insert s.2 x (q s))

theorem afterForward_measurable {H : Type*} [MeasurableSpace H] {D m : ℕ}
    (q : State H D m → Space D) (hq : Measurable q)
    (respond : State H D m × Space D → H) (hr : Measurable respond) :
    Measurable (fun p : State H D m × Space D => afterForward q respond p.1 p.2) :=
  hr.prodMk ((TransportControllerPairedStore.insert_measurable D m).comp
    ((measurable_snd.comp measurable_fst).prodMk ((hq.comp measurable_fst).prodMk measurable_snd)))

theorem afterReverse_measurable {H : Type*} [MeasurableSpace H] {D m : ℕ}
    (q : State H D m → Space D) (hq : Measurable q)
    (respond : State H D m × Space D → H) (hr : Measurable respond) :
    Measurable (fun p : State H D m × Space D => afterReverse q respond p.1 p.2) :=
  hr.prodMk ((TransportControllerPairedStore.insert_measurable D m).comp
    ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk (hq.comp measurable_fst))))

inductive Spec (H : Type*) [MeasurableSpace H] (D d : ℕ) : ℕ → ℕ → Type _
  | halt {m : ℕ} : Spec H D d m 0
  | check {m h : ℕ} (W v : State H D m → Fin d → Space D) (hW : Measurable W) (hv : Measurable v)
      (next : Spec H D d m h) : Spec H D d m (h+1)
  | forward {m h : ℕ} (q : State H D m → Space D) (hq : Measurable q)
      (respond : State H D m × Space D → H) (hr : Measurable respond)
      (next : Spec H D d (m+1) h) : Spec H D d m (h+1)
  | reverse {m h : ℕ} (q : State H D m → Space D) (hq : Measurable q)
      (respond : State H D m × Space D → H) (hr : Measurable respond)
      (next : Spec H D d (m+1) h) : Spec H D d m (h+1)
  | skip {m h : ℕ} (update : State H D m → H) (hu : Measurable update)
      (next : Spec H D d m h) : Spec H D d m (h+1)

def compile {H : Type*} [MeasurableSpace H] {D d : ℕ} :
    {m h : ℕ} → Spec H D d m h → State H D m → Program D H h
  | _,_,.halt,s => .halt s.1
  | _,_,.check W v _ _ next,s => .check (span (W s)) (span (TransportControllerPairedStore.fresh s.2 (v s))) (compile next s)
  | _,_,.forward q _ respond _ next,s => .forward (q s)
      (fun y => compile next (afterForward q respond s y))
  | _,_,.reverse q _ respond _ next,s => .reverse (q s)
      (fun x => compile next (afterReverse q respond s x))
  | _,_,.skip update _ next,s => .check ⊥ ⊥ (compile next (update s,s.2))

def failure {H : Type*} [MeasurableSpace H] {D d : ℕ} :
    {m h : ℕ} → Spec H D d m h → State H D m → OrthogonalHaar.Group D → Prop
  | _,_,.halt,_,_ => False
  | _,_,.check W v _ _ next,s,O => angleBad (span (W s)) (span (TransportControllerPairedStore.fresh s.2 (v s))) O ∨ failure next s O
  | _,_,.forward q _ respond _ next,s,O => failure next (afterForward q respond s (O • q s)) O
  | _,_,.reverse q _ respond _ next,s,O => failure next (afterReverse q respond s (O⁻¹ • q s)) O
  | _,_,.skip update _ next,s,O => failure next (update s,s.2) O

def value {H : Type*} [MeasurableSpace H] {D d : ℕ} :
    {m h : ℕ} → Spec H D d m h → State H D m → OrthogonalHaar.Group D → H
  | _,_,.halt,s,_ => s.1
  | _,_,.check _ _ _ _ next,s,O => value next s O
  | _,_,.forward q _ respond _ next,s,O => value next (afterForward q respond s (O • q s)) O
  | _,_,.reverse q _ respond _ next,s,O => value next (afterReverse q respond s (O⁻¹ • q s)) O
  | _,_,.skip update _ next,s,O => value next (update s,s.2) O

theorem compile_value {H : Type*} [MeasurableSpace H] {D d m h : ℕ}
    (P : Spec H D d m h) (s : State H D m) (O : OrthogonalHaar.Group D) :
    TransportNetwork.EdgeProgram.eval (erase (compile P s)) O=value P s O := by
  induction P with
  | halt => rfl
  | check W v hW hv next ih => exact ih s
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | skip update hu next ih => exact ih _

theorem compile_failure {H : Type*} [MeasurableSpace H] {D d m h : ℕ}
    (P : Spec H D d m h) (s : State H D m) (O : OrthogonalHaar.Group D) :
    bad (compile P s) O ↔ failure P s O := by
  induction P with
  | halt => rfl
  | check W v hW hv next ih => exact or_congr_right (ih s)
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | skip update hu next ih =>
    change angleBad ⊥ ⊥ O ∨ _ ↔ _
    have hn : ¬ angleBad (⊥ : Submodule ℝ (Space D)) ⊥ O := by
      rintro ⟨u,hu⟩
      have hu0 : (u : Space D)=0 := u.property
      change ‖(u : Space D)‖/8 < ‖ProjectionGeometry.project ⊥ (O • (u : Space D))‖ at hu
      simp [hu0,ProjectionGeometry.project] at hu
    simpa only [hn,false_or] using (ih (update s,s.2))

theorem failure_measurable {H : Type*} [MeasurableSpace H] {D d m h : ℕ}
    (P : Spec H D d m h) :
    MeasurableSet {p : State H D m × OrthogonalHaar.Group D | failure P p.1 p.2} := by
  induction P with
  | halt => exact MeasurableSet.empty
  | check W v hW hv next ih =>
    exact (TransportControllerPairedStore.fresh_angle_measurable _ (measurable_snd.comp measurable_fst)
      _ (hv.comp measurable_fst) _ (hW.comp measurable_fst) _ measurable_snd).union ih
  | forward q hq respond hr next ih =>
    have ha : Measurable (fun p : State H D _ × OrthogonalHaar.Group D => p.2 • q p.1) :=
      measurable_snd.smul (hq.comp measurable_fst)
    exact (((afterForward_measurable q hq respond hr).comp (measurable_fst.prodMk ha)).prodMk measurable_snd) ih
  | reverse q hq respond hr next ih =>
    have ha : Measurable (fun p : State H D _ × OrthogonalHaar.Group D => p.2⁻¹ • q p.1) :=
      measurable_snd.inv.smul (hq.comp measurable_fst)
    exact (((afterReverse_measurable q hq respond hr).comp (measurable_fst.prodMk ha)).prodMk measurable_snd) ih
  | skip update hu next ih =>
    exact (((hu.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd) ih

theorem compile_regular {H : Type*} [MeasurableSpace H] {D d m h : ℕ}
    (P : Spec H D d m h) (s : State H D m) : Regular (compile P s) := by
  induction P with
  | halt => trivial
  | check W v hW hv next ih => exact ih s
  | forward q hq respond hr next ih =>
    refine ⟨?_,fun y => ih (afterForward q respond s y)⟩
    have hm : Measurable (fun p : Space D × OrthogonalHaar.Group D =>
        (afterForward q respond s p.1,p.2)) :=
      (((afterForward_measurable q hq respond hr).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have hh := hm (failure_measurable next)
    simpa only [Set.mem_preimage,Set.mem_setOf_eq,← compile_failure] using hh
  | reverse q hq respond hr next ih =>
    refine ⟨?_,fun y => ih (afterReverse q respond s y)⟩
    have hm : Measurable (fun p : Space D × OrthogonalHaar.Group D =>
        (afterReverse q respond s p.1,p.2)) :=
      (((afterReverse_measurable q hq respond hr).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have hh := hm (failure_measurable next)
    simpa only [Set.mem_preimage,Set.mem_setOf_eq,← compile_failure] using hh
  | skip update hu next ih => exact ih _

theorem compile_valid {H : Type*} [MeasurableSpace H] {D d m h : ℕ}
    (P : Spec H D d m h) (s : State H D m) : Valid d (compile P s) (TransportControllerPairedStore.pairs s.2) := by
  induction P with
  | halt => trivial
  | check W v hW hv next ih =>
    exact ⟨TransportControllerPairedStore.fresh_perp _ _,span_rank_le _,span_rank_le _,ih s⟩
  | forward q hq respond hr next ih =>
    intro y
    have hh := ih (afterForward q respond s y)
    simpa only [afterForward,TransportControllerPairedStore.pairs_insert] using hh
  | reverse q hq respond hr next ih =>
    intro x
    have hh := ih (afterReverse q respond s x)
    simpa only [afterReverse,TransportControllerPairedStore.pairs_insert] using hh
  | skip update hu next ih =>
    exact ⟨bot_le,by simp,by simp,ih _⟩

theorem policy_angle_failure {H : Type*} [MeasurableSpace H] {D d m h : ℕ}
    (P : Spec H D d m h) (s : State H D m) (r : ℕ) (hr : 0<r) (hD : m+h+r≤D)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range (TransportControllerPairedStore.pairs s.2)) μ) (hL : ∀ᵐ O ∂μ, Supports (TransportControllerPairedStore.pairs s.2) O) :
    μ {O | failure P s O} ≤ (h:ℝ≥0∞)*budget d r := by
  have hd : Module.finrank ℝ (range (TransportControllerPairedStore.pairs s.2))+h+r≤D := by
    rw [TransportControllerPairedStore.range_pairs]
    have hh := span_rank_le s.2.2
    omega
  have hh := finite_angle_failure (compile P s) d r hr (TransportControllerPairedStore.pairs s.2) hd μ hμ hL
    (compile_regular P s) (compile_valid P s)
  simpa only [compile_failure] using hh

end Bilevel.TransportControllerEdgePolicy
