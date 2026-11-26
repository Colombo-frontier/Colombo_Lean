import Bilevel.TransportControllerMachineCompose

/-! Replaying the identical data path through the inverse current edge.
The paired store is swapped throughout and every physical orientation is
reversed. Invisible checks are erased to zero checks; this construction is
for history reconstruction, not an assertion of independence or equality
between forward and inverse angle events. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportGeneratorStore TransportEdgePosterior TransportRound
set_option maxHeartbeats 800000

def swapState {H : Memory.{u}} {D m : ℕ} (s : State H D m) : State H D m := (s.1,s.2.swap)

theorem swapState_measurable (H : Memory.{u}) (D m : ℕ) : Measurable (swapState (H := H) (D := D) (m := m)) :=
  measurable_fst.prodMk ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))

theorem swapState_swap {H : Memory.{u}} {D m : ℕ} (s : State H D m) : swapState (swapState s)=s := rfl

def inverseReplay {D d k : ℕ} {B : Memory.{u}} :
    {H : Memory.{u}} → {m h : ℕ} → Machine D d B k H m h → Machine D d B k H m h
  | H,_,_,.halt finish hf => .halt (fun s => finish (swapState s)) (hf.comp (swapState_measurable H D k))
  | _,_,_,.check _ _ _ _ next => .check (fun _ _ => 0) (fun _ _ => 0) measurable_const measurable_const (inverseReplay next)
  | H,m,_,.forward q hq respond hr next => .reverse (fun s => q (swapState s))
      (hq.comp (swapState_measurable H D m))
      (fun p => respond (swapState p.1,p.2))
      (hr.comp (((swapState_measurable H D m).comp measurable_fst).prodMk measurable_snd)) (inverseReplay next)
  | H,m,_,.reverse q hq respond hr next => .forward (fun s => q (swapState s))
      (hq.comp (swapState_measurable H D m))
      (fun p => respond (swapState p.1,p.2))
      (hr.comp (((swapState_measurable H D m).comp measurable_fst).prodMk measurable_snd)) (inverseReplay next)
  | H,m,_,.adapt update hu next => .adapt (fun s => update (swapState s))
      (hu.comp (swapState_measurable H D m)) (inverseReplay next)

theorem value_inverseReplay {D d k m h : ℕ} {H B : Memory.{u}} (P : Machine D d B k H m h)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    value (inverseReplay P) s O=swapState (value P (swapState s) O⁻¹) := by
  induction P with
  | halt finish hf => rfl
  | check W v hW hv next ih => exact ih s
  | forward q hq respond hr next ih =>
    simp only [inverseReplay,value]
    rw [ih]
    rfl
  | reverse q hq respond hr next ih =>
    simp only [inverseReplay,value,inv_inv]
    rw [ih]
    rfl
  | adapt update hu next ih =>
    simp only [inverseReplay,value]
    rw [ih]
    rfl

theorem value_inverseReplay_actual {D d k m h : ℕ} {H B : Memory.{u}} (P : Machine D d B k H m h)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    value (inverseReplay P) (swapState s) O⁻¹=swapState (value P s O) := by
  rw [value_inverseReplay,swapState_swap,inv_inv]

theorem span_zero (D b : ℕ) : span (fun _ : Fin b => (0 : Space D))=⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact Submodule.zero_mem _

theorem inverseReplay_no_failure {D d k m h : ℕ} {H B : Memory.{u}} (P : Machine D d B k H m h)
    (s : State H D m) (O : OrthogonalHaar.Group D) : ¬failure (inverseReplay P) s O := by
  induction P with
  | halt finish hf => exact not_false
  | check W v hW hv next ih =>
    change ¬(TransportControllerEdge.angleBad (span (fun _ : Fin d => (0 : Space D)))
      (span (TransportControllerPairedStore.fresh s.2 (fun _ : Fin d => (0 : Space D)))) O ∨ _)
    apply not_or.mpr
    refine ⟨?_,ih s⟩
    rw [TransportControllerPairedStore.fresh_span,span_zero]
    simp only [residualSpace,Submodule.map_bot]
    rintro ⟨x,hx⟩
    have hx0 : (x : Space D)=0 := x.property
    change ‖(x : Space D)‖/8 < ‖ProjectionGeometry.project ⊥ (O • (x : Space D))‖ at hx
    simp [hx0,ProjectionGeometry.project] at hx
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | adapt update hu next ih => exact ih _

end Bilevel.TransportControllerMachine
