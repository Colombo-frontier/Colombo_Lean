import Bilevel.TransportControllerMachine

/-! Sequential composition preserves the actual final paired store. Pure
memory adaptation has no probe and introduces no artificial failure event. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportEdgePosterior
set_option maxHeartbeats 600000

def compose {D d k l b : ℕ} {B C : Memory.{u}} :
    {H : Memory.{u}} → {m a : ℕ} → Machine D d B k H m a → Machine D d C l B k b → Machine D d C l H m (b+a)
  | _,_,_,.halt finish hf,Q => .adapt finish hf Q
  | _,_,_,.check W v hW hv next,Q => .check W v hW hv (compose next Q)
  | _,_,_,.forward q hq respond hr next,Q => .forward q hq respond hr (compose next Q)
  | _,_,_,.reverse q hq respond hr next,Q => .reverse q hq respond hr (compose next Q)
  | _,_,_,.adapt update hu next,Q => .adapt update hu (compose next Q)

theorem value_compose {D d k l m a b : ℕ} {H B C : Memory.{u}}
    (P : Machine D d B k H m a) (Q : Machine D d C l B k b)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    value (compose P Q) s O=value Q (value P s O) O := by
  induction P with
  | halt finish hf => rfl
  | check W v hW hv next ih => exact ih s
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | adapt update hu next ih => exact ih _

theorem failure_compose {D d k l m a b : ℕ} {H B C : Memory.{u}}
    (P : Machine D d B k H m a) (Q : Machine D d C l B k b)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    failure (compose P Q) s O ↔ failure P s O ∨ failure Q (value P s O) O := by
  induction P with
  | halt finish hf => simp only [compose,failure,value,false_or]
  | check W v hW hv next ih =>
    change _ ∨ failure (compose next Q) s O ↔ (_ ∨ failure next s O) ∨ _
    rw [ih s,or_assoc]
    rfl
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | adapt update hu next ih => exact ih _

def pure {D d m : ℕ} {H B : Memory.{u}} (f : H → B) (hf : Measurable f) : Machine D d B m H m 0 :=
  .halt (fun s => f s.1) (hf.comp measurable_fst)

theorem value_pure {D d m : ℕ} {H B : Memory.{u}} (f : H → B) (hf : Measurable f)
    (s : State H D m) (O : OrthogonalHaar.Group D) : value (pure (D := D) (d := d) f hf) s O=(f s.1,s.2) := rfl

def map {D d k : ℕ} {B C : Memory.{u}} :
    {H : Memory.{u}} → {m a : ℕ} → Machine D d B k H m a →
    (f : B → C) → Measurable f → Machine D d C k H m a
  | _,_,_,.halt finish hg,f,hf => .halt (fun s => f (finish s)) (hf.comp hg)
  | _,_,_,.check W v hW hv next,f,hf => .check W v hW hv (map next f hf)
  | _,_,_,.forward q hq respond hr next,f,hf => .forward q hq respond hr (map next f hf)
  | _,_,_,.reverse q hq respond hr next,f,hf => .reverse q hq respond hr (map next f hf)
  | _,_,_,.adapt update hu next,f,hf => .adapt update hu (map next f hf)

theorem value_map {D d k m a : ℕ} {H B C : Memory.{u}}
    (P : Machine D d B k H m a) (f : B → C) (hf : Measurable f)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    value (map P f hf) s O=(f (value P s O).1,(value P s O).2) := by
  induction P with
  | halt finish hg => rfl
  | check W v hW hv next ih => exact ih s
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | adapt update hu next ih => exact ih _

theorem failure_map {D d k m a : ℕ} {H B C : Memory.{u}}
    (P : Machine D d B k H m a) (f : B → C) (hf : Measurable f)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    failure (map P f hf) s O ↔ failure P s O := by
  induction P with
  | halt finish hg => rfl
  | check W v hW hv next ih => exact or_congr_right (ih s)
  | forward q hq respond hr next ih => exact ih _
  | reverse q hq respond hr next ih => exact ih _
  | adapt update hu next ih => exact ih _

end Bilevel.TransportControllerMachine
