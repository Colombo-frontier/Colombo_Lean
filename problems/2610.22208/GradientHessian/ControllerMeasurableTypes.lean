import GradientHessian.ComparisonControllerPhases
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! Canonical measurable structures for finite counters and controller
records. Pending points retain their given measurable structure; no point
space is discretized. -/

noncomputable section
namespace GradientHessian.ControllerMeasurable
open Classical TaskState ComparisonController

def stateEquiv (L M ell : ℕ) : State L M ell ≃
    (FrontierState.Leaf L → Fin (M+1)) × (FrontierState.Leaf L → Fin (ell+1)) where
  toFun s := (s.completed,s.slots)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance stateFintype (L M ell : ℕ) : Fintype (State L M ell) :=
  Fintype.ofEquiv _ (stateEquiv L M ell).symm

instance stateMeasurable (L M ell : ℕ) : MeasurableSpace (State L M ell) := ⊤
instance stateSingleton (L M ell : ℕ) : MeasurableSingletonClass (State L M ell) := ⟨fun _ => trivial⟩

def kindEquiv : Kind ≃ Bool where
  toFun k := match k with | .ordinary => false | .rich => true
  invFun b := if b then .rich else .ordinary
  left_inv k := by cases k <;> rfl
  right_inv b := by cases b <;> rfl

instance kindFintype : Fintype Kind := Fintype.ofEquiv Bool kindEquiv.symm
instance kindMeasurable : MeasurableSpace Kind := ⊤
instance kindSingleton : MeasurableSingletonClass Kind := ⟨fun _ => trivial⟩

instance finiteOptionMeasurable (A : Type*) [Fintype A] : MeasurableSpace (Option A) := ⊤
instance finiteOptionSingleton (A : Type*) [Fintype A] : MeasurableSingletonClass (Option A) :=
  ⟨fun _ => trivial⟩

def transportEquiv {A B : Type*} [MeasurableSpace B] (e : A ≃ B) :
    @MeasurableEquiv A B (MeasurableSpace.comap e inferInstance) inferInstance := by
  letI : MeasurableSpace A := MeasurableSpace.comap e inferInstance
  exact { toEquiv := e
          measurable_toFun := comap_measurable e
          measurable_invFun := by
            rintro s ⟨u,hu,rfl⟩
            simpa using hu }

def pendingEquiv (X : Type*) : Pending X ≃ X × Kind where
  toFun p := (p.point,p.kind)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance pendingMeasurable (X : Type*) [MeasurableSpace X] : MeasurableSpace (Pending X) :=
  MeasurableSpace.comap (pendingEquiv X) inferInstance

def pendingMeasurableEquiv (X : Type*) [MeasurableSpace X] : Pending X ≃ᵐ X × Kind :=
  transportEquiv (pendingEquiv X)

theorem measurable_pending_point {X : Type*} [MeasurableSpace X] :
    Measurable (Pending.point : Pending X → X) := measurable_fst.comp (pendingMeasurableEquiv X).measurable

theorem measurable_pending_kind {X : Type*} [MeasurableSpace X] :
    Measurable (Pending.kind : Pending X → Kind) := measurable_snd.comp (pendingMeasurableEquiv X).measurable

theorem measurable_pending_mk {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {point : Ω → X} {kind : Ω → Kind} (hp : Measurable point) (hk : Measurable kind) :
    Measurable (fun w => Pending.mk (point w) (kind w)) :=
  (pendingMeasurableEquiv X).symm.measurable.comp (hp.prodMk hk)

instance traceMeasurable (L M ell : ℕ) (A : Type*) : MeasurableSpace (List (State L M ell × A)) := ⊤
instance traceSingleton (L M ell : ℕ) (A : Type*) :
    MeasurableSingletonClass (List (State L M ell × A)) := ⟨fun _ => trivial⟩

def receiptEquiv (L M ell : ℕ) (X A : Type*) : Receipt L M ell X A ≃
    Pending X × State L M ell × State L M ell × List (State L M ell × A) where
  toFun r := (r.pending,r.beforeNormal,r.afterNormal,r.repairs)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance receiptMeasurable (L M ell : ℕ) (X A : Type*) [MeasurableSpace X] :
    MeasurableSpace (Receipt L M ell X A) := MeasurableSpace.comap (receiptEquiv L M ell X A) inferInstance

def receiptMeasurableEquiv (L M ell : ℕ) (X A : Type*) [MeasurableSpace X] :
    Receipt L M ell X A ≃ᵐ Pending X × State L M ell × State L M ell × List (State L M ell × A) :=
  transportEquiv (receiptEquiv L M ell X A)

theorem measurable_receipt_pending {L M ell : ℕ} {X A : Type*} [MeasurableSpace X] :
    Measurable (Receipt.pending : Receipt L M ell X A → Pending X) :=
  measurable_fst.comp (receiptMeasurableEquiv L M ell X A).measurable

theorem measurable_receipt_beforeNormal {L M ell : ℕ} {X A : Type*} [MeasurableSpace X] :
    Measurable (Receipt.beforeNormal : Receipt L M ell X A → State L M ell) :=
  measurable_fst.comp (measurable_snd.comp (receiptMeasurableEquiv L M ell X A).measurable)

theorem measurable_receipt_afterNormal {L M ell : ℕ} {X A : Type*} [MeasurableSpace X] :
    Measurable (Receipt.afterNormal : Receipt L M ell X A → State L M ell) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp (receiptMeasurableEquiv L M ell X A).measurable))

theorem measurable_receipt_repairs {L M ell : ℕ} {X A : Type*} [MeasurableSpace X] :
    Measurable (Receipt.repairs : Receipt L M ell X A → List (State L M ell × A)) :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (receiptMeasurableEquiv L M ell X A).measurable))

abbrev PhaseData (L M ell : ℕ) := State L M ell ⊕ State L M ell ⊕ (State L M ell × State L M ell) ⊕ State L M ell

instance sumSingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    MeasurableSingletonClass (A ⊕ B) := by
  constructor
  intro s
  cases s with
  | inl a => simpa using (measurableSet_singleton a).inl_image (β := B)
  | inr b => simpa using (measurableSet_singleton b).inr_image (α := A)

def phaseEquiv (L M ell : ℕ) (X A : Type*) : Phase L M ell X A ≃ Pending X × PhaseData L M ell where
  toFun q := match q with
    | .repairing p s => (p,.inl s)
    | .normal p s => (p,.inr (.inl s))
    | .delivered p before after => (p,.inr (.inr (.inl (before,after))))
    | .frozen p s => (p,.inr (.inr (.inr s)))
  invFun q := match q.2 with
    | .inl s => .repairing q.1 s
    | .inr (.inl s) => .normal q.1 s
    | .inr (.inr (.inl (before,after))) => .delivered q.1 before after
    | .inr (.inr (.inr s)) => .frozen q.1 s
  left_inv q := by cases q <;> rfl
  right_inv q := by rcases q with ⟨p,s|s|s|s⟩ <;> rfl

instance phaseMeasurable (L M ell : ℕ) (X A : Type*) [MeasurableSpace X] :
    MeasurableSpace (Phase L M ell X A) := MeasurableSpace.comap (phaseEquiv L M ell X A) inferInstance

def phaseMeasurableEquiv (L M ell : ℕ) (X A : Type*) [MeasurableSpace X] :
    Phase L M ell X A ≃ᵐ Pending X × PhaseData L M ell := transportEquiv (phaseEquiv L M ell X A)

end GradientHessian.ControllerMeasurable
