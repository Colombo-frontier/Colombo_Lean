import NCConcave16991.ConditionalHaarConeCounter
import NCConcave16991.OracleSimulation
import NCConcave16991.ConeProblem

/-!
# Typed state and row requests for the explicit cone reference machine

Each paid policy query uses n+2 internal phases: prepare the policy action,
read its frontier row and form the reply, then optionally release n rows of
the completed stage. The reply phase uses the stored pre-query frontier.
-/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

abbrev Domain := ConeProblem.dualDomain E M R hR
abbrev Query := OracleQuery n (ConeProblem.primalDimension E M) (Domain E M R hR)
abbrev Control := OracleSimulation.State (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M)
abbrev Action := OraclePolicy.Action (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M)
abbrev RowIndex := Fin (M + 1) × Fin n
abbrev Request := Unit ⊕ RowIndex n M

structure State where
  control : Control E n M R hR
  progress : ConeCounter.State n
  rows : Fin (M + 1) → Fin n → E
  means : Fin (M + 1) → E
  phase : Fin (n + 2)
  pending : Action E n M R hR
  pendingStage : ℕ
  release : Bool

abbrev Data := Control E n M R hR × ConeCounter.State n ×
  (Fin (M + 1) → Fin n → E) × (Fin (M + 1) → E) × Fin (n + 2) ×
  Action E n M R hR × ℕ × Bool

def encode (s : State E n M R hR) : Data E n M R hR :=
  (s.control, s.progress, s.rows, s.means, s.phase, s.pending, s.pendingStage, s.release)

def decode (p : Data E n M R hR) : State E n M R hR where
  control := p.1
  progress := p.2.1
  rows := p.2.2.1
  means := p.2.2.2.1
  phase := p.2.2.2.2.1
  pending := p.2.2.2.2.2.1
  pendingStage := p.2.2.2.2.2.2.1
  release := p.2.2.2.2.2.2.2

def stateEquiv : State E n M R hR ≃ Data E n M R hR where
  toFun := encode E n M R hR
  invFun := decode E n M R hR
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨a,b,c,d,e,f,g,h⟩; rfl

instance stateMeasurableSpace [MeasurableSpace E] : MeasurableSpace (State E n M R hR) :=
  (inferInstance : MeasurableSpace (Data E n M R hR)).comap (encode E n M R hR)

def stateMeasurableEquiv [MeasurableSpace E] : State E n M R hR ≃ᵐ Data E n M R hR where
  toEquiv := stateEquiv E n M R hR
  measurable_toFun := measurable_iff_comap_le.mpr le_rfl
  measurable_invFun := by
    apply measurable_comap_iff.mpr
    change Measurable (encode E n M R hR ∘ decode E n M R hR)
    have he : encode E n M R hR ∘ decode E n M R hR = id :=
      funext (stateEquiv E n M R hR).right_inv
    rw [he]
    exact measurable_id

def initial : State E n M R hR where
  control := Sum.inr (OraclePolicy.emptyHistory (Domain E M R hR))
  progress := ConeCounter.initial n
  rows := fun _ _ ↦ 0
  means := fun _ ↦ 0
  phase := 0
  pending := Sum.inl 0
  pendingStage := 0
  release := false

def nextPhase (s : State E n M R hR) : Fin (n + 2) := s.phase + 1

def pendingIndex (s : State E n M R hR) : Option (Fin n) :=
  s.pending.elim (fun _ ↦ none) (fun q ↦ some q.1)

abbrev RequestSummary (n : ℕ) := Fin (n + 2) × Bool × ℕ × Option (Fin n)

def requestOfSummary (hn : 0 < n) (p : RequestSummary n) : Request n M :=
  if p.1.val = 0 then Sum.inl () else
  if p.1.val = 1 then
    p.2.2.2.elim (Sum.inl ()) (fun i ↦
      if p.2.2.1 < M + 1 then
        Sum.inr (⟨p.2.2.1 % (M + 1), Nat.mod_lt _ (by omega)⟩, i)
      else Sum.inl ())
  else if p.2.1 then
    if p.2.2.1 < M + 1 then
      Sum.inr (⟨p.2.2.1 % (M + 1), Nat.mod_lt _ (by omega)⟩,
        ⟨(p.1.val - 2) % n, Nat.mod_lt _ hn⟩)
    else Sum.inl ()
  else Sum.inl ()

def request (hn : 0 < n) (s : State E n M R hR) : Request n M :=
  requestOfSummary n M hn (s.phase, s.release, s.pendingStage, pendingIndex E n M R hR s)

section Measurable

variable [MeasurableSpace E]

theorem encode_measurable : Measurable (encode E n M R hR) :=
  (stateMeasurableEquiv E n M R hR).measurable

theorem control_measurable : Measurable (State.control : State E n M R hR → _) :=
  measurable_fst.comp (encode_measurable E n M R hR)

theorem progress_measurable : Measurable (State.progress : State E n M R hR → _) :=
  measurable_fst.comp (measurable_snd.comp (encode_measurable E n M R hR))

theorem rows_measurable : Measurable (State.rows : State E n M R hR → _) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (encode_measurable E n M R hR)))

theorem means_measurable : Measurable (State.means : State E n M R hR → _) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (encode_measurable E n M R hR))))

theorem phase_measurable : Measurable (State.phase : State E n M R hR → _) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (encode_measurable E n M R hR)))))

theorem pending_measurable : Measurable (State.pending : State E n M R hR → _) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (encode_measurable E n M R hR))))))

theorem pendingStage_measurable : Measurable (State.pendingStage : State E n M R hR → _) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (encode_measurable E n M R hR)))))))

theorem release_measurable : Measurable (State.release : State E n M R hR → _) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (encode_measurable E n M R hR)))))))

theorem measurable_mk {X : Type*} [MeasurableSpace X]
    {control : X → Control E n M R hR} {progress : X → ConeCounter.State n}
    {rows : X → Fin (M + 1) → Fin n → E} {means : X → Fin (M + 1) → E}
    {phase : X → Fin (n + 2)} {pending : X → Action E n M R hR}
    {pendingStage : X → ℕ} {release : X → Bool}
    (hc : Measurable control) (hp : Measurable progress) (hr : Measurable rows) (hm : Measurable means)
    (hph : Measurable phase) (ha : Measurable pending) (hs : Measurable pendingStage) (hb : Measurable release) :
    Measurable (fun x ↦ (⟨control x, progress x, rows x, means x, phase x, pending x,
      pendingStage x, release x⟩ : State E n M R hR)) :=
  (stateMeasurableEquiv E n M R hR).symm.measurable.comp
    (hc.prodMk (hp.prodMk (hr.prodMk (hm.prodMk (hph.prodMk (ha.prodMk (hs.prodMk hb)))))))

theorem nextPhase_measurable : Measurable (nextPhase E n M R hR) :=
  (measurable_of_countable (fun p : Fin (n + 2) ↦ p + 1)).comp (phase_measurable E n M R hR)

theorem pendingIndex_measurable : Measurable (pendingIndex E n M R hR) := by
  have hmap : Measurable (fun a : Action E n M R hR ↦
      a.elim (fun _ ↦ none) (fun q ↦ some q.1)) :=
    measurable_const.sumElim ((measurable_of_countable (fun i : Fin n ↦ some i)).comp measurable_fst)
  exact hmap.comp (pending_measurable E n M R hR)

theorem request_measurable (hn : 0 < n) : Measurable (request E n M R hR hn) :=
  (measurable_of_countable (requestOfSummary n M hn)).comp
    ((phase_measurable E n M R hR).prodMk ((release_measurable E n M R hR).prodMk
      ((pendingStage_measurable E n M R hR).prodMk (pendingIndex_measurable E n M R hR))))

end Measurable

end

end NCConcave16991.Haar.ConeMachine
