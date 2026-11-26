import NCConcave16991.DenseSmoothMachineFresh
import NCConcave16991.DenseSmoothOracleMeasurable

/-! # Measurable public dense-machine state and cache replies -/

namespace NCConcave16991.DenseSmooth.Machine

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)

abbrev Data := Control E n T hn ρ hρ × Counter.State n × Rows E n T × Directions E T

def encode (s : State E n T hn ρ hρ) : Data E n T hn ρ hρ := (s.control, s.progress, s.rows, s.directions)

def decode (p : Data E n T hn ρ hρ) : State E n T hn ρ hρ := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

def stateEquiv : State E n T hn ρ hρ ≃ Data E n T hn ρ hρ where
  toFun := encode E n T hn ρ hρ
  invFun := decode E n T hn ρ hρ
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨a,b,c,d⟩; rfl

instance stateMeasurableSpace [MeasurableSpace E] : MeasurableSpace (State E n T hn ρ hρ) :=
  (inferInstance : MeasurableSpace (Data E n T hn ρ hρ)).comap (encode E n T hn ρ hρ)

def stateMeasurableEquiv [MeasurableSpace E] : State E n T hn ρ hρ ≃ᵐ Data E n T hn ρ hρ where
  toEquiv := stateEquiv E n T hn ρ hρ
  measurable_toFun := measurable_iff_comap_le.mpr le_rfl
  measurable_invFun := by
    apply measurable_comap_iff.mpr
    change Measurable (encode E n T hn ρ hρ ∘ decode E n T hn ρ hρ)
    rw [show encode E n T hn ρ hρ ∘ decode E n T hn ρ hρ = id from funext (stateEquiv E n T hn ρ hρ).right_inv]
    exact measurable_id

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem encode_measurable : Measurable (encode E n T hn ρ hρ) := (stateMeasurableEquiv E n T hn ρ hρ).measurable
theorem control_measurable : Measurable (State.control : State E n T hn ρ hρ → _) :=
  measurable_fst.comp (encode_measurable E n T hn ρ hρ)
theorem progress_measurable : Measurable (State.progress : State E n T hn ρ hρ → _) :=
  measurable_fst.comp (measurable_snd.comp (encode_measurable E n T hn ρ hρ))
theorem rows_measurable : Measurable (State.rows : State E n T hn ρ hρ → _) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (encode_measurable E n T hn ρ hρ)))
theorem directions_measurable : Measurable (State.directions : State E n T hn ρ hρ → _) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (encode_measurable E n T hn ρ hρ)))

theorem measurable_mk {X : Type*} [MeasurableSpace X]
    {control : X → Control E n T hn ρ hρ} {progress : X → Counter.State n}
    {rows : X → Rows E n T} {directions : X → Directions E T}
    (hc : Measurable control) (hp : Measurable progress) (hr : Measurable rows) (hd : Measurable directions) :
    Measurable (fun x ↦ (⟨control x, progress x, rows x, directions x⟩ : State E n T hn ρ hρ)) :=
  (stateMeasurableEquiv E n T hn ρ hρ).symm.measurable.comp (hc.prodMk (hp.prodMk (hr.prodMk hd)))

theorem stageIndex_measurable : Measurable (stageIndex E n T hn ρ hρ) :=
  (measurable_of_countable (fun f : ℕ ↦ (⟨f % (T + 1), Nat.mod_lt _ (by omega)⟩ : Fin (T + 1)))).comp
    (measurable_fst.comp (progress_measurable E n T hn ρ hρ))

theorem rowDirection_measurable : Measurable (rowDirection E n ρ) := by
  have hc : Continuous (rowDirection E n ρ) :=
    continuous_const.smul (continuous_finset_sum Finset.univ (fun i _ ↦ continuous_apply i))
  exact hc.measurable

theorem cachedReply_measurable : Measurable (fun p : State E n T hn ρ hρ × (Rows E n T × Query E n T hn ρ hρ) ↦
    cachedReply E n T hn ρ hρ p.1 p.2.1 p.2.2) := by
  have hm : Measurable (fun p : ℕ × (ReferenceParameters E n T × Query E n T hn ρ hρ) ↦
      referenceReply hn hρ p.1 p.2.1.1 p.2.1.2 p.2.2) :=
    measurable_from_prod_countable_right (fun h ↦ referenceReply_measurable (E := E) (T := T) hn hρ h)
  have hr : Measurable (fun p : State E n T hn ρ hρ × (Rows E n T × Query E n T hn ρ hρ) ↦
      fun i j ↦ p.2.1 j i) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
  have hp : Measurable (fun p : State E n T hn ρ hρ × (Rows E n T × Query E n T hn ρ hρ) ↦
      (p.1.progress.1, ((p.1.directions, fun i j ↦ p.2.1 j i), p.2.2))) :=
    ((measurable_fst.comp (progress_measurable E n T hn ρ hρ)).comp measurable_fst).prodMk
      ((((directions_measurable E n T hn ρ hρ).comp measurable_fst).prodMk hr).prodMk
        (measurable_snd.comp measurable_snd))
  convert hm.comp hp using 1
  all_goals rfl

end

end NCConcave16991.DenseSmooth.Machine
