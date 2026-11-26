import SecondOrder.CurvatureMeasurability

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def moveTag {d : ℕ} : IdealMove d → Fin 3
  | .halt => 0
  | .gradient _ => 1
  | .curvature _ => 2

def moveVector {d : ℕ} : IdealMove d → Point d
  | .halt => 0
  | .gradient g => g
  | .curvature u => u

def moveEncode {d : ℕ} (a : IdealMove d) : Fin 3 × Point d := (moveTag a,moveVector a)

theorem moveEncode_injective {d : ℕ} : Function.Injective (@moveEncode d) := by
  intro a b hab
  have ht : moveTag a = moveTag b := congrArg Prod.fst hab
  have hv : moveVector a = moveVector b := congrArg Prod.snd hab
  cases a <;> cases b <;> simp_all [moveTag, moveVector]

instance idealMoveMeasurableSpace (d : ℕ) : MeasurableSpace (IdealMove d) :=
  MeasurableSpace.comap moveEncode inferInstance

theorem moveEncode_measurable {d : ℕ} : Measurable (@moveEncode d) := comap_measurable _
theorem moveTag_measurable {d : ℕ} : Measurable (@moveTag d) := measurable_fst.comp moveEncode_measurable
theorem moveVector_measurable {d : ℕ} : Measurable (@moveVector d) := measurable_snd.comp moveEncode_measurable

theorem move_measurable_iff {X : Type*} [MeasurableSpace X] {d : ℕ} {a : X → IdealMove d} :
    Measurable a ↔ Measurable (fun x => moveEncode (a x)) := by
  constructor
  · exact fun ha => moveEncode_measurable.comp ha
  · intro ha s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact ha ht

theorem gradientMove_measurable {d : ℕ} : Measurable (@IdealMove.gradient d) := by
  rw [move_measurable_iff]
  exact measurable_const.prodMk measurable_id

theorem curvatureMove_measurable {d : ℕ} : Measurable (@IdealMove.curvature d) := by
  rw [move_measurable_iff]
  exact measurable_const.prodMk measurable_id

def stateEncode {d : ℕ} (z : IdealState d) : Point d × Bool × ℕ × ℕ × ℝ × ℝ :=
  (z.point,z.running,z.gradientMoves,z.curvatureMoves,z.gradientEnergy,z.curvatureEnergy)

theorem stateEncode_injective {d : ℕ} : Function.Injective (@stateEncode d) := by
  intro a b hab
  cases a
  cases b
  simpa [stateEncode, IdealState.mk.injEq] using hab

instance idealStateMeasurableSpace (d : ℕ) : MeasurableSpace (IdealState d) :=
  MeasurableSpace.comap stateEncode inferInstance

theorem stateEncode_measurable {d : ℕ} : Measurable (@stateEncode d) := comap_measurable _

theorem state_measurable_iff {X : Type*} [MeasurableSpace X] {d : ℕ} {z : X → IdealState d} :
    Measurable z ↔ Measurable (fun x => stateEncode (z x)) := by
  constructor
  · exact fun hz => stateEncode_measurable.comp hz
  · intro hz s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hz ht

theorem state_measurable_fields {X : Type*} [MeasurableSpace X] {d : ℕ} {z : X → IdealState d} :
    Measurable z ↔ Measurable (fun x => (z x).point) ∧ Measurable (fun x => (z x).running) ∧
      Measurable (fun x => (z x).gradientMoves) ∧ Measurable (fun x => (z x).curvatureMoves) ∧
      Measurable (fun x => (z x).gradientEnergy) ∧ Measurable (fun x => (z x).curvatureEnergy) := by
  rw [state_measurable_iff]
  constructor
  · intro hz
    exact ⟨hz.fst,hz.snd.fst,hz.snd.snd.fst,hz.snd.snd.snd.fst,
      hz.snd.snd.snd.snd.fst,hz.snd.snd.snd.snd.snd⟩
  · rintro ⟨hp,hr,hg,hc,hge,hce⟩
    exact hp.prodMk (hr.prodMk (hg.prodMk (hc.prodMk (hge.prodMk hce))))

theorem idealStep_as_ite {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool) :
    idealStep L s z a b =
    if z.running then
      if moveTag a = 1 then
        {z with
          point := gradientNext L z.point (moveVector a)
          gradientMoves := z.gradientMoves+1
          gradientEnergy := z.gradientEnergy+‖gradientNext L z.point (moveVector a)-z.point‖^2}
      else if moveTag a = 2 then
        {z with
          point := curvatureNext s z.point (moveVector a) b
          curvatureMoves := z.curvatureMoves+1
          curvatureEnergy := z.curvatureEnergy+‖curvatureNext s z.point (moveVector a) b-z.point‖^2}
      else {z with running := false}
    else z := by
  cases hr : z.running <;> cases a <;> simp [idealStep, moveTag, moveVector, hr]

theorem idealStep_measurable {X : Type*} [MeasurableSpace X] {d : ℕ} (L s : ℝ)
    {z : X → IdealState d} {a : X → IdealMove d} {b : X → Bool}
    (hz : Measurable z) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => idealStep L s (z x) (a x) (b x)) := by
  obtain ⟨hp,hr,hg,hc,hge,hce⟩ := state_measurable_fields.mp hz
  have ht := moveTag_measurable.comp ha
  have hv := moveVector_measurable.comp ha
  have hgn : Measurable (fun x => gradientNext L (z x).point (moveVector (a x))) :=
    hp.add (measurable_const.smul hv)
  have hcn : Measurable (fun x => curvatureNext s (z x).point (moveVector (a x)) (b x)) :=
    hp.add ((((measurable_of_countable signValue).comp hb).mul_const s).smul hv)
  simp_rw [idealStep_as_ite]
  apply Measurable.ite (hr (measurableSet_singleton true))
  · apply Measurable.ite (ht (measurableSet_singleton 1))
    · apply state_measurable_fields.mpr
      exact ⟨hgn,hr,hg.add_const 1,hc,hge.add ((hgn.sub hp).norm.pow_const 2),hce⟩
    · apply Measurable.ite (ht (measurableSet_singleton 2))
      · apply state_measurable_fields.mpr
        exact ⟨hcn,hr,hg,hc.add_const 1,hge,hce.add ((hcn.sub hp).norm.pow_const 2)⟩
      · exact state_measurable_fields.mpr ⟨hp,measurable_const,hg,hc,hge,hce⟩
  · exact hz

/-- Joint measurability in external randomness, past signs and current state. -/
def MeasurableIdealPolicy {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (policy : Ξ → IdealPolicy d) : Prop :=
  ∀ t, Measurable (fun w : (Ξ × (Fin t → Bool)) × IdealState d => policy w.1.1 t w.1.2 w.2)

theorem idealRun_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (t : ℕ) :
    Measurable (fun w : Ξ × (Fin t → Bool) => idealRun L s (policy w.1) t w.2) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hp : Measurable (fun w : Ξ × (Fin (t+1) → Bool) => (w.1,Fin.init w.2)) :=
      measurable_fst.prodMk ((measurable_of_countable (fun w : Fin (t+1) → Bool => Fin.init w)).comp measurable_snd)
    have hz := ih.comp hp
    exact idealStep_measurable L s hz ((hm t).comp (hp.prodMk hz))
      ((measurable_of_countable (fun w : Fin (t+1) → Bool => w (Fin.last t))).comp measurable_snd)

theorem decideMove_measurable {X : Type*} [MeasurableSpace X] {d : ℕ} (τ : ℝ)
    {g : X → Point d} {r : X → CurvatureReply d} (hg : Measurable g) (hr : Measurable r) :
    Measurable (fun x => decideMove τ (g x) (r x)) := by
  have he (x) : decideMove τ (g x) (r x) =
      if 4*τ < ‖g x‖ then .gradient (g x) else
        if curvatureTag (r x) then .curvature (curvatureVector (r x)) else .halt := by
    cases r x <;> simp [decideMove, curvatureTag, curvatureVector]
  simp_rw [he]
  exact Measurable.ite (measurableSet_lt measurable_const hg.norm) (gradientMove_measurable.comp hg)
    (Measurable.ite ((curvatureTag_measurable.comp hr) (measurableSet_singleton true))
      (curvatureMove_measurable.comp (curvatureVector_measurable.comp hr)) measurable_const)

end
end SecondOrder
