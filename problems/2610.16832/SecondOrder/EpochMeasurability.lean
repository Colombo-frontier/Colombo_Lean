import SecondOrder.IdealEpochs

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def epochClockEncode (z : EpochClock) : ℕ × ℕ × ℕ := (z.number,z.gradients,z.start)

instance epochClockMeasurableSpace : MeasurableSpace EpochClock :=
  MeasurableSpace.comap epochClockEncode inferInstance

theorem epochClockEncode_injective : Function.Injective epochClockEncode := by
  intro x y h
  cases x
  cases y
  simpa [epochClockEncode,EpochClock.mk.injEq] using h

theorem epochClockEncode_measurable : Measurable epochClockEncode := comap_measurable _

theorem epochClock_measurable_iff {A : Type*} [MeasurableSpace A] {z : A → EpochClock} :
    Measurable z ↔ Measurable (fun a => epochClockEncode (z a)) := by
  constructor
  · exact fun hz => epochClockEncode_measurable.comp hz
  · intro hz s hs
    obtain ⟨t,ht,rfl⟩ := hs
    exact hz ht

theorem epochClockStep_measurable {A : Type*} [MeasurableSpace A] (q t : ℕ)
    {g : A → Bool} {z : A → EpochClock} (hg : Measurable g) (hz : Measurable z) :
    Measurable (fun a => epochClockStep q t (g a) (z a)) := by
  rw [epochClock_measurable_iff] at hz ⊢
  have hgr := hz.snd.fst.add_const 1
  have he (a : A) : epochClockEncode (epochClockStep q t (g a) (z a)) =
      if g a then
        if (z a).gradients+1 = q then ((z a).number+1,0,t+1)
        else ((z a).number,(z a).gradients+1,(z a).start)
      else epochClockEncode (z a) := by
    cases hg' : g a <;> simp only [epochClockStep,hg',Bool.false_eq_true,↓reduceIte]
    split_ifs <;> rfl
  simp_rw [he]
  exact Measurable.ite ((measurableSet_singleton true).preimage hg)
    (Measurable.ite ((measurableSet_singleton q).preimage hgr)
      ((hz.fst.add_const 1).prodMk (measurable_const.prodMk measurable_const))
      (hz.fst.prodMk (hgr.prodMk hz.snd.snd))) hz

theorem epochClock_measurable {A : Type*} [MeasurableSpace A] (q : ℕ) {g : A → ℕ → Bool}
    (hg : ∀ t, Measurable (fun a => g a t)) (t : ℕ) : Measurable (fun a => epochClock q (g a) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact epochClockStep_measurable q t (hg t) ih

theorem epochClock_variable_measurable {A : Type*} [MeasurableSpace A] (q : ℕ) {g : A → ℕ → Bool}
    (hg : ∀ t, Measurable (fun a => g a t)) {N : A → ℕ} (hN : Measurable N) :
    Measurable (fun a => epochClock q (g a) (N a)) := by
  have he : Measurable (fun w : A × ℕ => epochClock q (g w.1) w.2) := by
    apply measurable_from_prod_countable
    exact epochClock_measurable q hg
  exact he.comp (measurable_id.prodMk hN)

theorem epochAddress_measurable {A : Type*} [MeasurableSpace A] {q : ℕ} (hq : 0 < q) {g : A → ℕ → Bool}
    (hg : ∀ t, Measurable (fun a => g a t)) (t : ℕ) : Measurable (fun a => epochAddress q (g a) t) := by
  have hz := epochClockEncode_measurable.comp (epochClock_measurable q hg t)
  simp only [epochAddress,← epochClock_number hq]
  exact hz.fst.prodMk ((measurable_of_countable (fun n : ℕ => t-n)).comp hz.snd.snd)

theorem idealPath_congr {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) {w v : ℕ → Bool} {t : ℕ}
    (hh : ∀ i < t, w i = v i) : idealPath L s policy w t = idealPath L s policy v t := by
  unfold idealPath
  congr 1
  funext i
  exact hh i.val i.isLt

theorem idealGradientFlag_congr {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) {w v : ℕ → Bool} {t : ℕ}
    (hh : ∀ i < t, w i = v i) : idealGradientFlag L s policy w t = idealGradientFlag L s policy v t := by
  have he : (fun i : Fin t => w i.val) = (fun i : Fin t => v i.val) := funext (fun i => hh i.val i.isLt)
  unfold idealGradientFlag
  rw [idealPath_congr L s policy hh,he]

/-- The entire restart state is fixed before the next sign is sampled.
This includes the random epoch start and local binary-tree origin. -/
theorem idealEpochClock_predictable {d : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    {w v : ℕ → Bool} {t : ℕ} (hh : ∀ i < t, w i = v i) :
    epochClock q (idealGradientFlag L s policy w) t = epochClock q (idealGradientFlag L s policy v) t := by
  apply epochClock_congr
  intro i hi
  exact idealGradientFlag_congr L s policy (fun j hj => hh j (hj.trans hi))

theorem idealEpochClock_snoc {d t : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    (w : Fin t → Bool) (b : Bool) :
    epochClock q (idealGradientFlag L s policy (extendSigns (Fin.snoc w b))) t =
      epochClock q (idealGradientFlag L s policy (extendSigns w)) t := by
  apply idealEpochClock_predictable
  intro i hi
  simp only [extendSigns,dif_pos hi,dif_pos (show i < t+1 by omega)]
  exact Fin.snoc_castSucc (α := fun _ : Fin (t+1) => Bool) b w ⟨i,hi⟩

end
end SecondOrder
