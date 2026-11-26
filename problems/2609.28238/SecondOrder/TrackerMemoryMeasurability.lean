import SecondOrder.TrackedRun

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def optionVectorEncode {d : ℕ} (x : Option (Point d)) : Bool × Point d := (x.isSome,x.getD 0)

theorem optionVectorEncode_injective {d : ℕ} : Function.Injective (@optionVectorEncode d) := by
  intro x y he
  cases x <;> cases y <;> simp_all [optionVectorEncode]

def trackerMemoryEncode {d L : ℕ} (z : TrackerMemory d L) :
    ℕ × (ℕ → Point d) × Point d × (BinaryNode L → Bool × Point d) :=
  (z.length,z.points,z.anchor,fun i => optionVectorEncode (z.table i))

instance trackerMemoryMeasurableSpace (d L : ℕ) : MeasurableSpace (TrackerMemory d L) :=
  MeasurableSpace.comap trackerMemoryEncode inferInstance

theorem trackerMemoryEncode_injective {d L : ℕ} : Function.Injective (@trackerMemoryEncode d L) := by
  intro x y he
  have hl : x.length=y.length := congrArg Prod.fst he
  have hp : x.points=y.points := congrArg (fun z => z.2.1) he
  have ha : x.anchor=y.anchor := congrArg (fun z => z.2.2.1) he
  have ht : x.table=y.table := by
    funext i
    exact optionVectorEncode_injective (congrArg (fun z => z.2.2.2 i) he)
  cases x
  cases y
  simpa only [TrackerMemory.mk.injEq] using ⟨hl,hp,ha,ht⟩

theorem trackerMemoryEncode_measurable {d L : ℕ} : Measurable (@trackerMemoryEncode d L) := comap_measurable _

theorem trackerMemory_measurable_iff {A : Type*} [MeasurableSpace A] {d L : ℕ} {z : A → TrackerMemory d L} :
    Measurable z ↔ Measurable (fun a => trackerMemoryEncode (z a)) := by
  constructor
  · exact fun hz => trackerMemoryEncode_measurable.comp hz
  · intro hz s hs
    obtain ⟨t,ht,rfl⟩ := hs
    exact hz ht

theorem trackerMemory_measurable_fields {A : Type*} [MeasurableSpace A] {d L : ℕ} {z : A → TrackerMemory d L} :
    Measurable z ↔ Measurable (fun a => (z a).length) ∧ Measurable (fun a => (z a).points) ∧
      Measurable (fun a => (z a).anchor) ∧ Measurable (fun a i => optionVectorEncode ((z a).table i)) := by
  rw [trackerMemory_measurable_iff]
  constructor
  · intro hz
    exact ⟨hz.fst,hz.snd.fst,hz.snd.snd.fst,hz.snd.snd.snd⟩
  · rintro ⟨hl,hp,ha,ht⟩
    exact hl.prodMk (hp.prodMk (ha.prodMk ht))

theorem measurable_countable_lookup {A I E : Type*} [MeasurableSpace A] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] [MeasurableSpace E]
    {f : A → I → E} {index : A → I} (hf : ∀ i, Measurable (fun a => f a i)) (hi : Measurable index) :
    Measurable (fun a => f a (index a)) := by
  have hh : Measurable (fun w : A × I => f w.1 w.2) := measurable_from_prod_countable hf
  exact hh.comp (measurable_id.prodMk hi)

theorem trackerRead_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    {z : A → TrackerMemory d L} (hz : Measurable z) : Measurable (fun a => trackerRead (z a)) := by
  obtain ⟨hl,hp,ha,ht⟩ := trackerMemory_measurable_fields.mp hz
  apply ha.add
  apply Finset.measurable_sum
  intro l hmem
  have hv (i : BinaryNode L) : Measurable (fun a => ((z a).table i).getD 0) := (ht.eval (a := i)).snd
  have hi : Measurable (fun a => activeNode (z a).length l) :=
    (measurable_of_countable (fun n => activeNode n l)).comp hl
  have hc : MeasurableSet {a | binaryActive (z a).length l.val} := by
    have hb := ((measurable_of_countable (fun n => decide (binaryActive n l.val))).comp hl)
      (measurableSet_singleton true)
    change MeasurableSet {a | decide (binaryActive (z a).length l.val) = true} at hb
    simpa only [decide_eq_true_eq] using hb
  exact Measurable.ite hc (measurable_countable_lookup
    (f := fun a i => ((z a).table i).getD (0 : Point d)) hv hi) measurable_const

theorem trackerReset_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    {x anchor : A → Point d} (hx : Measurable x) (ha : Measurable anchor) :
    Measurable (fun a => trackerReset (L := L) (x a) (anchor a)) := by
  apply trackerMemory_measurable_fields.mpr
  refine ⟨measurable_const,measurable_pi_lambda _ (fun _ => hx),ha,?_⟩
  change Measurable (fun _ : A => fun _ : BinaryNode L => (false,(0 : Point d)))
  exact measurable_const

theorem trackerPushPoints_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    {z : A → TrackerMemory d L} {x : A → Point d} (hz : Measurable z) (hx : Measurable x) :
    Measurable (fun a => trackerPushPoints (z a) (x a)) := by
  have hf := trackerMemory_measurable_fields.mp hz
  apply measurable_pi_lambda
  intro k
  have he (a : A) : trackerPushPoints (z a) (x a) k =
      if k=(z a).length+1 then x a else (z a).points k := by
    by_cases hk : k=(z a).length+1
    · rw [hk]
      simp [trackerPushPoints]
    · simp [trackerPushPoints,hk]
  simp_rw [he]
  exact Measurable.ite (measurableSet_eq_fun_of_countable measurable_const (hf.1.add_const 1)) hx (hf.2.1.eval (a := k))

theorem trackerPush_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    {z : A → TrackerMemory d L} {x : A → Point d} {packet : A → BinaryNode L → Point d}
    (hz : Measurable z) (hx : Measurable x) (hp : Measurable packet) :
    Measurable (fun a => trackerPush (z a) (x a) (packet a)) := by
  have hf := trackerMemory_measurable_fields.mp hz
  apply trackerMemory_measurable_fields.mpr
  refine ⟨hf.1.add_const 1,trackerPushPoints_measurable hz hx,hf.2.2.1,?_⟩
  apply measurable_pi_lambda
  intro i
  have he (a : A) : optionVectorEncode ((trackerPush (z a) (x a) (packet a)).table i) =
      if nodeRight i=(z a).length+1 then (true,packet a i) else optionVectorEncode ((z a).table i) := by
    by_cases hh : nodeRight i=(z a).length+1 <;> simp [trackerPush,mem_createdNodes,hh,optionVectorEncode]
  simp_rw [he]
  exact Measurable.ite (measurableSet_eq_fun_of_countable measurable_const (hf.1.add_const 1))
    (measurable_const.prodMk (hp.eval (a := i))) (hf.2.2.2.eval (a := i))

end
end SecondOrder
