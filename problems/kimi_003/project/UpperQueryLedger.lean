import ModelFull

open MeasureTheory

namespace Task006.Full

lemma measurable_actionToSum (d : ℕ) : Measurable (actionToSum d) := by
  exact measurable_iff_comap_le.mpr le_rfl

lemma measurable_some_action (d : ℕ) :
    Measurable (fun q : ℕ × Space d => (some q : QueryAction d)) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (fun q : ℕ × Space d => some q)
    (MeasurableSpace.comap (actionToSum d) inferInstance) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact measurable_inr.comap_le

/-- A query generator with unrestricted dependence on its private seed and past.
Pairing fixes only the handle schedule and never restricts output postprocessing. -/
structure PairedQueryProgram (d N : ℕ) (S : Type*) [MeasurableSpace S] where
  point : Fin N → S → Transcript N → Space d
  point_measurable : ∀ t, Measurable (fun sh : S × Transcript N => point t sh.1 sh.2)
  point_past : ∀ t s h h', (∀ i, i.val < t.val → h i = h' i) → point t s h = point t s h'
  postprocess : S → Transcript N → Space d
  postprocess_measurable : Measurable (fun sh : S × Transcript N => postprocess sh.1 sh.2)

namespace PairedQueryProgram

variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

def toAlgorithm (P : PairedQueryProgram d N S) : OracleAlgorithm d N S where
  action t s h := some (t.val / 2, P.point t s h)
  action_measurable t := (measurable_some_action d).comp
    (measurable_const.prodMk (P.point_measurable t))
  past_only t s h h' hh := by rw [P.point_past t s h h' hh]
  output := P.postprocess
  output_measurable := P.postprocess_measurable

lemma division_pair_card (N handle : ℕ) :
    (Finset.univ.filter (fun t : Fin N => t.val / 2 = handle)).card ≤ 2 := by
  let s := Finset.univ.filter (fun t : Fin N => t.val / 2 = handle)
  let f : s → Fin 2 := fun t => ⟨t.val.val % 2, Nat.mod_lt _ (by norm_num)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have ha : a.val.val / 2 = handle := (Finset.mem_filter.mp a.property).2
    have hb : b.val.val / 2 = handle := (Finset.mem_filter.mp b.property).2
    have hmod : a.val.val % 2 = b.val.val % 2 := congrArg Fin.val hab
    apply Subtype.ext
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

/-- Exactly one charged value per slot, including both values of every pair. -/
theorem reply_count_exact (P : PairedQueryProgram d N S)
    {Ω : Type*} (F : Space d → Ω → ℝ) (tape : ℕ → Ω) (seed : S) :
    (P.toAlgorithm.paidSlots F tape seed).card = N := by
  simp [OracleAlgorithm.paidSlots, OracleAlgorithm.executedAction, toAlgorithm]

/-- The paired schedule satisfies the two-reply contract on every path. -/
theorem handle_reply_cap (P : PairedQueryProgram d N S)
    {Ω : Type*} (F : Space d → Ω → ℝ) (tape : ℕ → Ω) (seed : S) (handle : ℕ) :
    (P.toAlgorithm.handleSlots F tape seed handle).card ≤ 2 := by
  have hs : P.toAlgorithm.handleSlots F tape seed handle =
      Finset.univ.filter (fun t : Fin N => t.val / 2 = handle) := by
    ext t
    simp [OracleAlgorithm.handleSlots, OracleAlgorithm.executedAction, toAlgorithm]
  rw [hs]
  exact division_pair_card N handle

/-- Domain and postprocessing bounds plus the actual paired ledger give the
complete pathwise oracle legality predicate. No performance guarantee is assumed. -/
theorem execution_legal (P : PairedQueryProgram d N S) (R : ℝ)
    (hq : ∀ t seed h, P.point t seed h ∈ queryDomain d R)
    (ho : ∀ seed h, P.postprocess seed h ∈ outputDomain d R)
    {Ω : Type*} (F : Space d → Ω → ℝ) (tape : ℕ → Ω) (seed : S) :
    P.toAlgorithm.executionLegal F tape seed R := by
  constructor
  · intro t handle x hx
    have he : x = P.point t seed (P.toAlgorithm.runPrefix F tape seed t.val) := by
      exact (congrArg Prod.snd (Option.some.inj hx)).symm
    rw [he]
    exact hq _ _ _
  · exact ⟨handle_reply_cap P F tape seed, ho _ _⟩

end PairedQueryProgram
end Task006.Full
