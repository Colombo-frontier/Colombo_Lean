import SecondOrder.PredictableEpochEnergy

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def StoppedEpochPartition {Ω : Type*} (M N : ℕ) (start finish : Fin N → Ω → ℕ) : Prop :=
  ∀ (i : Fin M) (w : Ω), ∃! e : Fin N, start e w ≤ i.val ∧ i.val < finish e w

def stoppedEpochIndex {Ω : Type*} {M N : ℕ} (start finish : Fin N → Ω → ℕ)
    (hpart : StoppedEpochPartition M N start finish) (i : Fin M) (w : Ω) : Fin N :=
  Classical.choose (hpart i w)

def stoppedEpochAddress {Ω : Type*} {M N : ℕ} (start finish : Fin N → Ω → ℕ)
    (hpart : StoppedEpochPartition M N start finish) (i : Fin M) (w : Ω) : Fin N × Fin M :=
  (stoppedEpochIndex start finish hpart i w,
    ⟨i.val-start (stoppedEpochIndex start finish hpart i w) w,(Nat.sub_le _ _).trans_lt i.isLt⟩)

theorem stoppedEpochAddress_iff {Ω : Type*} {M N : ℕ} (start finish : Fin N → Ω → ℕ)
    (hpart : StoppedEpochPartition M N start finish) (i : Fin M) (w : Ω) (e : Fin N) (k : Fin M) :
    stoppedEpochAddress start finish hpart i w=(e,k) ↔
      start e w ≤ i.val ∧ i.val < finish e w ∧ i.val-start e w=k.val := by
  have hspec := Classical.choose_spec (hpart i w)
  constructor
  · intro he
    have hje : stoppedEpochIndex start finish hpart i w=e := congrArg Prod.fst he
    have hactive : start e w ≤ i.val ∧ i.val < finish e w := by
      simpa only [←hje,stoppedEpochIndex] using hspec.1
    refine ⟨hactive.1,hactive.2,?_⟩
    have hk := congrArg (fun z : Fin N × Fin M => z.2.val) he
    simpa only [stoppedEpochAddress,hje] using hk
  · rintro ⟨hlo,hhi,hk⟩
    have hje : stoppedEpochIndex start finish hpart i w=e := (hspec.2 e ⟨hlo,hhi⟩).symm
    apply Prod.ext
    · exact hje
    · apply Fin.ext
      simpa only [stoppedEpochAddress,hje] using hk

theorem stoppedEpochAddress_injective {Ω : Type*} {M N : ℕ} (start finish : Fin N → Ω → ℕ)
    (hpart : StoppedEpochPartition M N start finish) (w : Ω) :
    Function.Injective (fun i => stoppedEpochAddress start finish hpart i w) := by
  intro i j he
  let r := stoppedEpochAddress start finish hpart i w
  have hi := (stoppedEpochAddress_iff start finish hpart i w r.1 r.2).mp rfl
  have hj := (stoppedEpochAddress_iff start finish hpart j w r.1 r.2).mp he.symm
  apply Fin.ext
  omega

/-- An exact stopped time below t is already observable by time t. -/
theorem stoppingTime_level_measurable {Ω : Type*} (past : ℕ → MeasurableSpace Ω)
    (hmono : Monotone past) (σ : Ω → ℕ)
    (hσ : ∀ n, MeasurableSet[past n] {w | σ w≤n}) {s t : ℕ} (hst : s≤t) :
    MeasurableSet[past t] {w | σ w=s} := by
  by_cases hs : s=0
  · subst s
    simpa only [Nat.le_zero] using hmono hst _ (hσ 0)
  · have he : {w | σ w=s}={w | σ w≤s} \ {w | σ w≤s-1} := by
      ext w
      simp only [Set.mem_setOf_eq,Set.mem_diff]
      omega
    rw [he]
    exact (hmono hst _ (hσ s)).diff (hmono ((Nat.sub_le _ _).trans hst) _ (hσ (s-1)))

theorem stoppingTime_measurable {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ n, past n≤m₀) (σ : Ω → ℕ)
    (hσ : ∀ n, MeasurableSet[past n] {w | σ w≤n}) : Measurable σ :=
  measurable_of_Iic (fun n => hp n _ (hσ n))

/-- A random partition into stopping-time intervals has predictable
epoch/local-time addresses. This is derived from the stopping events,
rather than assuming independence of a randomly selected future block. -/
theorem stoppedEpochAddress_predictable {Ω : Type*} {M N : ℕ}
    (start finish : Fin N → Ω → ℕ) (hpart : StoppedEpochPartition M N start finish)
    (past : ℕ → MeasurableSpace Ω) (hmono : Monotone past)
    (hstart : ∀ e t, MeasurableSet[past t] {w | start e w≤t})
    (hfinish : ∀ e t, MeasurableSet[past t] {w | finish e w≤t})
    (r : Fin N × Fin M) (i : Fin M) :
    MeasurableSet[past i.val] {w | stoppedEpochAddress start finish hpart i w=r} := by
  rcases r with ⟨e,k⟩
  by_cases hk : k.val ≤ i.val
  · have he : {w | stoppedEpochAddress start finish hpart i w=(e,k)}=
        {w | start e w=i.val-k.val} ∩ {w | i.val<finish e w} := by
      ext w
      simp only [Set.mem_setOf_eq,Set.mem_inter_iff,stoppedEpochAddress_iff]
      omega
    rw [he]
    have hf : MeasurableSet[past i.val] {w | i.val<finish e w} := by
      simpa only [Set.compl_setOf,not_le] using (hfinish e i.val).compl
    exact (stoppingTime_level_measurable past hmono (start e) (hstart e) (Nat.sub_le _ _)).inter hf
  · have he : {w | stoppedEpochAddress start finish hpart i w=(e,k)}=∅ := by
      ext w
      simp only [Set.mem_setOf_eq,stoppedEpochAddress_iff,Set.mem_empty_iff_false,iff_false]
      omega
    rw [he]
    exact @MeasurableSet.empty Ω (past i.val)

end
end SecondOrder
