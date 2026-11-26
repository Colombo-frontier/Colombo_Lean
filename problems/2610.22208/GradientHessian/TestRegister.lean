import GradientHessian.OracleControl

/-! A finite measurable cumulative test register. Unused slots are zero.
Appending never removes an earlier nonzero test, and a hard capacity bound
guarantees that every selected vector is actually recorded. -/

namespace GradientHessian.TestRegister
open MeasureTheory
noncomputable section

abbrev Register (s : ℕ) (E : Type*) := ℕ × (Fin s → E)
variable {s : ℕ} {E : Type*} [Zero E]

def empty : Register s E := (0,fun _ => 0)
def output (t : Register s E) (j : Fin s) : E := if j.val<t.1 then t.2 j else 0

def append (t : Register s E) (v : E) : Register s E :=
  (if t.1<s then t.1+1 else t.1,
    fun j => if j.val=t.1 ∧ t.1<s then v else t.2 j)

theorem output_empty : output (empty : Register s E) = 0 := by
  funext j
  simp [empty,output]

omit [Zero E] in
theorem append_full (t : Register s E) (v : E) (h : s≤t.1) : append t v=t := by
  ext j
  · simp [append,not_lt.mpr h]
  · simp [append,not_lt.mpr h]

theorem append_inserts (t : Register s E) (v : E) (h : t.1<s) :
    output (append t v) ⟨t.1,h⟩=v := by simp [output,append,h]

theorem append_retains (t : Register s E) (v : E) (j : Fin s) (hj : output t j≠0) :
    output (append t v) j=output t j := by
  have hji : j.val<t.1 := by
    by_contra h
    exact hj (by simp [output,h])
  by_cases h : t.1<s
  · have hne : j.val≠t.1 := ne_of_lt hji
    have hlt : j.val<t.1+1 := by omega
    simp [output,append,h,hne,hlt,hji]
  · rw [append_full t v (not_lt.mp h)]

theorem append_output (t : Register s E) (v : E) (j : Fin s) :
    output (append t v) j = if j.val=t.1 ∧ t.1<s then v else output t j := by
  by_cases h : t.1<s
  · by_cases hj : j.val=t.1
    · simp [output,append,h,hj]
    · have he : j.val<t.1+1 ↔ j.val<t.1 := by omega
      simp [output,append,h,hj,he]
  · rw [append_full t v (not_lt.mp h)]
    simp [h]

omit [Zero E] in
theorem append_count (t : Register s E) (v : E) :
    (append t v).1=if t.1<s then t.1+1 else t.1 := rfl

omit [Zero E] in
theorem append_count_le (t : Register s E) (v : E) (h : t.1≤s) : (append t v).1≤s := by
  rw [append_count]
  split_ifs <;> omega

theorem append_norm_le {F : Type*} [NormedAddCommGroup F]
    (t : Register s F) (v : F) (ht : ∀ j, ‖output t j‖≤1) (hv : ‖v‖≤1) (j : Fin s) :
    ‖output (append t v) j‖≤1 := by
  rw [append_output]
  split_ifs
  · exact hv
  · exact ht j

variable [MeasurableSpace E]

theorem output_measurable : Measurable (@output s E _ ) := by
  apply measurable_pi_lambda
  intro j
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((measurable_pi_apply j).comp measurable_snd) measurable_const

omit [Zero E] in
theorem append_measurable : Measurable (Function.uncurry (@append s E)) := by
  apply Measurable.prodMk
  · exact Measurable.ite (measurableSet_lt measurable_fst.fst measurable_const)
      (measurable_fst.fst.add measurable_const) measurable_fst.fst
  · apply measurable_pi_lambda
    intro j
    have he : MeasurableSet {t : Register s E × E | j.val=t.1.1} := by
      simpa only [Set.preimage,Set.mem_singleton_iff,eq_comm] using
        (measurable_fst.fst : Measurable (fun t : Register s E × E => t.1.1))
          (measurableSet_singleton j.val)
    exact Measurable.ite
      (he.inter (measurableSet_lt measurable_fst.fst measurable_const))
      measurable_snd ((measurable_pi_apply j).comp measurable_fst.snd)

end
end GradientHessian.TestRegister
