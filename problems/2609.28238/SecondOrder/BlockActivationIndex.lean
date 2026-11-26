import SecondOrder.KernelFirstEntry
import SecondOrder.CurvatureProgress

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X : Type u}

/-- Number of the last active block in an inspected prefix. Blocks use
zero-based indices and progress counts completed blocks. -/
def blockActivationIndex (active : Fin T → H → X → Prop) (Θ : Fin T → H)
    (x : X) (cap : ℕ) : ℕ :=
  Finset.univ.sup (fun i => if i.val<cap ∧ active i (Θ i) x then i.val+1 else 0)

theorem blockActivationIndex_le (active : Fin T → H → X → Prop) (Θ : Fin T → H)
    (x : X) (cap : ℕ) : blockActivationIndex active Θ x cap≤T ∧ blockActivationIndex active Θ x cap≤cap := by
  constructor <;> apply Finset.sup_le <;> intro i _ <;> split_ifs <;> omega

theorem blockActivationIndex_prefix (active : Fin T → H → X → Prop) (Θ Θ' : Fin T → H)
    (x : X) (cap : ℕ) (hΘ : ∀ i, i.val<cap → Θ i=Θ' i) :
    blockActivationIndex active Θ x cap=blockActivationIndex active Θ' x cap := by
  unfold blockActivationIndex
  congr 1
  funext i
  by_cases hi : i.val<cap
  · rw [hΘ i hi]
  · simp only [hi,false_and,if_false]

theorem active_le_blockActivationIndex (active : Fin T → H → X → Prop) (Θ : Fin T → H)
    (x : X) (cap : ℕ) (i : Fin T) (hi : i.val<cap) (ha : active i (Θ i) x) :
    i.val+1≤blockActivationIndex active Θ x cap := by
  have hh := Finset.le_sup (f := fun j : Fin T => if j.val<cap ∧ active j (Θ j) x then j.val+1 else 0)
    (Finset.mem_univ i)
  simpa only [hi,ha,and_self,if_true] using hh

theorem blockActivationIndex_no_far (active : Fin T → H → X → Prop) (Θ : Fin T → H)
    (x : X) (cap : ℕ) (hfar : ∀ i, cap ≤ i.val → ¬ active i (Θ i) x) :
    blockActivationIndex active Θ x cap=blockActivationIndex active Θ x T := by
  unfold blockActivationIndex
  congr 1
  funext i
  by_cases hi : i.val<cap
  · simp only [hi,i.isLt,true_and]
  · have ha := hfar i (by omega)
    simp only [hi,ha,and_false,if_false]

theorem blockActivationIndex_measurable [MeasurableSpace H] [MeasurableSpace X]
    (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    {B : Type*} [MeasurableSpace B] (Θ : B → Fin T → H) (x : B → X) (cap : B → ℕ)
    (hΘ : ∀ i, Measurable (fun b => Θ b i)) (hx : Measurable x) (hc : Measurable cap) :
    Measurable (fun b => blockActivationIndex active (Θ b) (x b) (cap b)) := by
  apply measurable_nat_finset_sup
  intro i _
  exact Measurable.ite ((measurableSet_lt measurable_const hc).inter
    ((ha i).preimage ((hΘ i).prodMk hx))) measurable_const measurable_const

theorem blockActivationIndex_all_active (active : Fin T → H → X → Prop) (Θ : Fin T → H)
    (x : X) (ha : ∀ i, active i (Θ i) x) : blockActivationIndex active Θ x T=T := by
  apply le_antisymm (blockActivationIndex_le active Θ x T).1
  cases T with
  | zero => exact Nat.zero_le _
  | succ t => exact active_le_blockActivationIndex active Θ x (t+1) (Fin.last t) (by omega) (ha _)

end
end SecondOrder
