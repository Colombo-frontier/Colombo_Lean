import SecondOrder.KernelContinuation

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

def historyCast {n m : ℕ} (he : n=m) : FiniteHistory S A n → FiniteHistory S A m :=
  he ▸ id

theorem historyCast_measurable {n m : ℕ} (he : n=m) :
    Measurable (historyCast (S := S) (A := A) he) := by
  subst m
  exact measurable_id

@[simp] theorem historyCast_refl (n : ℕ) : historyCast (S := S) (A := A) (rfl : n=n)=id := rfl

/-- Continuation to an absolute terminal time. The zero kernel outside
the time order makes finite sums well typed without changing any actual
continuation at an admissible entry time. -/
def kernelToTime (K : ∀ n, Kernel (FiniteHistory S A n) A) (n N : ℕ) :
    Kernel (FiniteHistory S A n) (FiniteHistory S A N) :=
  if h : n≤N then (kernelContinuation K n (N-n)).map (historyCast (Nat.add_sub_of_le h)) else 0

theorem kernelToTime_add (K : ∀ n, Kernel (FiniteHistory S A n) A) (n k : ℕ) :
    kernelToTime K n (n+k)=kernelContinuation K n k := by
  rw [kernelToTime,dif_pos (Nat.le_add_right n k)]
  have haux : ∀ l (he : l=k), (kernelContinuation K n l).map
      (historyCast (congrArg (fun z => n+z) he))=kernelContinuation K n k := by
    intro l he
    subst l
    simp only [historyCast_refl,Kernel.map_id]
  exact haux _ (Nat.add_sub_cancel_left n k)

theorem kernelToTime_self (K : ∀ n, Kernel (FiniteHistory S A n) A) (n : ℕ) :
    kernelToTime K n n=Kernel.id := kernelToTime_add K n 0

theorem kernelToTime_succ (K : ∀ n, Kernel (FiniteHistory S A n) A) {n N : ℕ} (hn : n≤N) :
    kernelToTime K n (N+1)=(Kernel.id ×ₖ K N) ∘ₖ kernelToTime K n N := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  change kernelToTime K n (n+(k+1))=(Kernel.id ×ₖ K (n+k)) ∘ₖ kernelToTime K n (n+k)
  rw [kernelToTime_add K n k,kernelToTime_add K n (k+1)]
  rfl

instance kernelToTime_sfinite (K : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] (n N : ℕ) : IsSFiniteKernel (kernelToTime K n N) := by
  unfold kernelToTime
  split_ifs <;> infer_instance

theorem kernelToTime_markov (K : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] {n N : ℕ} (hn : n≤N) : IsMarkovKernel (kernelToTime K n N) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [kernelToTime_add]
  infer_instance

end
end SecondOrder
