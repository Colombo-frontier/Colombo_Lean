import FreshGradientMinimax.KernelTransport

/-! Finite segments of nonstationary kernels and exact periodic blocks. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X : Type*} [MeasurableSpace X]

def kernelSegment (L : ℕ → Kernel X X) (start : ℕ) : ℕ → Kernel X X
  | 0 => Kernel.id
  | n + 1 => L (start + n) ∘ₖ kernelSegment L start n

instance kernelSegment_markov (L : ℕ → Kernel X X) [∀ n, IsMarkovKernel (L n)] (start n : ℕ) :
    IsMarkovKernel (kernelSegment L start n) := by
  induction n with
  | zero => dsimp [kernelSegment]; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (L (start + n) ∘ₖ kernelSegment L start n)
    infer_instance

theorem kernelSegment_split (L : ℕ → Kernel X X) (start a b : ℕ) :
    kernelSegment L start (a + b) = kernelSegment L (start + a) b ∘ₖ kernelSegment L start a := by
  induction b with
  | zero => simp only [Nat.add_zero, kernelSegment, Kernel.id_comp]
  | succ b ih =>
    rw [Nat.add_succ, kernelSegment, ih, kernelSegment, Kernel.comp_assoc]
    simp only [Nat.add_assoc]

theorem kernelSegment_congr (L M : ℕ → Kernel X X) (start start' n : ℕ)
    (h : ∀ j < n, L (start + j) = M (start' + j)) : kernelSegment L start n = kernelSegment M start' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [kernelSegment, kernelSegment, h n (by omega), ih (fun j hj => h j (by omega))]

theorem kernelSegment_blocks (L : ℕ → Kernel X X) (b : ℕ)
    (hperiod : ∀ n j, L (n * b + j) = L j) (n : ℕ) :
    kernelSegment L 0 (n * b) = iterateKernel (kernelSegment L 0 b) n := by
  induction n with
  | zero => simp only [Nat.zero_mul, kernelSegment, iterateKernel]
  | succ n ih =>
    rw [Nat.succ_mul, kernelSegment_split, Nat.zero_add, ih, iterateKernel]
    have h : kernelSegment L (n * b) b = kernelSegment L 0 b :=
      kernelSegment_congr L L _ _ _ (fun j _ => by simpa only [Nat.zero_add] using hperiod n j)
    rw [h]

end FreshGradientMinimax
