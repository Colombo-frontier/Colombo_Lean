import Nonsmooth.ParametricSelection

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {A : ℕ → Type} [∀ n, MeasurableSpace (A n)]

def kernelChain (κ : ∀ n, Kernel (A n) (A (n + 1))) : (n : ℕ) → Kernel (A 0) (A n)
  | 0 => Kernel.id
  | n + 1 => κ n ∘ₖ kernelChain κ n

instance kernelChain_markov (κ : ∀ n, Kernel (A n) (A (n + 1))) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) : IsMarkovKernel (kernelChain κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsMarkovKernel (κ n ∘ₖ kernelChain κ n))

/-- A possibly nonmeasurable invariant still excludes every measurable bad
terminal set. No measurability of the invariant itself is assumed. -/
theorem kernelChain_null_of_invariant (κ : ∀ n, Kernel (A n) (A (n + 1)))
    (P : ∀ n, A n → Prop)
    (hstep : ∀ n x, P n x → ∀ᵐ y ∂κ n x, P (n + 1) y)
    (x : A 0) (hx : P 0 x) (n : ℕ) (S : Set (A n)) (hS : MeasurableSet S)
    (hbad : ∀ z ∈ S, ¬ P n z) : kernelChain κ n x S = 0 := by
  induction n with
  | zero =>
    have hnot : x ∉ S := fun hmem => hbad x hmem hx
    simp only [kernelChain, Kernel.id_apply, Measure.dirac_apply' _ hS,
      indicator_of_notMem hnot]
  | succ n ih =>
    let T : Set (A n) := {z | κ n z S ≠ 0}
    have hT : MeasurableSet T :=
      (((κ n).measurable_coe hS) (measurableSet_singleton 0)).compl
    have hTb : ∀ z ∈ T, ¬ P n z := by
      intro z hz hp
      apply hz
      have ha : ∀ᵐ y ∂κ n z, y ∉ S :=
        (hstep n z hp).mono (fun y hy hmem => hbad y hmem hy)
      simpa only [ae_iff, not_not, Set.setOf_mem_eq] using ha
    have hzero := ih T hT hTb
    apply (Kernel.comp_null x hS).mpr
    change ∀ᵐ z ∂kernelChain κ n x, κ n z S = 0
    rw [ae_iff]
    exact hzero

theorem kernelChain_measurable_consequence (κ : ∀ n, Kernel (A n) (A (n + 1)))
    (P : ∀ n, A n → Prop)
    (hstep : ∀ n x, P n x → ∀ᵐ y ∂κ n x, P (n + 1) y)
    (x : A 0) (hx : P 0 x) (n : ℕ) (S : Set (A n)) (hS : MeasurableSet S)
    (hgood : ∀ z, P n z → z ∈ S) : ∀ᵐ z ∂kernelChain κ n x, z ∈ S := by
  have hzero := kernelChain_null_of_invariant κ P hstep x hx n Sᶜ hS.compl
    (fun z hz hp => hz (hgood z hp))
  exact hzero

theorem kernelChain_measurable_bound (κ : ∀ n, Kernel (A n) (A (n + 1)))
    (P : ∀ n, A n → Prop)
    (hstep : ∀ n x, P n x → ∀ᵐ y ∂κ n x, P (n + 1) y)
    (x : A 0) (hx : P 0 x) (n : ℕ) (f : A n → ℝ) (hf : Measurable f) (C : ℝ)
    (hbound : ∀ z, P n z → f z ≤ C) : ∀ᵐ z ∂kernelChain κ n x, f z ≤ C :=
  kernelChain_measurable_consequence κ P hstep x hx n {z | f z ≤ C}
    (measurableSet_le hf measurable_const) hbound

end
end Nonsmooth
