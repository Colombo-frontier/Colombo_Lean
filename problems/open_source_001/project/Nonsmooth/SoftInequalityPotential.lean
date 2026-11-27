import Nonsmooth.SoftplusConvexity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α ι : Type} [Fintype ι]

def softInequalityPenalty (f : ι → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  ∑ i, softplus ((n : ℝ) * f i x)

theorem softInequalityWeight_eq_exp (f : ι → α → ℝ) (n : ℕ) (x : α) :
    softInequalityWeight f n x = Real.exp (-softInequalityPenalty f n x) := by
  simp only [softInequalityWeight, softInequalityPenalty, softInequalityStep_exp,
    ← Finset.sum_neg_distrib, Real.exp_sum]

theorem softInequalityPenalty_nonneg (f : ι → α → ℝ) (n : ℕ) (x : α) :
    0 ≤ softInequalityPenalty f n x :=
  Finset.sum_nonneg (fun i _ => Real.log_nonneg (by linarith [Real.exp_pos ((n : ℝ) * f i x)]))

theorem softInequalityPotential_density (U : α → ℝ) (f : ι → α → ℝ) (n : ℕ) (x : α) :
    Real.exp (-U x) * softInequalityWeight f n x =
      Real.exp (-(U x + softInequalityPenalty f n x)) := by
  rw [softInequalityWeight_eq_exp, neg_add, Real.exp_add]

theorem softInequalityPenalty_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E → ℝ) (hf : ∀ i, ContDiff ℝ ⊤ (f i)) (n : ℕ) :
    ContDiff ℝ ⊤ (softInequalityPenalty f n) := by
  exact ContDiff.sum (fun i _ => softplus_contDiff.comp (contDiff_const.mul (hf i)))

theorem softInequalityPenalty_convex {E : Type} [AddCommGroup E] [Module ℝ E]
    (f : ι → E → ℝ) {S : Set E} (hS : Convex ℝ S)
    (hf : ∀ i, ConvexOn ℝ S (f i)) (n : ℕ) :
    ConvexOn ℝ S (softInequalityPenalty f n) := by
  have hi (i : ι) : ConvexOn ℝ S (fun x => softplus ((n : ℝ) * f i x)) := by
    have hc : ConvexOn ℝ S (fun x => (n : ℝ) * f i x) := (hf i).smul (Nat.cast_nonneg n)
    refine ⟨hS, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (softplus_monotone (hc.2 hx hy ha hb hab)).trans
      (softplus_convex.2 (mem_univ _) (mem_univ _) ha hb hab)
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa only [softInequalityPenalty, Finset.sum_add_distrib, ← Finset.smul_sum]
    using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hi i).2 hx hy ha hb hab)

theorem softInequalityPotential_strongConvex {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U : E → ℝ) (f : ι → E → ℝ) {S : Set E} {ρ : ℝ}
    (hU : StrongConvexOn S ρ U) (hf : ∀ i, ConvexOn ℝ S (f i)) (n : ℕ) :
    StrongConvexOn S ρ (fun x => U x + softInequalityPenalty f n x) := by
  apply strongConvexOn_iff_convex.mpr
  have hc := strongConvexOn_iff_convex.mp hU
  have hs := hc.add (softInequalityPenalty_convex f hc.1 hf n)
  convert! hs using 1
  funext x
  dsimp only [Pi.add_apply]
  ring

end
end Nonsmooth
