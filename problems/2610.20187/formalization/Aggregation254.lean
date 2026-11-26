import Problem254
import Audit254
import Mathlib.Analysis.Convex.Jensen

noncomputable section
open scoped BigOperators
namespace Paper254

def weightedPrediction {d : ℕ} {D : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → W.carrier)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) : W.carrier :=
  ⟨∑ j, p j • (x j).val,
    W.convex.sum_mem (fun j _ => hp j) hsum (fun j _ => (x j).property)⟩

def exponentialNormalizer {ι : Type*} [Fintype ι] (lam : ℝ) (p loss : ι → ℝ) : ℝ :=
  ∑ j, p j * Real.exp (-lam * loss j)

def exponentialUpdate {ι : Type*} [Fintype ι]
    (lam : ℝ) (p loss : ι → ℝ) (j : ι) : ℝ :=
  p j * Real.exp (-lam * loss j) / exponentialNormalizer lam p loss

/-- Finite Jensen's inequality applied to the actual proper prediction. -/
theorem master_mixable {d : ℕ} {D lam : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → W.carrier)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) {f : Loss d}
    (hf : ExpConcaveOn lam W.carrier f) :
    exponentialNormalizer lam p (fun j => f (x j).val) ≤
      Real.exp (-lam*f (weightedPrediction p x hp hsum).val) := by
  simpa only [exponentialNormalizer, weightedPrediction, smul_eq_mul] using
    hf.le_map_sum (fun j _ => hp j) hsum (fun j _ => (x j).property)

theorem exponentialNormalizer_pos {ι : Type*} [Fintype ι]
    (lam : ℝ) (p loss : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (j : ι) (hj : 0 < p j) : 0 < exponentialNormalizer lam p loss := by
  classical
  have hs : p j * Real.exp (-lam*loss j) ≤ exponentialNormalizer lam p loss := by
    change p j * Real.exp (-lam*loss j) ≤ ∑ k, p k * Real.exp (-lam*loss k)
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (hp k) (Real.exp_pos (-lam*loss k)).le) (Finset.mem_univ j)
  exact lt_of_lt_of_le (mul_pos hj (Real.exp_pos _)) hs

theorem exponential_update_one_step {d : ℕ} {D lam : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → W.carrier)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) {f : Loss d}
    (hf : ExpConcaveOn lam W.carrier f) (j : ι) (hj : 0 < p j) :
    lam*(f (weightedPrediction p x hp hsum).val-f (x j).val) ≤
      Real.log (exponentialUpdate lam p (fun k => f (x k).val) j)-Real.log (p j) := by
  have hZ := exponentialNormalizer_pos lam p (fun k => f (x k).val) hp j hj
  have hlog := Real.log_le_log hZ (master_mixable p x hp hsum hf)
  rw [Real.log_exp] at hlog
  unfold exponentialUpdate
  rw [Real.log_div (mul_ne_zero (ne_of_gt hj) (Real.exp_ne_zero _)) (ne_of_gt hZ),
    Real.log_mul (ne_of_gt hj) (Real.exp_ne_zero _), Real.log_exp]
  nlinarith

/-- Removing nonnegative mass and renormalizing the survivors can only
increase each surviving probability. -/
theorem pruning_increases_mass (p mass : ℝ) (hp : 0 ≤ p)
    (hm : 0 < mass) (hsmall : mass ≤ 1) : p ≤ p / mass := by
  apply (le_div_iff₀ hm).mpr
  nlinarith

end Paper254
#print axioms Paper254.master_mixable
#print axioms Paper254.exponential_update_one_step
