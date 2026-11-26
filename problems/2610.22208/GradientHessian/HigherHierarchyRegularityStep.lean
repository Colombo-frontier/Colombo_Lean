import GradientHessian.CouplingCostHierarchy
import GradientHessian.HigherHierarchyValues

/-! Actual Leibniz estimates for one hierarchy layer. The order-zero
selector mass is at most one, so the inherited top derivative has coefficient
one rather than an iteration-dependent loss. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
open ScaledJets CouplingCost
open scoped BigOperators

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def selectedChildren (w : ℝ) (c : Fin 8 → E) (f : Fin 8 → F → ℝ) (Z : Layer F E) : ℝ :=
  ∑ i, InnerSelector.weight (nodePorts w c Z) i * f i (lower F E Z)

def selectorMassBound (w : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else 8*weightConstant/w^n

theorem selectorMassBound_nonneg {w : ℝ} (hw : 0 < w) (n : ℕ) : 0 ≤ selectorMassBound w n := by
  unfold selectorMassBound
  split_ifs
  · norm_num
  · exact div_nonneg (mul_nonneg (by norm_num) weightConstant_pos.le) (pow_nonneg hw.le n)

theorem selector_derivative_mass {w : ℝ} (hw : 0 < w) (c : Fin 8 → E)
    (Z : Layer F E) {n : ℕ} (hn : n ≤ 3) :
    (∑ i : Fin 8, ‖iteratedFDeriv ℝ n (fun W : Layer F E => InnerSelector.weight (nodePorts w c W) i) Z‖)
      ≤ selectorMassBound w n := by
  by_cases hn0 : n = 0
  · subst n
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, selectorMassBound, ↓reduceIte]
    simp_rw [abs_of_nonneg (SelectorPayloadBounds.finite_weight_nonneg _ (nodePorts_bounds w c Z) _)]
    have h := SelectorPayloadBounds.finite_weight_partition 8 (nodePorts w c Z)
    have hp : 0 ≤ ∏ i, nodePorts w c Z i := Finset.prod_nonneg (fun i _ => (nodePorts_bounds w c Z i).1)
    linarith
  · calc
      _ ≤ ∑ _i : Fin 8, weightConstant/w^n := Finset.sum_le_sum
        (fun i _ => (weight_scaledJets (F := F) hw c i).norm_le n hn Z)
      _ = selectorMassBound w n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          selectorMassBound, if_neg hn0]
        ring

theorem selectedChildren_contDiff {w : ℝ} (hw : 0 < w) (c : Fin 8 → E)
    (f : Fin 8 → F → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) :
    ContDiff ℝ 3 (selectedChildren w c f) :=
  ContDiff.sum (fun i _ => (weight_scaledJets (F := F) hw c i).smooth.mul
    ((hf i).comp (lower F E).contDiff))

theorem selectedChildren_derivative_bound {w : ℝ} (hw : 0 < w) (c : Fin 8 → E)
    (f : Fin 8 → F → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (A : ℕ → ℝ)
    (hA : ∀ j, j ≤ 3 → 0 ≤ A j)
    (hD : ∀ i j, j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ A j)
    (Z : Layer F E) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (selectedChildren w c f) Z‖ ≤
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * selectorMassBound w j * A (n-j) := by
  let g (i : Fin 8) : Layer F E → ℝ := fun W => f i (lower F E W)
  let a (i : Fin 8) : Layer F E → ℝ := fun W => InnerSelector.weight (nodePorts w c W) i
  have hg (i : Fin 8) : ContDiff ℝ 3 (g i) := (hf i).comp (lower F E).contDiff
  have ha (i : Fin 8) : ContDiff ℝ 3 (a i) := (weight_scaledJets (F := F) hw c i).smooth
  have hgD (i : Fin 8) (j : ℕ) (hj : j ≤ 3) : ‖iteratedFDeriv ℝ j (g i) Z‖ ≤ A j :=
    (Inner.derivative_comp_linear_le (lower F E) (lower_norm_le F E) (hf i) hj Z).trans (hD i j hj _)
  change ‖iteratedFDeriv ℝ n (fun W => ∑ i, a i W*g i W) Z‖ ≤ _
  rw [iteratedFDeriv_sum (fun i _ => ((ha i).mul (hg i)).of_le (by exact_mod_cast hn))]
  simp only [Finset.sum_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin 8, ∑ j ∈ Finset.range (n+1),
        (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j (a i) Z‖ * A (n-j) := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_iteratedFDeriv_mul_le (ha i) (hg i) Z (by exact_mod_cast hn)).trans
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul_of_nonneg_left (hgD i (n-j) ((Nat.sub_le n j).trans hn))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    _ = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        (∑ i : Fin 8, ‖iteratedFDeriv ℝ j (a i) Z‖) * A (n-j) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      apply mul_le_mul_of_nonneg_right _ (hA (n-j) ((Nat.sub_le n j).trans hn))
      exact mul_le_mul_of_nonneg_left (selector_derivative_mass hw c Z (hjn.trans hn)) (Nat.cast_nonneg _)

theorem selectedChildren_first_bound {w : ℝ} (hw : 0 < w) (c : Fin 8 → E)
    (f : Fin 8 → F → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (A : ℕ → ℝ)
    (hA : ∀ j, j ≤ 3 → 0 ≤ A j)
    (hD : ∀ i j, j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ A j) (Z : Layer F E) :
    ‖iteratedFDeriv ℝ 1 (selectedChildren w c f) Z‖ ≤ A 1 + 8*weightConstant*A 0/w := by
  convert selectedChildren_derivative_bound hw c f hf A hA hD Z (n := 1) (by norm_num) using 1;
    norm_num [Finset.sum_range_succ, selectorMassBound]; ring

theorem selectedChildren_second_bound {w : ℝ} (hw : 0 < w) (c : Fin 8 → E)
    (f : Fin 8 → F → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (A : ℕ → ℝ)
    (hA : ∀ j, j ≤ 3 → 0 ≤ A j)
    (hD : ∀ i j, j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ A j) (Z : Layer F E) :
    ‖iteratedFDeriv ℝ 2 (selectedChildren w c f) Z‖ ≤
      A 2 + 16*weightConstant*A 1/w + 8*weightConstant*A 0/w^2 := by
  convert selectedChildren_derivative_bound hw c f hf A hA hD Z (n := 2) (by norm_num) using 1;
    norm_num [Finset.sum_range_succ, selectorMassBound]; ring

theorem selectedChildren_third_bound {w : ℝ} (hw : 0 < w) (c : Fin 8 → E)
    (f : Fin 8 → F → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (A : ℕ → ℝ)
    (hA : ∀ j, j ≤ 3 → 0 ≤ A j)
    (hD : ∀ i j, j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ A j) (Z : Layer F E) :
    ‖iteratedFDeriv ℝ 3 (selectedChildren w c f) Z‖ ≤
      A 3 + 24*weightConstant*A 2/w + 24*weightConstant*A 1/w^2 + 8*weightConstant*A 0/w^3 := by
  convert selectedChildren_derivative_bound hw c f hf A hA hD Z (n := 3) (by norm_num) using 1;
    norm_num [Finset.sum_range_succ, selectorMassBound]; ring

end GradientHessian.HigherHierarchy

