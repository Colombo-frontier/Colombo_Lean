import GradientHessian.SelectorVectorBounds
import GradientHessian.InnerSelectorPushforward

/-! Actual uniform stick-breaking derivative bounds. A norm-one bilinear
pairing combines the Bernoulli mass vector in ℓ¹ with the first-zero payoff
vector in ℓ∞. Payloads may share arbitrary coordinates. -/

namespace GradientHessian.SelectorPayloadBounds
open SelectorBernoulli SelectorPortBounds SelectorCoordinateBounds SelectorPortJets
  SelectorMassBounds SelectorVectorBounds InnerSelectorPushforward
open Classical
open scoped BigOperators
noncomputable section

/- The generic mass-vector module uses the classical finite-function
enumeration. Use that same instance for its finite-index specialization. -/
local instance outcomeFintype (m : ℕ) : Fintype (Fin m → Bool) :=
  @Pi.instFintype (Fin m) (fun _ => Bool)
    (fun a b => Classical.propDecidable (a = b)) (Fin.fintype m) (fun _ => Bool.fintype)

def pairingLinear (κ : Type*) [Fintype κ] : L1Vector κ →ₗ[ℝ] (κ → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a e => ∑ i, a i * e i)
    (by intro a b e; simp [PiLp.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a e; simp [PiLp.smul_apply, mul_assoc, Finset.mul_sum])
    (by intro a e f; simp [mul_add, Finset.sum_add_distrib])
    (by intro c a e; simp [Finset.mul_sum]; congr 1; ext i; ring)

theorem pairingLinear_bound (κ : Type*) [Fintype κ] (a : L1Vector κ) (e : κ → ℝ) :
    ‖pairingLinear κ a e‖ ≤ 1 * ‖a‖ * ‖e‖ := by
  change ‖∑ i, a i * e i‖ ≤ _
  calc
    _ ≤ ∑ i, ‖a i * e i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |a i| * ‖e‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm e i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← l1_norm, one_mul]

def pairing (κ : Type*) [Fintype κ] : L1Vector κ →L[ℝ] (κ → ℝ) →L[ℝ] ℝ :=
  (pairingLinear κ).mkContinuous₂ 1 (pairingLinear_bound κ)

@[simp] theorem pairing_apply (κ : Type*) [Fintype κ] (a : L1Vector κ) (e : κ → ℝ) :
    pairing κ a e = ∑ i, a i * e i := rfl

theorem pairing_norm_le (κ : Type*) [Fintype κ] : ‖pairing κ‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def payoffVector (m : ℕ) (e : Fin m → F → ℝ) (terminal : F → ℝ) (x : F) :
    (Fin m → Bool) → ℝ := fun ω => stopPayoff m (fun i => e i x) (terminal x) ω

theorem payoffVector_contDiff (m : ℕ) (e : Fin m → F → ℝ) (terminal : F → ℝ)
    (he : ∀ i, ContDiff ℝ 3 (e i)) (ht : ContDiff ℝ 3 terminal) :
    ContDiff ℝ 3 (payoffVector m e terminal) :=
  contDiff_pi.mpr (fun ω => stopPayoff_contDiff m ω e terminal he ht)

theorem payoffVector_derivative_apply (m : ℕ) (e : Fin m → F → ℝ) (terminal : F → ℝ)
    (he : ∀ i, ContDiff ℝ 3 (e i)) (ht : ContDiff ℝ 3 terminal) (x : F)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → F) (ω : Fin m → Bool) :
    (iteratedFDeriv ℝ n (payoffVector m e terminal) x w) ω =
      iteratedFDeriv ℝ n (fun y => stopPayoff m (fun i => e i y) (terminal y) ω) x w := by
  have h := (ContinuousLinearMap.proj ω : ((Fin m → Bool) → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (x := x) (payoffVector_contDiff m e terminal he ht).contDiffAt (by exact_mod_cast hn : (n : WithTop ℕ∞) ≤ 3)
  exact (congrArg (fun T => T w) h).symm

theorem payoffVector_derivative_bound (m : ℕ) (e : Fin m → F → ℝ) (terminal : F → ℝ)
    (he : ∀ i, ContDiff ℝ 3 (e i)) (ht : ContDiff ℝ 3 terminal) (x : F)
    {n : ℕ} (hn : n ≤ 3) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ i, ‖iteratedFDeriv ℝ n (e i) x‖ ≤ B)
    (hT : ‖iteratedFDeriv ℝ n terminal x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (payoffVector m e terminal) x‖ ≤ B := by
  apply ContinuousMultilinearMap.opNorm_le_bound hB
  intro w
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (Finset.prod_nonneg (fun j _ => norm_nonneg _)))).mpr
  intro ω
  rw [payoffVector_derivative_apply m e terminal he ht x hn]
  exact ((iteratedFDeriv ℝ n (fun y => stopPayoff m (fun i => e i y) (terminal y) ω) x).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (stopPayoff_derivative_bound m ω e terminal x n hD hT)
      (Finset.prod_nonneg (fun j _ => norm_nonneg _)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finite_weight_nonneg (p : Fin m → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) :
    0 ≤ InnerSelector.weight p i := by
  apply mul_nonneg (sub_nonneg.mpr (hp i).2)
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact (hp j).1
  · norm_num

theorem select_ones_partition (m : ℕ) (p : Fin m → ℝ) :
    InnerSelector.select m p (fun _ => 1) + (∏ i, p i) = 1 := by
  induction m with
  | zero => simp [InnerSelector.select]
  | succ m ih =>
    rw [InnerSelector.select, Fin.prod_univ_succ]
    calc
      _ = (1 - p 0) + p 0 *
          (InnerSelector.select m (fun i => p i.succ) (fun _ => 1) + ∏ i : Fin m, p i.succ) := by ring
      _ = 1 := by rw [ih]; ring

theorem finite_weight_partition (m : ℕ) (p : Fin m → ℝ) :
    (∑ i, InnerSelector.weight p i) + (∏ i, p i) = 1 := by
  have h := select_ones_partition m p
  simpa only [InnerSelector.select_eq_weighted_sum, mul_one] using h

def weightedScalar (R : ℝ) (v : Fin m → E) (A : Fin m → F →L[ℝ] E)
    (e : Fin m → F → ℝ) (terminal : F → ℝ) (x : F) : ℝ :=
  InnerSelector.select m (fun i => coordinatePort R v A i x) (fun i => e i x) +
    (∏ i, coordinatePort R v A i x) * terminal x

theorem weightedScalar_eq_source (R : ℝ) (v : Fin m → E) (A : Fin m → F →L[ℝ] E)
    (e : Fin m → F → ℝ) (terminal : F → ℝ) (x : F) :
    weightedScalar R v A e terminal x =
      (∑ i, InnerSelector.weight (fun j => coordinatePort R v A j x) i * e i x) +
        (∏ i, coordinatePort R v A i x) * terminal x := by
  rw [weightedScalar, InnerSelector.select_eq_weighted_sum]

theorem weightedScalar_eq_pairing (R : ℝ) (v : Fin m → E) (A : Fin m → F →L[ℝ] E)
    (e : Fin m → F → ℝ) (terminal : F → ℝ) (x : F) :
    weightedScalar R v A e terminal x = pairing (Fin m → Bool)
      (massVector R v A x) (payoffVector m e terminal x) := by
  rw [pairing_apply]
  convert (bernoulli_pushforward m (fun i => coordinatePort R v A i x)
    (fun i => e i x) (terminal x)).symm using 1
  congr 1
  ext ω
  simp

theorem weightedScalar_contDiff (R : ℝ) (v : Fin m → E) (A : Fin m → F →L[ℝ] E)
    (e : Fin m → F → ℝ) (terminal : F → ℝ)
    (he : ∀ i, ContDiff ℝ 3 (e i)) (ht : ContDiff ℝ 3 terminal) :
    ContDiff ℝ 3 (weightedScalar R v A e terminal) := by
  apply (InnerSelector.select_contDiff m _ _ (coordinatePort_contDiff R v A) he).add
  exact (contDiff_prod (fun i _ => coordinatePort_contDiff R v A i)).mul ht

/-- All product-rule estimates through order three for the actual finite
selector, with the source payload scale exponents. -/
theorem weightedScalar_derivative_bound {R C₀ S₀ : ℝ} (hR : 0 < R) (hC : 0 ≤ C₀) (hS : 0 ≤ S₀)
    (v : Fin m → E) (hv : ∀ i, ‖v i‖ = 1) (A : Fin m → F →L[ℝ] E) (hA : CoordinateContraction A)
    (e : Fin m → F → ℝ) (terminal : F → ℝ)
    (he : ∀ i, ContDiff ℝ 3 (e i)) (ht : ContDiff ℝ 3 terminal) (x : F)
    (hD : ∀ i j, j ≤ 3 → ‖iteratedFDeriv ℝ j (e i) x‖ ≤ C₀ * S₀ ^ (3 - j))
    (hT : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j terminal x‖ ≤ C₀ * S₀ ^ (3 - j))
    {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (weightedScalar R v A e terminal) x‖ ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (massConstant j / R ^ j) *
        (C₀ * S₀ ^ (3 - (n - j))) := by
  classical
  have heq : weightedScalar R v A e terminal = fun y => pairing (Fin m → Bool)
      (massVector R v A y) (payoffVector m e terminal y) := funext (weightedScalar_eq_pairing R v A e terminal)
  rw [heq]
  apply ((pairing (Fin m → Bool)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (𝕜 := ℝ) (N := 3) (f := massVector R v A) (g := payoffVector m e terminal) (n := n)
    (massVector_contDiff R v A) (payoffVector_contDiff m e terminal he ht) x
    (by exact_mod_cast hn) (pairing_norm_le _)).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hnj : n - j ≤ 3 := (Nat.sub_le n j).trans hn
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (massVector_derivative_bound hR v hv A hA x (hjn.trans hn))
      (Nat.cast_nonneg _)
  · exact payoffVector_derivative_bound m e terminal he ht x hnj
      (mul_nonneg hC (pow_nonneg hS _)) (fun i => hD i _ hnj) (hT _ hnj)
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (massConstant_nonneg j) (pow_nonneg hR.le _))

def selectorConstant : ℝ := 1 + ∑ j ∈ Finset.range 4, (Nat.choose 3 j : ℝ) * massConstant j

theorem selectorConstant_pos : 0 < selectorConstant := by
  have hs : 0 ≤ ∑ j ∈ Finset.range 4, (Nat.choose 3 j : ℝ) * massConstant j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (massConstant_nonneg j))
  unfold selectorConstant
  linarith

theorem selectorConstant_coefficient {j : ℕ} (hj : j ≤ 3) :
    (Nat.choose 3 j : ℝ) * massConstant j ≤ selectorConstant := by
  have hs := Finset.single_le_sum (s := Finset.range 4) (f := fun j => (Nat.choose 3 j : ℝ) * massConstant j)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (massConstant_nonneg j))
    (a := j) (Finset.mem_range.mpr (by omega))
  dsimp at hs
  unfold selectorConstant
  linarith

/-- The manuscript's third derivative selector estimate, including a
terminal payoff, with one absolute dimension-independent constant. -/
theorem manuscript_selector_bound {R C₀ S₀ : ℝ} (hR : 0 < R) (hC : 0 ≤ C₀) (hS : 0 ≤ S₀)
    (v : Fin m → E) (hv : ∀ i, ‖v i‖ = 1) (A : Fin m → F →L[ℝ] E) (hA : CoordinateContraction A)
    (e : Fin m → F → ℝ) (terminal : F → ℝ)
    (he : ∀ i, ContDiff ℝ 3 (e i)) (ht : ContDiff ℝ 3 terminal) (x : F)
    (hD : ∀ i j, j ≤ 3 → ‖iteratedFDeriv ℝ j (e i) x‖ ≤ C₀ * S₀ ^ (3 - j))
    (hT : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j terminal x‖ ≤ C₀ * S₀ ^ (3 - j)) :
    ‖iteratedFDeriv ℝ 3 (weightedScalar R v A e terminal) x‖ ≤
      selectorConstant * C₀ * (1 + S₀ / R + (S₀ / R) ^ 2 + (S₀ / R) ^ 3) := by
  apply (weightedScalar_derivative_bound hR hC hS v hv A hA e terminal he ht x hD hT (by norm_num)).trans
  have hs : (∑ j ∈ Finset.range 4, (Nat.choose 3 j : ℝ) * massConstant j * (S₀ / R) ^ j) ≤
      selectorConstant * ∑ j ∈ Finset.range 4, (S₀ / R) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (selectorConstant_coefficient (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (pow_nonneg (div_nonneg hS hR.le) _)
  have hm := mul_le_mul_of_nonneg_left hs hC
  convert hm using 1 <;> norm_num [Finset.sum_range_succ, Nat.choose]
  · field_simp [hR.ne']
    ring
  · ring

def uniformOrderConstant (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * massConstant j

theorem uniformOrderConstant_nonneg (n : ℕ) : 0 ≤ uniformOrderConstant n :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (massConstant_nonneg j))

theorem weightedScalar_uniform_bound {R C₀ : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C₀)
    (v : Fin m → E) (hv : ∀ i, ‖v i‖ = 1) (A : Fin m → F →L[ℝ] E) (hA : CoordinateContraction A)
    (e : Fin m → F → ℝ) (terminal : F → ℝ)
    (he : ∀ i, ContDiff ℝ 3 (e i)) (ht : ContDiff ℝ 3 terminal) (x : F)
    (hD : ∀ i j, j ≤ 3 → ‖iteratedFDeriv ℝ j (e i) x‖ ≤ C₀)
    (hT : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j terminal x‖ ≤ C₀)
    {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (weightedScalar R v A e terminal) x‖ ≤ C₀ * uniformOrderConstant n := by
  have hr : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h := weightedScalar_derivative_bound (S₀ := 1) hr hC (by norm_num) v hv A hA e terminal he ht x
    (by simpa using hD) (by simpa using hT) hn
  simp only [one_pow, mul_one] at h
  apply h.trans
  unfold uniformOrderConstant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hd : massConstant j / R ^ j ≤ massConstant j :=
    div_le_self (massConstant_nonneg j) (one_le_pow₀ hR)
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (n.choose j))) hC
  convert hm using 1
  ring

end
end GradientHessian.SelectorPayloadBounds
