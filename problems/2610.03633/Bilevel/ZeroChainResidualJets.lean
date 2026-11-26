import Bilevel.ZeroChainResidualLocality
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Dimension-independent derivative estimates for the actual tail masks. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainResidualJets
open ZeroChain ZeroChainRegularity ZeroChainResidualCutoffs ZeroChainResidual ZeroChainResidualLocality

def squareCutoff (t : ℝ) : ℝ := coordinateCutoff t^2

theorem squareCutoff_contDiff : ContDiff ℝ 3 squareCutoff := coordinateCutoff_contDiff.pow 2

theorem squareCutoff_range (t : ℝ) : 0 ≤ squareCutoff t ∧ squareCutoff t ≤ 1 := by
  have h := coordinateCutoff_range t
  dsimp [squareCutoff]
  constructor
  · positivity
  · nlinarith

theorem squareCutoff_one {t : ℝ} (ht : 1/2 ≤ |t|) : squareCutoff t = 1 := by
  rw [squareCutoff, coordinateCutoff_one ht, one_pow]

theorem squareCutoff_deriv_compactSupport : HasCompactSupport (deriv squareCutoff) := by
  apply SmallGapProfileBounds.compactSupport_of_tail (1/2)
  intro t ht
  have h := ((coordinateCutoff_contDiff.differentiable (by norm_num) t).hasDerivAt.pow 2).deriv
  have hz : deriv coordinateCutoff t = 0 := by
    simpa only [iteratedDeriv_one] using coordinateCutoff_flat_outer 1 (by norm_num) (by norm_num) t ht
  change deriv squareCutoff t = _ at h
  rw [h, hz]
  simp

structure MaskControl (C : ℝ) : Prop where
  one_le : 1 ≤ C
  coordinate1 : ∀ t, |deriv coordinateCutoff t| ≤ C
  energy : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val energyCutoff t| ≤ C
  square : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val squareCutoff t| ≤ C

theorem mask_control_exists : ∃ C : ℝ, MaskControl C := by
  obtain ⟨A,hA,ha⟩ := cutoff_common_bound
  have he (j : Fin 4) := plateau_profile_bound squareCutoff squareCutoff_contDiff
    squareCutoff_range squareCutoff_deriv_compactSupport j.val (show j.val ≤ 3 by omega)
  choose B hB hb using he
  have hsum : 0 ≤ ∑ j, B j := Finset.sum_nonneg (fun j _ => hB j)
  refine ⟨A+∑ j, B j, ⟨by linarith, ?_, ?_, ?_⟩⟩
  · intro t
    have h := (ha 1 t).1
    simp only [Fin.val_one, iteratedDeriv_one] at h
    linarith
  · intro j t
    exact (ha j t).2.trans (le_add_of_nonneg_right hsum)
  · intro j t
    have hj : B j ≤ ∑ k, B k := Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ j)
    exact (hb j t).trans (by linarith)

theorem sum_abs_mul_le {n : ℕ} (u v : Space n) :
    (∑ j : Fin (n+1), |u j| * |v j|) ≤ ‖u‖*‖v‖ := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (n+1)))
    (fun j => |u j|) (fun j => |v j|)
  simp only [sq_abs] at hs
  rw [← norm_sq_coordinates u, ← norm_sq_coordinates v] at hs
  have hn : 0 ≤ ∑ j : Fin (n+1), |u j| * |v j| := Finset.sum_nonneg (fun _ _ => by positivity)
  apply (sq_le_sq₀ hn (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mp
  simpa only [mul_pow] using hs

theorem sum_abs_triple_le {n : ℕ} (u v w : Space n) :
    (∑ j : Fin (n+1), |u j| * |v j| * |w j|) ≤ ‖u‖*‖v‖*‖w‖ := by
  calc
    _ ≤ ∑ j : Fin (n+1), |u j| * |v j| * ‖w‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w j)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ j : Fin (n+1), |u j| * |v j|)*‖w‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_abs_mul_le u v) (norm_nonneg w)

theorem tailEnergy_jet_apply {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (k : ℕ) (hk : k ≤ 3) (v : Fin k → Space n) :
    iteratedFDeriv ℝ k (tailEnergy i) z v = ∑ j : Fin (n+1),
      if i ≤ j then (∏ l : Fin k, v l j)*iteratedDeriv k squareCutoff (z j) else 0 := by
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hc (j : Fin (n+1)) : ContDiff ℝ k (fun w : Space n => if i ≤ j then squareCutoff (w j) else 0) := by
    by_cases hij : i ≤ j
    · simp only [if_pos hij]
      exact (squareCutoff_contDiff.of_le hk').comp (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff
    · simp only [if_neg hij]
      exact contDiff_const
  change iteratedFDeriv ℝ k (fun w : Space n => ∑ j : Fin (n+1),
    if i ≤ j then squareCutoff (w j) else 0) z v = _
  rw [iteratedFDeriv_sum (fun j _ => hc j)]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i ≤ j
  · simp only [if_pos hij]
    change iteratedFDeriv ℝ k (squareCutoff ∘ EuclideanSpace.proj (𝕜:=ℝ) j) z v = _
    rw [(EuclideanSpace.proj (𝕜:=ℝ) j).iteratedFDeriv_comp_right squareCutoff_contDiff z hk']
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  · simp [if_neg hij, iteratedFDeriv_zero_fun]

theorem tailEnergy_second_bound {C : ℝ} (h : MaskControl C) {n : ℕ}
    (i : Fin (n+1)) (z : Space n) : ‖iteratedFDeriv ℝ 2 (tailEnergy i) z‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by linarith [h.one_le])
  intro v
  rw [tailEnergy_jet_apply i z 2 (by norm_num), Real.norm_eq_abs]
  calc
    _ ≤ ∑ j : Fin (n+1), |if i ≤ j then (∏ l : Fin 2, v l j)*iteratedDeriv 2 squareCutoff (z j) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (n+1), C*(|v 0 j| * |v 1 j|) := by
      apply Finset.sum_le_sum
      intro j _
      have hb := h.square 2 (z j)
      change |iteratedDeriv 2 squareCutoff (z j)| ≤ C at hb
      by_cases hij : i ≤ j
      · simp only [if_pos hij, Fin.prod_univ_two, abs_mul]
        nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg (v 0 j)) (abs_nonneg (v 1 j)))]
      · simp only [if_neg hij, abs_zero]
        exact mul_nonneg (by linarith [h.one_le]) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = C*(∑ j : Fin (n+1), |v 0 j| * |v 1 j|) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*(‖v 0‖*‖v 1‖) := mul_le_mul_of_nonneg_left (sum_abs_mul_le _ _) (by linarith [h.one_le])
    _ = _ := by rw [Fin.prod_univ_two]

theorem tailEnergy_third_bound {C : ℝ} (h : MaskControl C) {n : ℕ}
    (i : Fin (n+1)) (z : Space n) : ‖iteratedFDeriv ℝ 3 (tailEnergy i) z‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by linarith [h.one_le])
  intro v
  rw [tailEnergy_jet_apply i z 3 (by norm_num), Real.norm_eq_abs]
  calc
    _ ≤ ∑ j : Fin (n+1), |if i ≤ j then (∏ l : Fin 3, v l j)*iteratedDeriv 3 squareCutoff (z j) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (n+1), C*(|v 0 j| * |v 1 j| * |v 2 j|) := by
      apply Finset.sum_le_sum
      intro j _
      have hb := h.square 3 (z j)
      change |iteratedDeriv 3 squareCutoff (z j)| ≤ C at hb
      by_cases hij : i ≤ j
      · simp only [if_pos hij, Fin.prod_univ_three, abs_mul]
        nlinarith [mul_le_mul_of_nonneg_left hb
          (mul_nonneg (mul_nonneg (abs_nonneg (v 0 j)) (abs_nonneg (v 1 j))) (abs_nonneg (v 2 j)))]
      · simp only [if_neg hij, abs_zero]
        exact mul_nonneg (by linarith [h.one_le]) (by positivity)
    _ = C*(∑ j : Fin (n+1), |v 0 j| * |v 1 j| * |v 2 j|) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*(‖v 0‖*‖v 1‖*‖v 2‖) := mul_le_mul_of_nonneg_left (sum_abs_triple_le _ _ _) (by linarith [h.one_le])
    _ = _ := by rw [Fin.prod_univ_three]

def energyGradient {n : ℕ} (i : Fin (n+1)) (z : Space n) : Space n :=
  ∑ j : Fin (n+1), (if i ≤ j then 2*coordinateCutoff (z j)*deriv coordinateCutoff (z j) else 0) • basis j

theorem energyDerivative_eq_toDual {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    energyDerivative i z = InnerProductSpace.toDual ℝ (Space n) (energyGradient i z) := by
  ext v
  simp only [energyDerivative, energyGradient, ContinuousLinearMap.sum_apply,
    InnerProductSpace.toDual_apply, sum_inner, real_inner_smul_left, inner_basis]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem energyGradient_norm_bound {C : ℝ} (h : MaskControl C) {n : ℕ}
    (i : Fin (n+1)) (z : Space n) (hz : tailEnergy i z ≤ 1) : ‖energyGradient i z‖ ≤ 2*C := by
  have hC : 0 ≤ C := by linarith [h.one_le]
  have hs : ‖energyGradient i z‖^2 ≤ 4*C^2*tailEnergy i z := by
    rw [energyGradient, norm_sum_basis_sq (fun j : Fin (n+1) => j) Function.injective_id]
    rw [tailEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i ≤ j
    · simp only [if_pos hij]
      have hh := (sq_le_sq₀ (abs_nonneg (deriv coordinateCutoff (z j))) hC).mpr (h.coordinate1 (z j))
      rw [sq_abs] at hh
      have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg (coordinateCutoff (z j)))
      nlinarith
    · simp only [if_neg hij, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, le_refl]
  have hs' := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 4*C^2)
  nlinarith [norm_nonneg (energyGradient i z)]

theorem tailEnergy_first_bound {C : ℝ} (h : MaskControl C) {n : ℕ}
    (i : Fin (n+1)) (z : Space n) (hz : tailEnergy i z ≤ 1) :
    ‖iteratedFDeriv ℝ 1 (tailEnergy i) z‖ ≤ 2*C := by
  rw [← norm_iteratedFDeriv_fderiv (n:=0), norm_iteratedFDeriv_zero,
    (tailEnergy_hasFDerivAt i z).fderiv, energyDerivative_eq_toDual, LinearIsometryEquiv.norm_map]
  exact energyGradient_norm_bound h i z hz

theorem flat_jet_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : E) (k : ℕ) (hk : k ≤ 3)
    (hg0 : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g (f x)‖ = 0) :
    iteratedFDeriv ℝ k (g ∘ f) x = 0 := by
  let D := 1+∑ j ∈ Finset.range (k+1), ‖iteratedFDeriv ℝ j f x‖
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hi (j : ℕ) (hj0 : 1 ≤ j) (hjk : j ≤ k) : ‖iteratedFDeriv ℝ j f x‖ ≤ D^j := by
    have hs := Finset.single_le_sum (f:=fun l => ‖iteratedFDeriv ℝ l f x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (show j < k+1 by omega))
    have hb : ‖iteratedFDeriv ℝ j f x‖ ≤ D := by dsimp [D]; linarith
    exact hb.trans (by simpa only [pow_one] using pow_le_pow_right₀ hD hj0)
  have hb := norm_iteratedFDeriv_comp_le hg hf (show (k : WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)
    x (C:=0) (D:=D) (fun j hj => le_of_eq (hg0 j hj)) hi
  simpa only [mul_zero, zero_mul, norm_le_zero_iff] using hb

theorem tailMask_flat_jet {n : ℕ} (i : Fin (n+1)) (z : Space n) (hz : 1 ≤ tailEnergy i z)
    (k : ℕ) (hk : k ≤ 3) : iteratedFDeriv ℝ k (tailMask i) z = 0 := by
  apply flat_jet_comp (tailEnergy_contDiff i) energyCutoff_contDiff z k hk
  intro j hj
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, energyCutoff_flat_right j (by omega) _ hz, norm_zero]

theorem tailMask_jet_bound {C : ℝ} (h : MaskControl C) {n : ℕ}
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (tailMask i) z‖ ≤ (k.factorial : ℝ)*C*(2*C)^k := by
  have hC : 0 ≤ C := by linarith [h.one_le]
  by_cases hz : 1 ≤ tailEnergy i z
  · rw [tailMask_flat_jet i z hz k hk, norm_zero]
    positivity
  · apply norm_iteratedFDeriv_comp_le energyCutoff_contDiff (tailEnergy_contDiff i)
      (show (k : WithTop ℕ∞) ≤ 3 by exact_mod_cast hk) z
    · intro j hj
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact h.energy ⟨j, by omega⟩ _
    · intro j hj0 hjk
      have hj3 : j ≤ 3 := by omega
      interval_cases j
      · simpa only [pow_one] using tailEnergy_first_bound h i z (le_of_not_ge hz)
      · exact (tailEnergy_second_bound h i z).trans (by nlinarith [h.one_le, sq_nonneg (C-1)])
      · have hpow : (2*C)^2 ≤ (2*C)^3 := pow_le_pow_right₀ (by linarith [h.one_le]) (by norm_num)
        exact (tailEnergy_third_bound h i z).trans (by nlinarith [h.one_le, sq_nonneg (C-1)])

end Bilevel.ZeroChainResidualJets
