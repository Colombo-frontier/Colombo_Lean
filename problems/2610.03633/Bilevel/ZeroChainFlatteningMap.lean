import Bilevel.ZeroChainFlatteningCutoff

/-! The actual coordinate flattening map and dimension-independent jet norms. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainFlatteningMap
open ZeroChain ZeroChainRegularity ZeroChainFlatteningCutoff

def coordinateMap (n : ℕ) (f : ℝ → ℝ) (z : Space n) : Space n :=
  (WithLp.equiv 2 (Fin (n+1) → ℝ)).symm (fun j => f (z j))
def coreMap (n : ℕ) : Space n → Space n := coordinateMap n core
def flattenMap (n : ℕ) (δ : ℝ) : Space n → Space n := coordinateMap n (flatten δ)

@[simp] theorem coordinateMap_apply (n : ℕ) (f : ℝ → ℝ) (z : Space n) (j : Fin (n+1)) :
    coordinateMap n f z j = f (z j) := rfl

theorem coordinateMap_contDiff (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 3 (coordinateMap n f) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact hf.comp (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff

theorem coreMap_contDiff (n : ℕ) : ContDiff ℝ 3 (coreMap n) := coordinateMap_contDiff n core_contDiff
theorem flattenMap_contDiff (n : ℕ) (δ : ℝ) : ContDiff ℝ 3 (flattenMap n δ) :=
  coordinateMap_contDiff n (flatten_contDiff δ)

theorem coordinateMap_jet_apply (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (z : Space n) (k : ℕ) (hk : k ≤ 3) (v : Fin k → Space n) (j : Fin (n+1)) :
    iteratedFDeriv ℝ k (coordinateMap n f) z v j = (∏ l : Fin k, v l j)*iteratedDeriv k f (z j) := by
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hl := (EuclideanSpace.proj (𝕜:=ℝ) j).iteratedFDeriv_comp_left
    (coordinateMap_contDiff n hf).contDiffAt (x:=z) hk'
  have he : EuclideanSpace.proj (𝕜:=ℝ) j ∘ coordinateMap n f = f ∘ EuclideanSpace.proj (𝕜:=ℝ) j := rfl
  rw [he, (EuclideanSpace.proj (𝕜:=ℝ) j).iteratedFDeriv_comp_right hf z hk'] at hl
  have hh := congrArg (fun D => D v) hl
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] using hh.symm

theorem norm_le_of_coord_abs_le {n : ℕ} (u v : Space n) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ j, |u j| ≤ M*|v j|) : ‖u‖ ≤ M*‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  rw [mul_pow, norm_sq_coordinates u, norm_sq_coordinates v, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hh := (sq_le_sq₀ (abs_nonneg (u j)) (mul_nonneg hM (abs_nonneg (v j)))).mpr (hv j)
  simpa only [mul_pow, sq_abs] using hh

theorem coordinateMap_jet_norm_bound (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (z : Space n) (B : ℝ) (hB : 0 ≤ B) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3)
    (hb : ∀ t, |iteratedDeriv k f t| ≤ B) : ‖iteratedFDeriv ℝ k (coordinateMap n f) z‖ ≤ B := by
  apply ContinuousMultilinearMap.opNorm_le_bound hB
  intro v
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  let M := B*∏ l : Fin m, ‖v l.succ‖
  have hM : 0 ≤ M := mul_nonneg hB (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  have hcoord (j : Fin (n+1)) : |iteratedFDeriv ℝ (m+1) (coordinateMap n f) z v j| ≤ M*|v 0 j| := by
    rw [coordinateMap_jet_apply n hf z (m+1) hk v j, Fin.prod_univ_succ, abs_mul, abs_mul]
    have hp : |∏ l : Fin m, v l.succ j| ≤ ∏ l : Fin m, ‖v l.succ‖ := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro l _
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v l.succ) j
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hp (abs_nonneg (v 0 j)))
      (hb (z j)) (abs_nonneg _) (mul_nonneg (abs_nonneg (v 0 j)) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
    exact hh.trans_eq (by dsimp [M]; ring)
  have hh := norm_le_of_coord_abs_le (iteratedFDeriv ℝ (m+1) (coordinateMap n f) z v) (v 0) M hM hcoord
  exact hh.trans_eq (by rw [Fin.prod_univ_succ]; dsimp [M]; ring)

theorem coreMap_common_jet_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ (n k : ℕ), 1 ≤ k → k ≤ 3 → ∀ z : Space n,
    ‖iteratedFDeriv ℝ k (coreMap n) z‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := core_common_jet_bound
  exact ⟨B,hB,fun n k hk0 hk z => coordinateMap_jet_norm_bound n core_contDiff z B (by linarith) k hk0 hk (hb k hk0 hk)⟩

theorem flattenMap_jet_bound {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ t, |iteratedDeriv k core t| ≤ B)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) (z : Space n) :
    ‖iteratedFDeriv ℝ k (flattenMap n δ) z‖ ≤ B*δ/δ^k :=
  coordinateMap_jet_norm_bound n (flatten_contDiff δ) z _ (by positivity) k hk0 hk
    (flatten_jet_bound hb δ hδ k hk0 hk)

theorem flattenMap_eq_scaled_coreMap (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0) (z : Space n) :
    flattenMap n δ z = δ • coreMap n (δ⁻¹ • z) := by
  ext j
  simp only [flattenMap, coreMap, coordinateMap_apply, PiLp.smul_apply, smul_eq_mul,
    flatten_eq_scaled_core δ hδ, div_eq_inv_mul]

@[simp] theorem flattenMap_zero (n : ℕ) (δ : ℝ) : flattenMap n δ 0 = 0 := by
  ext j
  simp [flattenMap, coordinateMap, flatten]

theorem flattenMap_gradient_kills_small {n : ℕ} (δ : ℝ) (hδ : 0 < δ) (z : Space n)
    (j : Fin (n+1)) (hj : |z j| ≤ δ) : fderiv ℝ (flattenMap n δ) z (basis j) = 0 := by
  have hd : deriv (flatten δ) (z j) = 0 := by
    simpa only [iteratedDeriv_one] using flatten_flat_inner hδ 1 (by norm_num) (z j) hj
  ext l
  have he := coordinateMap_jet_apply n (flatten_contDiff δ) z 1 (by norm_num) (fun _ => basis j) l
  simp only [iteratedFDeriv_one_apply, Fin.prod_univ_one, iteratedDeriv_one] at he
  change (fderiv ℝ (coordinateMap n (flatten δ)) z (basis j)) l = 0
  rw [he]
  by_cases hlj : l = j
  · subst l
    rw [hd, mul_zero]
  · simp [basis, hlj, Ne.symm hlj]

end Bilevel.ZeroChainFlatteningMap
