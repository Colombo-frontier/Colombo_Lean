import MatchingBounds1005.MaskComposition
import MatchingBounds1005.ConfinedMasks
import MatchingBounds1005.ConfinementSmoothness

/-! Explicit finite-order budgets for the actual source-confined objective. -/
noncomputable section
open scoped ContDiff BigOperators

namespace MatchingBounds1005.RadialHigher

def smoothnessConstant (p : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (p + 2), (n : ℝ) * compositionConstant n

theorem smoothnessConstant_one_le (p : ℕ) : 1 ≤ smoothnessConstant p := by
  have h : 0 ≤ ∑ n ∈ Finset.range (p + 2), (n : ℝ) * compositionConstant n :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg n)
      (zero_le_one.trans (compositionConstant_one_le n)))
  unfold smoothnessConstant
  linarith

theorem orderConstant_le {p n : ℕ} (hn : n ≤ p + 1) :
    (n : ℝ) * compositionConstant n ≤ smoothnessConstant p := by
  have h := Finset.single_le_sum (s := Finset.range (p + 2))
    (f := fun j : ℕ => (j : ℝ) * compositionConstant j)
    (fun j _ => mul_nonneg (Nat.cast_nonneg j) (zero_le_one.trans (compositionConstant_one_le j)))
    (Finset.mem_range.mpr (by omega : n < p + 2))
  exact h.trans (by unfold smoothnessConstant; linarith)

def baseBudget (p : ℕ) : ℝ := 1 / (16 * smoothnessConstant p)
def accuracyThreshold (p : ℕ) : ℝ := 1 / (40 * smoothnessConstant p)

theorem baseBudget_pos (p : ℕ) : 0 < baseBudget p := by
  have h := smoothnessConstant_one_le p
  unfold baseBudget
  positivity

theorem accuracyThreshold_pos (p : ℕ) : 0 < accuracyThreshold p := by
  have h := smoothnessConstant_one_le p
  unfold accuracyThreshold
  positivity

theorem accuracyThreshold_le_one (p : ℕ) : accuracyThreshold p ≤ 1 := by
  have h := smoothnessConstant_one_le p
  unfold accuracyThreshold
  apply (div_le_iff₀ (by positivity : 0 < 40 * smoothnessConstant p)).mpr
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem uniform_base_composition {n : ℕ} (hn : 2 ≤ n) {F : E → ℝ}
    (hF : ContDiff ℝ n F) {b R : ℝ} (hb : 0 ≤ b) (hR : 1 ≤ R)
    (hzero : ‖iteratedFDeriv ℝ 1 F 0‖ ≤ b)
    (hjet : ∀ j, 2 ≤ j → j ≤ n → ∀ y : E, ‖iteratedFDeriv ℝ j F y‖ ≤ b)
    (x : E) :
    ‖iteratedFDeriv ℝ n (F ∘ radial R) x‖ ≤ 2 * n * compositionConstant n * b := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have h := radial_composition_budget hn hF hRpos (fun _ => b) (fun _ _ _ => hb) hjet x
  have hR1 : R ≤ R ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ hR (show 1 ≤ n by omega)
  have hsum : (∑ j ∈ Finset.Icc 2 n, b * R ^ j) ≤
      ((Finset.Icc 2 n).card : ℝ) * (b * R ^ n) := by
    calc
      _ ≤ ∑ _j ∈ Finset.Icc 2 n, b * R ^ n := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Finset.mem_Icc.mp hj).2) hb
      _ = _ := by simp
  have hcard : ((Finset.Icc 2 n).card : ℝ) + 1 = n := by
    exact_mod_cast (show (Finset.Icc 2 n).card + 1 = n by simp; omega)
  have hterm : ‖iteratedFDeriv ℝ 1 F 0‖ * R ≤ b * R ^ n :=
    mul_le_mul hzero hR1 hRpos.le hb
  have hall : ‖iteratedFDeriv ℝ 1 F 0‖ * R +
      (∑ j ∈ Finset.Icc 2 n, b * R ^ j) ≤ n * b * R ^ n := by
    calc
      _ ≤ b * R ^ n + ((Finset.Icc 2 n).card : ℝ) * (b * R ^ n) := add_le_add hterm hsum
      _ = _ := by rw [← hcard]; ring
  apply h.trans
  apply (div_le_iff₀ (pow_pos hRpos n)).mpr
  have hK : 0 ≤ 2 * compositionConstant n :=
    mul_nonneg (by norm_num) (zero_le_one.trans (compositionConstant_one_le n))
  exact (mul_le_mul_of_nonneg_left hall hK).trans_eq (by ring)

end MatchingBounds1005.RadialHigher

namespace MatchingBounds1005.TensorGeometry

theorem source_mask_composition {d n : ℕ} (hn : 2 ≤ n)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h3 : ‖tensorForm T₃‖ ≤ ε ^ 3 / 8) (h4 : ‖tensorForm T₄‖ ≤ ε ^ 4 / 8)
    (x : Vec d) :
    ‖iteratedFDeriv ℝ n (mask T₃ T₄ ∘ radial ε⁻¹) x‖ ≤
      6 * n * RadialHigher.compositionConstant n * ε ^ 2 := by
  have h := mask_radial_derivative_bound (by omega : 1 ≤ n) T₃ T₄ h3 h4 (inv_pos.mpr hε) x
  have hscale : ε ^ 3 / 8 * (ε⁻¹) ^ 3 + ε ^ 4 / 8 * (ε⁻¹) ^ 4 = 1 / 4 := by
    calc
      _ = ε⁻¹ * (ε ^ 3 / 8 * (ε⁻¹) ^ 2 + ε ^ 4 / 8 * (ε⁻¹) ^ 3) := by ring
      _ = _ := (source_mask_budgets hε).2.2
  rw [hscale, inv_pow, div_inv_eq_mul] at h
  have hp : ε ^ n ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 hn
  calc
    _ ≤ (24 * n * RadialHigher.compositionConstant n) * (1 / 4) * ε ^ n := h
    _ = (6 * n * RadialHigher.compositionConstant n) * ε ^ n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg (by positivity)
      (zero_le_one.trans (RadialHigher.compositionConstant_one_le n)))

theorem source_confined_class {d p : ℕ} {F : Vec d → ℝ}
    (hF : ContDiff ℝ ∞ F) (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ RadialHigher.accuracyThreshold p)
    (hzero : ‖iteratedFDeriv ℝ 1 F 0‖ ≤ RadialHigher.baseBudget p)
    (hjet : ∀ q, 1 ≤ q → q ≤ p → ∀ y : Vec d,
      ‖iteratedFDeriv ℝ (q + 1) F y‖ ≤ RadialHigher.baseBudget p)
    (hgap : ∀ y, F 0 - F y ≤ 1 / 4)
    (h3 : ‖tensorForm T₃‖ ≤ ε ^ 3 / 8) (h4 : ‖tensorForm T₄‖ ≤ ε ^ 4 / 8) :
    Model.InFunctionClass p (Confinement.objective (fun y => F y + mask T₃ T₄ y)
      ε⁻¹ (4 * ε ^ 2)) := by
  let C := RadialHigher.smoothnessConstant p
  have hC1 : 1 ≤ C := RadialHigher.smoothnessConstant_one_le p
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hb : 0 < RadialHigher.baseBudget p := RadialHigher.baseBudget_pos p
  have hε1 : ε ≤ 1 := hsmall.trans (RadialHigher.accuracyThreshold_le_one p)
  have hR : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  apply Model.confined_inFunctionClass hF (mask_smooth T₃ T₄) ε⁻¹ (4 * ε ^ 2)
    (fun q => 2 * (q + 1 : ℕ) * RadialHigher.compositionConstant (q + 1) * RadialHigher.baseBudget p)
    (fun q => 6 * (q + 1 : ℕ) * RadialHigher.compositionConstant (q + 1) * ε ^ 2)
  · intro q hq hqp x
    have hlevel : ((q + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
      by exact_mod_cast (show (q + 1 : ℕ∞) ≤ ⊤ from le_top)
    apply RadialHigher.uniform_base_composition (by omega) (hF.of_le hlevel) hb.le hR hzero
    intro j hj hjq y
    have he : j = (j - 1) + 1 := by omega
    rw [he]
    exact hjet (j - 1) (by omega) (by omega) y
  · intro q hq _ x
    exact source_mask_composition (by omega) T₃ T₄ hε hε1 h3 h4 x
  · intro q hq hqp
    have hk : ((q + 1 : ℕ) : ℝ) * RadialHigher.compositionConstant (q + 1) ≤ C :=
      RadialHigher.orderConstant_le (by omega)
    have hbase : 2 * (q + 1 : ℕ) * RadialHigher.compositionConstant (q + 1) *
        RadialHigher.baseBudget p ≤ 1 / 8 := by
      have hh := mul_le_mul_of_nonneg_right hk hb.le
      have he : C * RadialHigher.baseBudget p = 1 / 16 := by
        unfold RadialHigher.baseBudget
        change C * (1 / (16 * C)) = 1 / 16
        field_simp
        ring
      nlinarith only [hh, he]
    have hmask := mul_le_mul_of_nonneg_right hk (sq_nonneg ε)
    have hquad : (if q = 1 then |4 * ε ^ 2| else 0) ≤ 4 * ε ^ 2 := by
      split_ifs <;> simp [abs_of_nonneg (by positivity : 0 ≤ 4 * ε ^ 2)] <;> positivity
    have heps : 40 * C * ε ≤ 1 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 40 * C)).mp hsmall
      nlinarith only [hh]
    have heps2 : ε ^ 2 ≤ ε := by nlinarith only [hε, hε1]
    have heps2C := mul_le_mul_of_nonneg_left heps2 hC.le
    have hCeps := mul_le_mul_of_nonneg_right hC1 (sq_nonneg ε)
    nlinarith only [hbase, hmask, hquad, heps, heps2C, hCeps]
  · intro x
    exact (source_confined_gap F T₃ T₄ hε hgap h3 h4 x).trans (by norm_num)

end MatchingBounds1005.TensorGeometry
