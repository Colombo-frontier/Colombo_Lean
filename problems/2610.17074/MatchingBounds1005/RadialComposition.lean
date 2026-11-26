import MatchingBounds1005.RadialHigherBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! Dimension-free composition estimates for the actual radial map.
Outer function values never enter the derivative budget: the proof subtracts
the value at the evaluation point before applying the higher chain rule. -/
namespace MatchingBounds1005.RadialHigher

open Set
open scoped ContDiff Topology BigOperators

section Centering
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_sub_constant {n : ℕ} (hn : 1 ≤ n) {f : E → F}
    (hf : ContDiff ℝ n f) (c : F) (x : E) :
    iteratedFDeriv ℝ n (fun y => f y - c) x = iteratedFDeriv ℝ n f x := by
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' hf.contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega : n ≠ 0)]
  simp

theorem norm_comp_derivative_positive {n : ℕ} (hn : 1 ≤ n)
    {g : F → G} {f : E → F} (hg : ContDiff ℝ n g) (hf : ContDiff ℝ n f)
    (x : E) {C D : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * D ^ n := by
  let g₀ : F → G := fun y => g y - g (f x)
  have hg₀ : ContDiff ℝ n g₀ := hg.sub contDiff_const
  have hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g₀ (f x)‖ ≤ C := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa only [norm_iteratedFDeriv_zero, g₀, sub_self, norm_zero] using hC0
    · rw [show g₀ = (fun y => g y - g (f x)) from rfl,
        iteratedFDeriv_sub_constant (by omega) (hg.of_le (by exact_mod_cast hi))]
      exact hC i (by omega) hi
  have h := norm_iteratedFDeriv_comp_le hg₀ hf le_rfl x hb hD
  change ‖iteratedFDeriv ℝ n (fun y => (g ∘ f) y - g (f x)) x‖ ≤ _ at h
  rwa [iteratedFDeriv_sub_constant hn (hg.comp hf)] at h

end Centering

noncomputable def radialJet (n : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n + 1), normalizationConstant i

theorem radialJet_one_le (n : ℕ) : 1 ≤ radialJet n := by
  unfold radialJet
  have hs : 0 ≤ ∑ i ∈ Finset.range (n + 1), normalizationConstant i :=
    Finset.sum_nonneg (fun i _ => (normalizationConstant_pos i).le)
  linarith

theorem normalizationConstant_le_radialJet {i n : ℕ} (hi : i ≤ n) :
    normalizationConstant i ≤ radialJet n := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range (n + 1)) => (normalizationConstant_pos j).le)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  exact h.trans (by unfold radialJet; linarith)

noncomputable def compositionConstant (n : ℕ) : ℝ := n.factorial * radialJet n ^ n

theorem compositionConstant_one_le (n : ℕ) : 1 ≤ compositionConstant n := by
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ (radialJet_one_le n))

section Space
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_one_jet_bound {n i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) (x : E) :
    ‖iteratedFDeriv ℝ i (radial 1 : E → E) x‖ ≤ radialJet n ^ i := by
  apply (radial_one_derivative_bound i x).trans
  apply (normalizationConstant_le_radialJet hin).trans
  simpa only [pow_one] using pow_le_pow_right₀ (radialJet_one_le n) hi1

/-- Arbitrary positive-order outer jet budgets on the image ball. The scaling
is exact: an outer derivative of order j contributes R^(j-n). -/
theorem radial_composition_jet_bound {n : ℕ} (hn : 1 ≤ n)
    {F : E → ℝ} (hF : ContDiff ℝ n F) {R : ℝ} (hR : 0 < R)
    (b : ℕ → ℝ) (hb : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ b j)
    (hbound : ∀ j, 1 ≤ j → j ≤ n → ∀ y : E, ‖y‖ ≤ R →
      ‖iteratedFDeriv ℝ j F y‖ ≤ b j) (x : E) :
    ‖iteratedFDeriv ℝ n (F ∘ radial R) x‖ ≤ compositionConstant n *
      (∑ j ∈ Finset.Icc 1 n, b j * R ^ j) / R ^ n := by
  let A : E →L[ℝ] E := R • ContinuousLinearMap.id ℝ E
  let B : E →L[ℝ] E := R⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ R := by
    dsimp only [A]
    rw [norm_smul R (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos hR]
    exact mul_le_of_le_one_right hR.le ContinuousLinearMap.norm_id_le
  have hB : ‖B‖ ≤ R⁻¹ := by
    dsimp only [B]
    rw [norm_smul R⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hR.le) ContinuousLinearMap.norm_id_le
  let H : E → ℝ := F ∘ A
  have hH : ContDiff ℝ n H := hF.comp A.contDiff
  let C : ℝ := ∑ j ∈ Finset.Icc 1 n, b j * R ^ j
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hb j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
      (pow_nonneg hR.le j)
  have hjet : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i H (radial 1 (B x))‖ ≤ C := by
    intro i hi1 hin
    rw [show H = F ∘ A from rfl, A.iteratedFDeriv_comp_right hF _
      (by exact_mod_cast hin)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i F (A (radial 1 (B x)))‖ * ‖A‖ ^ i := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (iteratedFDeriv ℝ i F (A (radial 1 (B x)))).norm_compContinuousLinearMap_le
            (fun _ => A)
      _ ≤ b i * R ^ i := by
        apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg A) hA i)
          (by positivity) (hb i hi1 hin)
        apply hbound i hi1 hin
        change ‖R • radial 1 (R⁻¹ • x)‖ ≤ R
        rw [← radial_radius_scaling hR]
        exact (radial_norm_lt hR x).le
      _ ≤ C := Finset.single_le_sum
        (fun j hj => mul_nonneg (hb j (Finset.mem_Icc.mp hj).1
          (Finset.mem_Icc.mp hj).2) (pow_nonneg hR.le j))
        (Finset.mem_Icc.mpr ⟨hi1, hin⟩)
  have hcomp := norm_comp_derivative_positive hn hH (radial_contDiff 1 n)
    (B x) hC hjet (fun i hi1 hin => radial_one_jet_bound hi1 hin _)
  have heq : F ∘ radial R = (H ∘ radial 1) ∘ B := by
    funext y
    change F (radial R y) = F (R • radial 1 (R⁻¹ • y))
    rw [radial_radius_scaling hR]
  rw [heq, B.iteratedFDeriv_comp_right (hH.comp (radial_contDiff 1 n)) x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (H ∘ radial 1) (B x)‖ * ‖B‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (H ∘ radial 1) (B x)).norm_compContinuousLinearMap_le
          (fun _ => B)
    _ ≤ (n.factorial * C * radialJet n ^ n) * (R⁻¹) ^ n :=
      mul_le_mul hcomp (pow_le_pow_left₀ (norm_nonneg B) hB n)
        (by positivity) ((norm_nonneg _).trans hcomp)
    _ = _ := by simp only [compositionConstant, C, div_eq_mul_inv, inv_pow]; ring

theorem first_jet_growth {F : E → ℝ} (hF : ContDiff ℝ 2 F) {B : ℝ}
    (hB : ∀ y : E, ‖iteratedFDeriv ℝ 2 F y‖ ≤ B) (y : E) :
    ‖iteratedFDeriv ℝ 1 F y‖ ≤ ‖iteratedFDeriv ℝ 1 F 0‖ + B * ‖y‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ 1 F) :=
    hF.differentiable_iteratedFDeriv (by norm_num)
  have h := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hd x) (fun x _ => by simpa only [norm_fderiv_iteratedFDeriv] using hB x)
    (mem_univ (0 : E)) (mem_univ y)
  have ht := norm_add_le (iteratedFDeriv ℝ 1 F y - iteratedFDeriv ℝ 1 F 0)
    (iteratedFDeriv ℝ 1 F 0)
  rw [sub_add_cancel] at ht
  simp only [sub_zero] at h
  linarith

/-- The base-function part of the manuscript's composition budget. This uses
the gradient size at zero and only derivatives of order at least two; it has
the precise radius powers after division by R^n. -/
theorem radial_composition_budget {n : ℕ} (hn : 2 ≤ n)
    {F : E → ℝ} (hF : ContDiff ℝ n F) {R : ℝ} (hR : 0 < R)
    (B : ℕ → ℝ) (hB : ∀ j, 2 ≤ j → j ≤ n → 0 ≤ B j)
    (hbound : ∀ j, 2 ≤ j → j ≤ n → ∀ y : E,
      ‖iteratedFDeriv ℝ j F y‖ ≤ B j) (x : E) :
    ‖iteratedFDeriv ℝ n (F ∘ radial R) x‖ ≤ 2 * compositionConstant n *
      (‖iteratedFDeriv ℝ 1 F 0‖ * R + ∑ j ∈ Finset.Icc 2 n, B j * R ^ j) / R ^ n := by
  let c := ‖iteratedFDeriv ℝ 1 F 0‖
  let b : ℕ → ℝ := fun j => if j = 1 then c + B 2 * R else B j
  have hb : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ b j := by
    intro j hj1 hjn
    dsimp only [b]
    split_ifs with hj
    · exact add_nonneg (norm_nonneg _) (mul_nonneg (hB 2 le_rfl hn) hR.le)
    · exact hB j (by omega) hjn
  have hbnd : ∀ j, 1 ≤ j → j ≤ n → ∀ y : E, ‖y‖ ≤ R →
      ‖iteratedFDeriv ℝ j F y‖ ≤ b j := by
    intro j hj1 hjn y hy
    dsimp only [b]
    split_ifs with hj
    · subst j
      have hF2 : ContDiff ℝ 2 F := hF.of_le (by exact_mod_cast hn)
      exact (first_jet_growth hF2 (hbound 2 le_rfl hn) y).trans
        (add_le_add_left (mul_le_mul_of_nonneg_left hy (hB 2 le_rfl hn)) c)
    · exact hbound j (by omega) hjn y
  have h := radial_composition_jet_bound (by omega : 1 ≤ n) hF hR b hb hbnd x
  let S := ∑ j ∈ Finset.Icc 2 n, B j * R ^ j
  have hS : B 2 * R ^ 2 ≤ S := Finset.single_le_sum
    (fun j hj => mul_nonneg (hB j (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hj).2) (pow_nonneg hR.le j))
    (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
  have hs : (∑ j ∈ Finset.Icc 1 n, b j * R ^ j) =
      (c + B 2 * R) * R + S := by
    rw [← Nat.Icc_insert_succ_left (by omega : 1 ≤ n)]
    rw [Finset.sum_insert (by simp : 1 ∉ Finset.Icc 2 n)]
    simp only [b, if_pos rfl, pow_one]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : j ≠ 1 := by have := (Finset.mem_Icc.mp hj).1; omega
    simp only [if_neg hj1]
  have hsbound : (∑ j ∈ Finset.Icc 1 n, b j * R ^ j) ≤ 2 * (c * R + S) := by
    rw [hs]
    have hc : 0 ≤ c * R := mul_nonneg (norm_nonneg _) hR.le
    nlinarith
  apply h.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hR.le n)
  have hK : 0 ≤ compositionConstant n := (by norm_num : (0 : ℝ) ≤ 1).trans
    (compositionConstant_one_le n)
  calc
    _ ≤ compositionConstant n * (2 * (c * R + S)) :=
      mul_le_mul_of_nonneg_left hsbound hK
    _ = _ := by ring

end Space
end MatchingBounds1005.RadialHigher
