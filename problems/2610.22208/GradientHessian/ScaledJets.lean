import GradientHessian.LocalizedProductDerivatives
import GradientHessian.InnerPayloadDerivatives

/-! Product calculus for actual scalar jets through order three. Constants
are uniform over the domain; no separation of the factors is required. -/

noncomputable section
namespace GradientHessian.ScaledJets
open scoped BigOperators

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

structure Bound (f : F → ℝ) (C r : ℝ) : Prop where
  nonneg : 0 ≤ C
  smooth : ContDiff ℝ 3 f
  norm_le : ∀ n, n ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C / r ^ n

theorem Bound.mono {f : F → ℝ} {C D r : ℝ} (h : Bound f C r)
    (hr : 0 < r) (hCD : C ≤ D) : Bound f D r :=
  ⟨h.nonneg.trans hCD, h.smooth, fun n hn x => (h.norm_le n hn x).trans
    (div_le_div_of_nonneg_right hCD (pow_nonneg hr.le n))⟩

theorem constant {r C c : ℝ} (hr : 0 < r) (hc : |c| ≤ C) :
    Bound (fun _ : F => c) C r := by
  refine ⟨(abs_nonneg c).trans hc, contDiff_const, ?_⟩
  intro n _ x
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, div_one] using hc
  | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
              exact div_nonneg ((abs_nonneg c).trans hc) (pow_nonneg hr.le _)

theorem Bound.mul {f g : F → ℝ} {C D r : ℝ} (hf : Bound f C r) (hg : Bound g D r)
    (hr : 0 < r) : Bound (fun x => f x * g x) (8 * C * D) r := by
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) hf.nonneg) hg.nonneg, hf.smooth.mul hg.smooth, ?_⟩
  intro n hn x
  apply (norm_iteratedFDeriv_mul_le hf.smooth hg.smooth x (by exact_mod_cast hn)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (C * D / r^n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hprod := mul_le_mul
        (mul_le_mul_of_nonneg_left (hf.norm_le i (hin.trans hn) x) (Nat.cast_nonneg (n.choose i)))
        (hg.norm_le (n-i) ((Nat.sub_le n i).trans hn) x) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg (n.choose i)) (div_nonneg hf.nonneg (pow_nonneg hr.le _)))
      apply hprod.trans_eq
      have hp : r^i * r^(n-i) = r^n := by rw [← pow_add, Nat.add_sub_of_le hin]
      rw [mul_assoc, div_mul_div_comm, hp]
    _ = 2^n * (C*D/r^n) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose n
    _ ≤ 8*C*D/r^n := by
      have hp : (2:ℝ)^n ≤ 8 := by
        calc (2:ℝ)^n ≤ 2^3 := pow_le_pow_right₀ (by norm_num) hn
             _ = _ := by norm_num
      have h := mul_le_mul_of_nonneg_right hp
        (div_nonneg (mul_nonneg hf.nonneg hg.nonneg) (pow_nonneg hr.le n))
      convert h using 1; ring

theorem Bound.sub {f g : F → ℝ} {C D r : ℝ} (hf : Bound f C r) (hg : Bound g D r)
    (_hr : 0 < r) : Bound (fun x => f x - g x) (C+D) r := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.sub hg.smooth, ?_⟩
  intro n hn x
  have h := LocalizedProductDerivatives.norm_iteratedFDeriv_sub_le
    (hf.smooth.of_le (by exact_mod_cast hn)).contDiffAt
    (hg.smooth.of_le (by exact_mod_cast hn)).contDiffAt (x := x)
  exact h.trans ((add_le_add (hf.norm_le n hn x) (hg.norm_le n hn x)).trans_eq
    (by rw [add_div]))

theorem Bound.changeScale {f : F → ℝ} {C r b : ℝ} (hf : Bound f C r)
    (hr : 0 < r) (hb : 0 < b) (hbr : b ≤ 4*r) : Bound f (64*C) b := by
  refine ⟨mul_nonneg (by norm_num) hf.nonneg, hf.smooth, ?_⟩
  intro n hn x
  apply (hf.norm_le n hn x).trans
  apply (div_le_div_iff₀ (pow_pos hr n) (pow_pos hb n)).mpr
  have hp : b^n ≤ 64*r^n := by
    calc b^n ≤ (4*r)^n := pow_le_pow_left₀ hb.le hbr n
         _ = 4^n*r^n := mul_pow _ _ _
         _ ≤ 64*r^n := by
           apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le _)
           calc (4:ℝ)^n ≤ 4^3 := pow_le_pow_right₀ (by norm_num) hn
                _ = _ := by norm_num
  have h := mul_le_mul_of_nonneg_left hp hf.nonneg
  nlinarith

theorem Bound.comp_linear {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → ℝ} {C r : ℝ} (hf : Bound f C r) (L : G →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    Bound (fun x => f (L x)) C r := by
  refine ⟨hf.nonneg, hf.smooth.comp L.contDiff, ?_⟩
  intro n hn x
  exact (Inner.derivative_comp_linear_le L hL hf.smooth hn x).trans (hf.norm_le n hn (L x))

theorem finset_prod {ι : Type*} (s : Finset ι) (f : ι → F → ℝ) {C r : ℝ}
    (hr : 0 < r) (hf : ∀ i ∈ s, Bound (f i) C r) :
    Bound (fun x => ∏ i ∈ s, f i x) ((8*C)^s.card) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (constant (F := F) hr (c := 1) (C := 1) (by norm_num))
  | @insert i s hi ih =>
    have hiB := hf i (Finset.mem_insert_self _ _)
    have hsB := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi, Finset.card_insert_of_not_mem hi, pow_succ,
      mul_comm ((8*C)^s.card)] using hiB.mul hsB hr

theorem finset_sum {ι : Type*} (s : Finset ι) (f : ι → F → ℝ) {C r : ℝ}
    (_hr : 0 < r) (hC : 0 ≤ C) (hf : ∀ i ∈ s, Bound (f i) C r) :
    Bound (fun x => ∑ i ∈ s, f i x) (s.card*C) r := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hC, ContDiff.sum (fun i hi => (hf i hi).smooth), ?_⟩
  intro n hn x
  rw [iteratedFDeriv_sum (fun i hi => ((hf i hi).smooth.of_le (by exact_mod_cast hn)))]
  simp only [Finset.sum_apply]
  apply (norm_sum_le _ _).trans
  calc _ ≤ ∑ i ∈ s, C/r^n := Finset.sum_le_sum (fun i hi => (hf i hi).norm_le n hn x)
       _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end GradientHessian.ScaledJets




