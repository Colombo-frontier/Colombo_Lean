import Smoothness2601.WidthGeometry
import Smoothness2601.SineEnvelope
import Smoothness2601.Population

/-! A single choice of scale constants, before the regularity order, meets
all nonvanishing baseline and factorial-envelope constraints. -/
noncomputable section
open scoped BigOperators
namespace Smoothness2601

theorem finite_common_bound {n : ℕ} (f : Fin n → ℝ) : ∃ t : ℝ, 1 ≤ t ∧ ∀ i, f i ≤ t := by
  refine ⟨1+∑ i, |f i|,?_,?_⟩
  · have hs : 0 ≤ ∑ i, |f i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · intro i
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (f j)) (Finset.mem_univ i)
    have hf := le_abs_self (f i)
    linarith

theorem exists_uniform_width_constants (b : Budgets) (hgap : b.μ < b.L₁)
    {LA C₀ C₁ C₂ M Λ β : ℝ} (hLA : 0 ≤ LA) (_hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hM : 0 < M) (hΛ : 0 < Λ) :
    ∃ m c τ K : ℝ, b.μ < m ∧ m < b.L₁ ∧ 0 < c ∧ c ≤ b.L₀ ∧ 0 < τ ∧ 0 < K ∧
      τ*LA ≤ b.L₁ ∧ (m/c)*τ*K*C₂ ≤ (b.L₁-m)/2 ∧
      (m/c)*(τ*C₂+C₁/K) ≤ b.L₂ ∧ (m/c)*(C₁/K+C₀/(τ*K^2)) ≤ b.L₂ ∧
      Real.exp 1^β/(K*Λ) ≤ 1 ∧
      ((m/c)*(C₁+C₀))*(Real.exp 1^β/(K*Λ)) ≤ M*Λ := by
  let m := (b.μ+b.L₁)/2
  let c := min b.L₀ 1/2
  have hmμ : b.μ < m := by dsimp [m]; linarith
  have hmL : m < b.L₁ := by dsimp [m]; linarith
  have hm : 0 < m := b.μ_pos.trans hmμ
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (lt_min b.L₀_pos zero_lt_one) (by norm_num)
  have hcL : c ≤ b.L₀ := by
    dsimp [c]
    linarith [min_le_left b.L₀ (1:ℝ),b.L₀_pos]
  have hmc : 0 < m/c := div_pos hm hc
  let requests : Fin 6 → ℝ := ![LA/b.L₁,2*(m/c)*C₂/(b.L₁-m),
    (m/c)*(C₂+C₁)/b.L₂,(m/c)*(C₁+C₀)/b.L₂,
    Real.exp 1^β/Λ,((m/c)*(C₁+C₀))*Real.exp 1^β/(M*Λ^2)]
  obtain ⟨t,ht,hd⟩ := finite_common_bound requests
  have ht0 : 0 < t := by linarith
  have h0 : LA/b.L₁ ≤ t := hd 0
  have h1 : 2*(m/c)*C₂/(b.L₁-m) ≤ t := hd 1
  have h2 : (m/c)*(C₂+C₁)/b.L₂ ≤ t := hd 2
  have h3 : (m/c)*(C₁+C₀)/b.L₂ ≤ t := hd 3
  have h4 : Real.exp 1^β/Λ ≤ t := hd 4
  have h5 : ((m/c)*(C₁+C₀))*Real.exp 1^β/(M*Λ^2) ≤ t := hd 5
  have ht2 : t ≤ t^2 := by nlinarith
  obtain ⟨he1,he2,hi3,hi2⟩ := square_cube_scales ht
  refine ⟨m,c,1/t^3,t^2,hmμ,hmL,hc,hcL,by positivity,by positivity,?_,?_,?_,?_,?_,?_⟩
  · calc
      _ ≤ LA/t := (mul_le_mul_of_nonneg_right hi3 hLA).trans_eq (by ring)
      _ ≤ _ := (div_le_iff₀ ht0).mpr (by
        have hh := (div_le_iff₀ b.L₁_pos).mp h0
        nlinarith only [hh])
  · rw [mul_assoc (m/c) (1/t^3) (t^2),he1]
    apply (show (m/c)*(1/t)*C₂ = ((m/c)*C₂)/t by ring).trans_le
    apply (div_le_iff₀ ht0).mpr
    have hh := (div_le_iff₀ (sub_pos.mpr hmL)).mp h1
    nlinarith only [hh]
  · have ha := mul_le_mul_of_nonneg_right hi3 hC₂
    have hb := mul_le_mul_of_nonneg_right hi2 hC₁
    have hupper : (m/c)*((1/t^3)*C₂+C₁/t^2) ≤ ((m/c)*(C₂+C₁))/t := by
      have hh := mul_le_mul_of_nonneg_left (add_le_add ha hb) hmc.le
      convert hh using 1 <;> ring
    apply hupper.trans
    apply (div_le_iff₀ ht0).mpr
    have hh := (div_le_iff₀ b.L₂_pos).mp h2
    nlinarith only [hh]
  · have hb := mul_le_mul_of_nonneg_right hi2 hC₁
    have he : C₀/((1/t^3)*(t^2)^2) = C₀/t := by
      have hh := congrArg (fun u => C₀*u) he2
      simpa only [mul_one_div] using hh
    rw [he]
    have hupper : (m/c)*(C₁/t^2+C₀/t) ≤ ((m/c)*(C₁+C₀))/t := by
      have hh := mul_le_mul_of_nonneg_left (add_le_add_right hb (C₀/t)) hmc.le
      convert hh using 1 <;> ring
    apply hupper.trans
    apply (div_le_iff₀ ht0).mpr
    have hh := (div_le_iff₀ b.L₂_pos).mp h3
    nlinarith only [hh]
  · apply (div_le_one (by positivity : 0 < t^2*Λ)).mpr
    have hh := (div_le_iff₀ hΛ).mp h4
    exact hh.trans (mul_le_mul_of_nonneg_right ht2 hΛ.le)
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < t^2*Λ)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < M*Λ^2)).mp h5
    have hs := mul_le_mul_of_nonneg_right ht2 (by positivity : 0 ≤ M*Λ^2)
    nlinarith only [hh,hs]

end Smoothness2601
