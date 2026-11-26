import Bilevel.GenieTheorem
import Mathlib.Data.Complex.ExponentialBounds

/-! The source's single sufficient dimension inequality controls both energy and projection radius. -/
noncomputable section
namespace Bilevel.GenieDimension

theorem logarithm_one_le (M T δ : ℝ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 ≤ Real.log (4*M*T/δ) := by
  have hp : 1 ≤ M*T := by nlinarith
  have harg : 4 ≤ 4*M*T/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have he : Real.exp 1 < 4*M*T/δ := lt_of_lt_of_le (by linarith [Real.exp_one_lt_d9]) harg
  exact ((Real.lt_log_iff_exp_lt (by positivity : 0 < 4*M*T/δ)).mpr he).le

theorem dimension_budget (d M T K θ ℓ : ℝ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hK : 1 ≤ K) (hθ : 1 ≤ θ) (hℓ : 1 ≤ ℓ)
    (hd : 128*K^2*(M+T)*θ^2*T*ℓ ≤ d) :
    0 < d-M-T-2 ∧ 8*M*(K^2*θ^2*T)*(8*ℓ/(d-M-T-2)) ≤ 1 := by
  let A := K^2*θ^2*T
  have hK2 : 1 ≤ K^2 := by nlinarith
  have hθ2 : 1 ≤ θ^2 := by nlinarith
  have hA : 1 ≤ A := by
    have h₁ : 1 ≤ K^2*θ^2 := by nlinarith
    dsimp [A]
    nlinarith
  have hAl : 1 ≤ A*ℓ := by nlinarith
  have hs : 2 ≤ M+T := by linarith
  have hD : 128*(M+T)*(A*ℓ) ≤ d := by dsimp [A]; nlinarith only [hd]
  have hd4 : 4*(M+T) ≤ d := by
    have h := mul_le_mul_of_nonneg_left hAl (show 0 ≤ 128*(M+T) by linarith)
    nlinarith
  have hn : d/2 ≤ d-M-T-2 := by linarith
  have hn64 : 64*M*A*ℓ ≤ d-M-T-2 := by
    have h := mul_nonneg (show 0 ≤ T by linarith) (show 0 ≤ A*ℓ by nlinarith)
    nlinarith [hD]
  have hnp : 0 < d-M-T-2 := by
    have hpos : 0 < 64*M*A*ℓ := by positivity
    linarith
  refine ⟨hnp,?_⟩
  have he : 8*M*A*(8*ℓ/(d-M-T-2)) = (64*M*A*ℓ)/(d-M-T-2) := by ring
  change 8*M*A*(8*ℓ/(d-M-T-2)) ≤ 1
  rw [he]
  exact (div_le_one hnp).mpr hn64

theorem sufficient_dimension (d M T K θ ℓ R τ : ℝ)
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hK : 1 ≤ K) (hθ : 1 ≤ θ) (hℓ : 1 ≤ ℓ)
    (hR : 0 < R) (_hτ : 0 < τ) (hratio : R^2 ≤ K^2*θ^2*T*τ^2)
    (hd : 128*K^2*(M+T)*θ^2*T*ℓ ≤ d) :
    let b := 8*ℓ/(d-M-T-2)
    0 < b ∧ T*M*b ≤ 1/2 ∧ 2*M*b ≤ τ^2/(4*R^2) := by
  obtain ⟨hn,henergy⟩ := dimension_budget d M T K θ ℓ hM hT hK hθ hℓ hd
  let b := 8*ℓ/(d-M-T-2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hK2 : 1 ≤ K^2 := by nlinarith
  have hθ2 : 1 ≤ θ^2 := by nlinarith
  have hprod : 1 ≤ K^2*θ^2 := by nlinarith
  have hA : T ≤ K^2*θ^2*T := by nlinarith
  have hmub : 0 ≤ M*b := by positivity
  have hc := mul_le_mul_of_nonneg_right hA (show 0 ≤ 8*M*b by positivity)
  have hcap : T*M*b ≤ 1/2 := by change 8*M*(K^2*θ^2*T)*b ≤ 1 at henergy; nlinarith
  have hr := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 8*M*b by positivity)
  have ht := mul_le_mul_of_nonneg_right henergy (sq_nonneg τ)
  have hproj : 2*M*b ≤ τ^2/(4*R^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*R^2)).mpr
    change (8*M*(K^2*θ^2*T)*b)*τ^2 ≤ 1*τ^2 at ht
    nlinarith [hr,ht]
  exact ⟨hb,hcap,hproj⟩

end Bilevel.GenieDimension
