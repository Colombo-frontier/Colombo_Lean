import Bilevel.ChiExtensionCalibration

/-! Explicit depth cancellations for the wide-window Hessian budgets.
The constants are fixed before theta, kappa, or the recursion depth. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiCurvatureSchedule ChiIndependentWidths

theorem sqrt_scale_pays_ledger {θ A CT : ℝ} (hθ : 0≤θ) (hA : 0≤A)
    (hCT : 0<CT) (hbound : A^2≤CT) (p q : ℕ) (hp : 2*q≤p) :
    A^(chosenDepth θ+1)*((chosenDepth θ:ℝ)+1)^q*Real.sqrt (scale θ CT p)≤Real.sqrt θ := by
  have hs := scale_pays_ledger (A:=A^2) hθ (sq_nonneg A) (by norm_num : (1:ℝ)≤1)
    hCT (by simpa using hbound) p (2*q) hp
  have hscale : 0≤scale θ CT p := by unfold scale; positivity
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg θ)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt hscale,Real.sq_sqrt hθ]
  simpa only [one_mul,div_one,← pow_mul,Nat.mul_comm] using hs

theorem fine_parameter_simple_upper {θ μ L η₀ a Cf : ℝ}
    (hθ : 0≤θ) (hμ : 0<μ) (hL : 0<L) (hη₀ : 0<η₀) (ha : 1≤a)
    (hCf : 0<Cf) (J : ℕ) (hJ : 1≤J) :
    fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J≤
      θ/(6*η₀*Cf^(J+1)) := by
  rw [fineParameter_source_formula hμ hL]
  have hj : (1:ℝ)≤J := by exact_mod_cast hJ
  have hs : (1:ℝ)≤Real.sqrt (2*(J:ℝ)) := Real.one_le_sqrt.mpr (by linarith)
  have hprod : (1:ℝ)≤((J:ℝ)+1)*Real.sqrt (2*(J:ℝ))*a := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) hs) ha
  apply div_le_div_of_nonneg_left hθ (by positivity)
  have hh := mul_le_mul_of_nonneg_left hprod (show 0≤6*η₀*Cf^(J+1) by positivity)
  nlinarith only [hh]

theorem fine_sqrt_depth_cancellation {θ μ L η₀ a Cf A : ℝ}
    (hθ : 0≤θ) (hμ : 0<μ) (hL : 0<L) (hη₀ : 0<η₀) (ha : 1≤a)
    (hCf : 0<Cf) (hA : 0≤A) (hbound : 4*A^2≤Cf) (J : ℕ) (hJ : 1≤J) :
    A^(J+1)*((J:ℝ)+1)*
      Real.sqrt (fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J)≤
        Real.sqrt (θ/(6*η₀)) := by
  let v := fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J
  have hv : 0≤v := by
    dsimp [v,fineParameter]
    have hd := normalCoefficient_pos hL hJ
    positivity
  have hvup : v≤θ/(6*η₀*Cf^(J+1)) := fine_parameter_simple_upper hθ hμ hL hη₀ ha hCf J hJ
  have hj : ((J:ℝ)+1)^2≤(4:ℝ)^(J+1) := by
    convert depth_sq_le_pow (J+1) using 1
    push_cast
    rfl
  have hab : (A^(J+1))^2*((J:ℝ)+1)^2≤Cf^(J+1) := by
    calc
      _≤(A^(J+1))^2*4^(J+1) := mul_le_mul_of_nonneg_left hj (sq_nonneg _)
      _=(4*A^2)^(J+1) := by rw [mul_pow]; ring
      _≤Cf^(J+1) := pow_le_pow_left₀ (by positivity) hbound _
  have hp := mul_le_mul hab hvup hv (pow_nonneg hCf.le _)
  have he : Cf^(J+1)*(θ/(6*η₀*Cf^(J+1)))=θ/(6*η₀) := by field_simp; ring
  rw [he] at hp
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt hv,Real.sq_sqrt (by positivity : 0≤θ/(6*η₀))]
  exact hp

end Bilevel.ChiExtensionCalibration
