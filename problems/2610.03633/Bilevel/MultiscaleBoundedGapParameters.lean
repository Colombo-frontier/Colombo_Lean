import Bilevel.MultiscaleMeanCore

/-! Explicit macro-free source parameters; all geometry comes from the
displayed scalar budgets and one actual orthonormal frame. -/
noncomputable section
namespace Bilevel.MultiscaleMean
set_option autoImplicit false

def innerParameters {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (n : ℕ) (μ L η β θ K : ℝ)
    (hμ : 0<μ) (hL : 0<L) (hη : 0≤η) (hη1 : η≤1)
    (hβ : 0<β) (hθ : 1≤θ) (hK : 1≤K) (U : ZeroChain.Space n →ₗᵢ[ℝ] E) :
    Parameters (E:=E) n where
  μ := μ
  L := L
  η := η
  β := β
  θ := θ
  c := 1/64
  ν := η*L/24
  R := K*β*Real.sqrt (n+1:ℕ)
  U := U
  μ_pos := hμ
  L_pos := hL
  η_nonneg := hη
  η_le_one := hη1
  β_pos := hβ
  θ_ge_one := hθ
  c_pos := by norm_num
  c_small := by norm_num
  ν_nonneg := by positivity
  β_le_R := by
    have hs : 1≤Real.sqrt (n+1:ℕ) := Real.one_le_sqrt.mpr (by norm_num)
    have hh := mul_le_mul hK hs (by norm_num : (0:ℝ)≤1) (by linarith : 0≤K)
    have hm := mul_le_mul_of_nonneg_right hh hβ.le
    nlinarith only [hm]

end Bilevel.MultiscaleMean
