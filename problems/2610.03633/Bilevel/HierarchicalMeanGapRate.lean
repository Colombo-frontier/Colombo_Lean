import Bilevel.HierarchicalMeanGap

/-! Source-scale arithmetic for the literal initial gap. This keeps the
macro stage count linear and has no ambient-dimension dependence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Bilevel.HierarchicalMean.Parameters
open ChiBoundedChain
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (P : Parameters (X:=X) (U:=U))

omit [CompleteSpace X] [CompleteSpace U] in
theorem gapBudget_rate (Cm Cν Cg : ℝ) (hCm : 0≤Cm) (hCν : 0≤Cν) (hCg : 0≤Cg)
    (hL : 0≤P.L) (hA : 0≤P.receiver) (hb : 0≤P.macroNode.width)
    (hℓ : P.macroNode.ell≤P.L)
    (hn : ((P.n:ℝ)+1)*P.β^2≤Cm*P.macroNode.width^2)
    (hν : P.ν≤Cν*P.L) (hg : P.force≤Cg*P.L*P.macroNode.width) :
    P.gapBudget≤(gaussianBound*(1+Cm)+3*P.receiver*(3*Cν+Cg))*
      ((P.macroNode.n:ℝ)+1)*P.L*P.macroNode.width^2 := by
  have hG : 0≤gaussianBound := by unfold gaussianBound; positivity
  have hS : 1≤(P.macroNode.n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) P.macroNode.n; linarith
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hℓ (sq_nonneg P.macroNode.width))
    (show 0≤((P.macroNode.n:ℝ)+1)*gaussianBound by positivity)
  have hi := mul_le_mul_of_nonneg_left hn (mul_nonneg hG hL)
  have hν' := mul_le_mul_of_nonneg_right hν (show 0≤3*P.macroNode.width by positivity)
  have hsum : 3*P.ν*P.macroNode.width+P.force≤(3*Cν+Cg)*P.L*P.macroNode.width := by
    nlinarith only [hν',hg]
  have hd := mul_le_mul_of_nonneg_left hsum
    (show 0≤P.receiver*(3*P.macroNode.width) by positivity)
  have hB : 0≤(gaussianBound*Cm+3*P.receiver*(3*Cν+Cg))*P.L*P.macroNode.width^2 := by positivity
  have hs := mul_le_mul_of_nonneg_right hS hB
  dsimp only [gapBudget,microBudget]
  nlinarith only [hm,hi,hd,hs]

theorem source_gap_rate (κ Cm ζ Cg : ℝ) (hκ : 1≤κ)
    (hCm : 0≤Cm) (hζ : 0≤ζ) (hCg : 0≤Cg)
    (hL : 0≤P.L) (hA : 0≤P.receiver) (hβ : 0<P.β)
    (hscale : κ*P.β=P.macroNode.width) (hℓ : P.macroNode.ell=P.L)
    (hn : (P.n:ℝ)+1≤Cm*κ^2)
    (hν : P.ν=ζ*P.L) (hg : P.force=Cg*P.L*P.β)
    (hmacro : 0≤P.macroRadial) :
    P.objective κ 0-sInf (Set.range (P.objective κ))≤
      (gaussianBound*(1+Cm)+3*P.receiver*(3*ζ+Cg))*
        ((P.macroNode.n:ℝ)+1)*P.L*P.macroNode.width^2 := by
  have hκ0 : 0<κ := lt_of_lt_of_le zero_lt_one hκ
  have hb : 0<P.macroNode.width := hscale ▸ mul_pos hκ0 hβ
  have hβb : P.β≤P.macroNode.width := by
    rw [← hscale]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hκ hβ.le
  have hnn : ((P.n:ℝ)+1)*P.β^2≤Cm*P.macroNode.width^2 := by
    have hh := mul_le_mul_of_nonneg_right hn (sq_nonneg P.β)
    rw [← hscale,mul_pow]
    nlinarith only [hh]
  apply (P.objective_gap_to_infimum κ (by simpa only [hℓ] using hL) hL hA
    (by rw [hν];positivity) hmacro (by rw [hg];positivity) hβ hb).trans
  apply P.gapBudget_rate Cm ζ Cg hCm hζ hCg hL hA hb.le hℓ.le hnn hν.le
  rw [hg]
  exact mul_le_mul_of_nonneg_left hβb (mul_nonneg hCg hL)

end Bilevel.HierarchicalMean.Parameters
