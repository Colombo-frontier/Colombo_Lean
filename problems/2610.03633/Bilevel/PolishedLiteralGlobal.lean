import Bilevel.PolishedLiteralCalibration
import Bilevel.PolishedLiteralFormulas

/-! The actual macro slice and the literal stop-or-descend alternative.
All selected terms use the manuscript's fixed exponential gate. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain ZeroChainPotential RadialWrapper
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

theorem meanBase_x_slice (x : X) (u : U) :
    P.meanBase (pack x u)=attachment P.macroNode P.macroRadial
      (fun i => P.microRelease i u) (fun i => P.microCore i u) x+bowl P.ν P.radius u := by
  change P.macroCarrier x+bowl P.ν P.radius u+
    (∑ i,wrappedSelector P.macroNode i x*P.microCore i u)+
      (∑ i,wrappedResidual P.macroNode i x*P.microRelease i u)=_
  unfold macroCarrier attachment
  dsimp only
  simp only [sub_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,one_mul]
  simp only [mul_comm]
  ring

omit [CompleteSpace U] in
theorem attachment_contDiff (Q W : Fin (P.macroNode.n+1) → ℝ) (k : ℕ) :
    ContDiff ℝ k (attachment P.macroNode P.macroRadial Q W) :=
  (macro_contDiff P.macroNode P.macroRadial k).add (ContDiff.sum (fun i _ =>
    (contDiff_const.mul (wrappedResidual_contDiff P.macroNode i k)).add
      (contDiff_const.mul (wrappedSelector_contDiff P.macroNode i k))))

theorem meanBase_x_fderiv (x : X) (u : U) :
    fderiv ℝ (fun y => P.meanBase (pack y u)) x=
      fderiv ℝ (attachment P.macroNode P.macroRadial
        (fun i => P.microRelease i u) (fun i => P.microCore i u)) x := by
  have he : (fun y => P.meanBase (pack y u))=fun y =>
      attachment P.macroNode P.macroRadial (fun i => P.microRelease i u)
        (fun i => P.microCore i u) y+bowl P.ν P.radius u := funext (fun y => P.meanBase_x_slice y u)
  rw [he]
  have hd := ((P.attachment_contDiff (fun i => P.microRelease i u) (fun i => P.microCore i u) 1).differentiable (by norm_num) x).hasFDerivAt
  exact (hd.add_const _).fderiv

/-- Source-faithful stop-or-descend at the actual finite mean, with the
payload bound supplied separately by the explicit value-budget theorem. -/
theorem meanBase_stop_or_descend (Cs Cr δ : ℝ) (hCs : 0≤Cs) (hCr : 0≤Cr) (hδ : 0≤δ)
    (hδsmall : δ≤releaseTolerance (literalControl (Cr+Cs)))
    (hL : 0≤P.macroNode.ell) (hb : 0<P.macroNode.width) (hR : 0<P.macroNode.radius)
    (x : X) (u : U)
    (hs : ∀ i,‖fderiv ℝ (wrappedSelector P.macroNode i) x‖≤
      (Cs/P.macroNode.width)*Real.sqrt (wrappedSelector P.macroNode i x))
    (hr : ∀ i,‖fderiv ℝ (wrappedResidual P.macroNode i) x‖≤
      Cr*(P.macroNode.ell*P.macroNode.width)*Real.sqrt (wrappedSelector P.macroNode i x))
    (hW : ∀ i,|P.microCore i u|≤δ*(P.macroNode.ell*P.macroNode.width^2))
    (hmacro : (P.macroNode.ell*P.macroNode.width)/2≤
      ‖fderiv ℝ (macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial
        P.macroNode.radius P.macroNode.frame) x‖) :
    (P.macroNode.ell*P.macroNode.width)/4≤‖fderiv ℝ (fun y => P.meanBase (pack y u)) x‖ ∨
      ∃ i : Fin (P.macroNode.n+1),
        descentThreshold (literalControl (Cr+Cs))<wrappedSelector P.macroNode i x ∧ P.microRelease i u<1 := by
  rw [P.meanBase_x_fderiv]
  apply attachment_stop_or_descend P.macroNode P.macroRadial
    (fun i => P.microRelease i u) (fun i => P.microCore i u) x hCs hCr hδ hδsmall hL hb hR
    (fun i => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩) hs hr hW hmacro

end Parameters
end Bilevel.PolishedLiteral
