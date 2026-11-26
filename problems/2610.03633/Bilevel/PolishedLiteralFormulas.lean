import Bilevel.PolishedLiteralResidual
import Bilevel.PolishedLiteralWrappedSelectors
import Bilevel.PolishedLiteralJointMean

/-! Literal finite macro--micro additive mean. The macro and micro chains
are one-sided, the micro residual has the global centering constant, and the
receiver and release gate are actual smooth profiles. No lower response or
selector-dependent derivative equality is postulated. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain RadialWrapper
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

structure Parameters where
  macroNode : Node X
  macroRadial : ℝ
  n : ℕ
  μ : ℝ
  L : ℝ
  β : ℝ
  radius : ℝ
  ν : ℝ
  receiver : ℝ
  force : ℝ
  frames : Fin (macroNode.n+1) → Space n →ₗᵢ[ℝ] U
  J : ℕ
  δ : ℕ → ℝ
  w : ℕ → ℝ
  w_pos : ∀ j,j≤J → 0<w j

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

def coordinates (i : Fin (P.macroNode.n+1)) : U → Space P.n :=
  WrappedChain.coordinates P.n P.radius (P.frames i)

def microResidual (i : Fin (P.macroNode.n+1)) (u : U) : ℝ :=
  residual P.n P.L P.β (P.coordinates i u)

def microPiece (i : Fin (P.macroNode.n+1)) (j : ℕ) (u : U) : ℝ :=
  piece P.n P.J P.L P.β P.δ j (P.coordinates i u)

def terminal (i : Fin (P.macroNode.n+1)) (u : U) : ℝ :=
  P.coordinates i u (Fin.last P.n)

def microCore (i : Fin (P.macroNode.n+1)) (u : U) : ℝ :=
  PolishedLiteral.chain P.n P.L P.β (P.coordinates i u)+
    positiveReceiver P.receiver P.ν P.force P.β P.macroNode.width (P.terminal i u)

def microRelease (i : Fin (P.macroNode.n+1)) (u : U) : ℝ :=
  releaseGate (P.terminal i u/P.macroNode.width)

def macroCarrier (x : X) : ℝ :=
  PolishedLiteral.macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial
    P.macroNode.radius P.macroNode.frame x-
      ∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedResidual P.macroNode i x

def selectedResidual (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedSelector P.macroNode i z.fst*P.microResidual i z.snd

def selectedPiece (j : ℕ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedSelector P.macroNode i z.fst*P.microPiece i j z.snd

def upperBase (z : Joint X U) : ℝ :=
  P.macroCarrier z.fst+bowl P.ν P.radius z.snd+
    (∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedSelector P.macroNode i z.fst*
      (P.microCore i z.snd-P.microResidual i z.snd))+
    ∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedResidual P.macroNode i z.fst*P.microRelease i z.snd

def meanBase (z : Joint X U) : ℝ :=
  P.macroCarrier z.fst+bowl P.ν P.radius z.snd+
    (∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedSelector P.macroNode i z.fst*P.microCore i z.snd)+
    ∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedResidual P.macroNode i z.fst*P.microRelease i z.snd

omit [CompleteSpace X] in
theorem coordinates_contDiff (i : Fin (P.macroNode.n+1)) : ContDiff ℝ 3 (P.coordinates i) :=
  ZeroChainWrappedResidual.coordinates_contDiff P.n P.radius (P.frames i)

omit [CompleteSpace X] in
theorem microResidual_contDiff (i : Fin (P.macroNode.n+1)) : ContDiff ℝ 3 (P.microResidual i) :=
  (residual_contDiff P.n 3 P.L P.β).comp (P.coordinates_contDiff i)

omit [CompleteSpace X] in
theorem microPiece_contDiff (i : Fin (P.macroNode.n+1)) (j : ℕ) : ContDiff ℝ 3 (P.microPiece i j) :=
  (piece_contDiff P.n P.J P.L P.β P.δ j).comp (P.coordinates_contDiff i)

omit [CompleteSpace X] in
theorem terminal_contDiff (i : Fin (P.macroNode.n+1)) : ContDiff ℝ 3 (P.terminal i) :=
  (EuclideanSpace.proj (𝕜:=ℝ) (Fin.last P.n)).contDiff.comp (P.coordinates_contDiff i)

omit [CompleteSpace X] in
theorem microCore_contDiff (i : Fin (P.macroNode.n+1)) : ContDiff ℝ 3 (P.microCore i) :=
  ((PolishedLiteral.chain_contDiff P.n P.L P.β 3).comp (P.coordinates_contDiff i)).add
    ((positiveReceiver_contDiff P.receiver P.ν P.force P.β P.macroNode.width 3).comp (P.terminal_contDiff i))

omit [CompleteSpace X] in
theorem microRelease_contDiff (i : Fin (P.macroNode.n+1)) : ContDiff ℝ 3 (P.microRelease i) :=
  releaseGate_contDiff.comp ((P.terminal_contDiff i).div_const P.macroNode.width)

omit [CompleteSpace U] in
theorem macroCarrier_contDiff : ContDiff ℝ 3 P.macroCarrier :=
  (PolishedLiteral.macro_contDiff P.macroNode P.macroRadial 3).sub
    (ContDiff.sum (fun i _ => PolishedLiteral.wrappedResidual_contDiff P.macroNode i 3))

omit [CompleteSpace X] [CompleteSpace U] in
private theorem fst_contDiff : ContDiff ℝ 3 (fun z : Joint X U => z.fst) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ X U).contDiff.fst

omit [CompleteSpace X] [CompleteSpace U] in
private theorem snd_contDiff : ContDiff ℝ 3 (fun z : Joint X U => z.snd) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ X U).contDiff.snd

theorem selectedResidual_contDiff : ContDiff ℝ 3 P.selectedResidual :=
  ContDiff.sum (fun i _ => ((PolishedLiteral.wrappedSelector_contDiff P.macroNode i 3).comp fst_contDiff).mul
    ((P.microResidual_contDiff i).comp snd_contDiff))

theorem selectedPiece_contDiff (j : ℕ) : ContDiff ℝ 3 (P.selectedPiece j) :=
  ContDiff.sum (fun i _ => ((PolishedLiteral.wrappedSelector_contDiff P.macroNode i 3).comp fst_contDiff).mul
    ((P.microPiece_contDiff i j).comp snd_contDiff))

theorem upperBase_contDiff : ContDiff ℝ 3 P.upperBase :=
  (((P.macroCarrier_contDiff.comp fst_contDiff).add
    ((full_bowl_contDiff P.ν P.radius 3).comp snd_contDiff)).add
      (ContDiff.sum (fun i _ => ((PolishedLiteral.wrappedSelector_contDiff P.macroNode i 3).comp fst_contDiff).mul
        (((P.microCore_contDiff i).sub (P.microResidual_contDiff i)).comp snd_contDiff)))).add
    (ContDiff.sum (fun i _ => ((PolishedLiteral.wrappedResidual_contDiff P.macroNode i 3).comp fst_contDiff).mul
      ((P.microRelease_contDiff i).comp snd_contDiff)))

theorem decomposition (z : Joint X U) :
    (∑ j ∈ Finset.range (P.J+1),P.selectedPiece j z)=P.selectedResidual z := by
  unfold selectedPiece selectedResidual microPiece microResidual
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum,sum_piece]

def data : PolishedLiteralJointMean.Data (X:=X) (U:=U) where
  μ := P.μ
  L := P.L
  J := P.J
  r := P.selectedResidual
  A := P.upperBase
  e := P.selectedPiece
  w := P.w
  r_smooth := P.selectedResidual_contDiff
  A_smooth := P.upperBase_contDiff
  e_smooth := P.selectedPiece_contDiff
  w_pos := P.w_pos
  decomposition := P.decomposition

theorem exact_cancellation (z : Joint X U) : P.upperBase z+P.selectedResidual z=P.meanBase z := by
  simp only [upperBase,selectedResidual,meanBase,mul_sub,Finset.sum_sub_distrib]
  ring

theorem exact_hyperobjective (hL : P.L≠0) (x : X) (v : U) :
    PolishedLiteralJointMean.upper P.data x v (PolishedLiteralJointMean.response P.data x v)=
      P.meanBase (pack x ((P.L/P.μ) • v)) := by
  rw [PolishedLiteralJointMean.hyperobjective_substitution P.data hL]
  exact P.exact_cancellation _

theorem selectedResidual_zero : P.selectedResidual 0=0 := by
  have hc (i : Fin (P.macroNode.n+1)) : P.coordinates i 0=0 := by
    simp [coordinates,WrappedChain.coordinates,compress]
  simp only [selectedResidual,show (0:Joint X U).snd=0 from rfl,microResidual,hc,
    residual_zero,mul_zero,Finset.sum_const_zero]

theorem exact_initialization : PolishedLiteralJointMean.response P.data (0:X) (0:U)=0 :=
  PolishedLiteralJointMean.response_zero P.data P.selectedResidual_zero

end Parameters
end Bilevel.PolishedLiteral
