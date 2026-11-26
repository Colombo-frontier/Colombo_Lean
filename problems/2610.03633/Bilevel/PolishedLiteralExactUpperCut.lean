import Bilevel.PolishedLiteralActiveCut
import Bilevel.PolishedLiteralUpperPrimitive

/-! Exact upper reply uses the pre-activation disclosed prefixes. Terminal
release and positive receiver remain flat in every incomplete block. -/
noncomputable section
set_option maxHeartbeats 1500000
open scoped BigOperators Topology
open Filter
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ChiPrefixEvaluation PrimitiveGeometry RadialWrapper

theorem retain_full {n s : ℕ} (hs : n+1≤s) (z : Space n) : retain n s z=z := by
  ext k
  rw [retain_apply,if_pos (by omega)]

namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def cutRelease (counts : Fin (P.macroNode.n+1) → ℕ) (i : Fin (P.macroNode.n+1)) (u : U) : ℝ :=
  releaseGate (P.cutMicroCoordinates counts i u (Fin.last P.n)/P.macroNode.width)

def exactUpperCutBase (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (z : Joint X U) : ℝ :=
  closedChain P.macroNode.n P.macroNode.ell P.macroNode.width (fun i => P.cutRelease counts i z.snd)
    (P.cutMacroCoordinates r z.fst)+bowl P.macroRadial P.macroNode.radius z.fst+bowl P.ν P.radius z.snd+
    ∑ i : Fin (P.macroNode.n+1),P.cutSelector r i z.fst*
      microClosedCarrier P.n P.L P.β P.receiver P.ν P.force P.macroNode.width (P.cutMicroCoordinates counts i z.snd)

def exactUpperCut (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  P.exactUpperCutBase r counts (pack q.fst.fst q.snd.fst)+P.L*q.snd.snd

theorem upperBase_closed_formula (z : Joint X U) :
    P.upperBase z=closedChain P.macroNode.n P.macroNode.ell P.macroNode.width
      (fun i => P.microRelease i z.snd) (P.macroNode.coordinates z.fst)+
      bowl P.macroRadial P.macroNode.radius z.fst+bowl P.ν P.radius z.snd+
      ∑ i : Fin (P.macroNode.n+1),wrappedSelector P.macroNode i z.fst*
        microClosedCarrier P.n P.L P.β P.receiver P.ν P.force P.macroNode.width (P.coordinates i z.snd) := by
  have hc (i : Fin (P.macroNode.n+1)) : P.microCore i z.snd-P.microResidual i z.snd=
      microClosedCarrier P.n P.L P.β P.receiver P.ν P.force P.macroNode.width (P.coordinates i z.snd) := by
    unfold microCore microResidual terminal microClosedCarrier microCarrier
    ring
  have hm : closedChain P.macroNode.n P.macroNode.ell P.macroNode.width
      (fun i => P.microRelease i z.snd) (P.macroNode.coordinates z.fst)=
      chain P.macroNode.n P.macroNode.ell P.macroNode.width (P.macroNode.coordinates z.fst)+
        ∑ i : Fin (P.macroNode.n+1),wrappedResidual P.macroNode i z.fst*(P.microRelease i z.snd-1) := by
    simp only [closedChain,closedValue,chain,ZeroChainResidualScaled.scaled,wrappedResidual,mul_add,Finset.mul_sum]
    ring
  unfold upperBase macroCarrier
  simp_rw [hc]
  rw [hm]
  change (chain P.macroNode.n P.macroNode.ell P.macroNode.width (P.macroNode.coordinates z.fst)+
    bowl P.macroRadial P.macroNode.radius z.fst)-_+_+_+_=_
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
  ring

omit [CompleteSpace X] in
theorem cutRelease_eq (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hτb : τ≤P.macroNode.width) (i : Fin (P.macroNode.n+1)) (u : U)
    (hu : ∀ k : Fin (P.n+1),counts i≤k.val → |P.coordinates i u k|≤τ) :
    P.microRelease i u=P.cutRelease counts i u := by
  by_cases hc : P.n+1≤counts i
  · simp only [microRelease,terminal,cutRelease,cutMicroCoordinates,retain_full hc]
  · have hci : counts i≤P.n := by omega
    have hs : P.coordinates i u (Fin.last P.n)≤P.macroNode.width :=
      (abs_le.mp (hu _ hci)).2.trans hτb
    have ht : retain P.n (counts i) (P.coordinates i u) (Fin.last P.n)=0 := by
      rw [retain_apply,if_neg (by simpa using not_lt.mpr hci)]
    simp only [microRelease,terminal,cutRelease,cutMicroCoordinates,ht,zero_div,
      releaseGate_zero ((div_le_iff₀ hb).mpr (by simpa using hs)),releaseGate_zero (by norm_num : (0:ℝ)≤1)]

theorem exactUpperCutBase_value (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτβ : τ≤P.β/4) (hτb : τ≤P.macroNode.width)
    (hcounts : ∀ i : Fin (P.macroNode.n+1),r ≤ i.val → counts i≤P.n) (z : Joint X U)
    (hx : ∀ k : Fin (P.macroNode.n+1),r≤k.val → |P.macroNode.coordinates z.fst k|≤P.macroNode.width/4)
    (hu : ∀ (i : Fin (P.macroNode.n+1)) (k : Fin (P.n+1)),counts i≤k.val → |P.coordinates i z.snd k|≤τ) :
    P.upperBase z=P.exactUpperCutBase r counts z := by
  have hQ (i : Fin (P.macroNode.n+1)) := P.cutRelease_eq counts τ hb hτb i z.snd (hu i)
  have hQfuture (i : Fin (P.macroNode.n+1)) (hi : r ≤ i.val) : P.microRelease i z.snd=0 := by
    unfold microRelease terminal
    apply releaseGate_zero
    apply (div_le_iff₀ hb).mpr
    simpa only [one_mul] using (abs_le.mp (hu i (Fin.last P.n) (hcounts i hi))).2.trans hτb
  have hmacro := closedChain_prefix_value P.macroNode.n r P.macroNode.ell P.macroNode.width hb
    (fun i => P.microRelease i z.snd) hQfuture (P.macroNode.coordinates z.fst) hx
  have hcarrier (i : Fin (P.macroNode.n+1)) :
      microClosedCarrier P.n P.L P.β P.receiver P.ν P.force P.macroNode.width (P.coordinates i z.snd)=
      microClosedCarrier P.n P.L P.β P.receiver P.ν P.force P.macroNode.width (P.cutMicroCoordinates counts i z.snd) := by
    by_cases hc : P.n+1≤counts i
    · simp only [cutMicroCoordinates,retain_full hc]
    · exact microClosedCarrier_prefix_value P.n (counts i) (by omega) P.L P.β P.receiver P.ν P.force
        P.macroNode.width hβ (P.coordinates i z.snd) (fun k hk => (hu i k hk).trans hτβ)
  rw [P.upperBase_closed_formula,hmacro]
  unfold exactUpperCutBase cutMacroCoordinates
  have hq : (fun i => P.microRelease i z.snd)=(fun i => P.cutRelease counts i z.snd) := funext hQ
  rw [hq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [P.cutSelector_eq r hb z.fst hx i,hcarrier i]

theorem exactUpperCut_gradient (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτβ : τ≤P.β/4) (hτb : τ≤P.macroNode.width)
    (hcounts : ∀ i : Fin (P.macroNode.n+1),r ≤ i.val → counts i≤P.n)
    (q : FullMeanSpace (X:=X) (U:=U)) (hq : P.BlindBox r counts τ q) :
    gradient P.upperJoint q=gradient (P.exactUpperCut r counts) q := by
  have he : P.upperJoint=ᶠ[𝓝 q] P.exactUpperCut r counts := by
    filter_upwards [(P.blindBox_isOpen r counts τ).mem_nhds hq] with z hz
    change P.upperBase (pack z.fst.fst z.snd.fst)+P.L*z.snd.snd=
      P.exactUpperCutBase r counts (pack z.fst.fst z.snd.fst)+P.L*z.snd.snd
    rw [P.exactUpperCutBase_value r counts τ hb hβ hτβ hτb hcounts (pack z.fst.fst z.snd.fst)
      (fun k hk => (hz.1 k hk).le) (fun i k hk => (hz.2 i k hk).le)]
  simp only [gradient,he.fderiv_eq]

end Parameters
end Bilevel.PolishedLiteral
