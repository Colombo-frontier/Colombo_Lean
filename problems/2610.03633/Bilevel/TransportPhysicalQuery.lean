import Bilevel.TransportVirtualHybridReply
import Bilevel.TransportProgramController
import Bilevel.ChiCarrierJoint

/-! The positive-depth full query exposes its macro and ordinary lower
points to the auxiliary process and its physical lower point to a single
frozen network batch. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open PrimitiveGeometry PartialLegendre EndpointTransportResponse TransportRound ChiRecursive ChiCarrier
set_option autoImplicit false
set_option maxHeartbeats 800000

abbrev PhysicalOutput (J D : ℕ) := HybridOuter (Block D) (Blocks J (Block D)) D
abbrev PhysicalQuery (J n D s : ℕ) := HybridQuery (Block D) (Blocks J (Block D)) (ChiExtension.Normals s) n D
abbrev PhysicalReply (J n D s : ℕ) := PhysicalQuery J n D s × PhysicalQuery J n D s

def physicalNetworkQueries {J n D s : ℕ} (w : PhysicalQuery J n D s) : Queries (n+1) D 1 :=
  fun v _ => w.snd.fst.snd v

def physicalAuxiliaryQueries {J n D s : ℕ} (w : PhysicalQuery J n D s) : Fin (J+1) → Block D :=
  Fin.cases w.fst.fst.fst (fun j => block J j.val w.snd.fst.fst)

def physicalNetworkOutput {J n D : ℕ} (x : PhysicalOutput J D) : Queries (n+1) D 1 :=
  fun _ _ => x.snd

def physicalAuxiliaryOutput {J D : ℕ} (x : PhysicalOutput J D) : Block D := x.fst.fst

theorem physicalNetworkQueries_physical {J n D s : ℕ} (w : PhysicalQuery J n D s) :
    physical (fun v => physicalNetworkQueries w v 0)=w.snd.fst.snd := rfl

theorem physicalAuxiliaryQueries_macro {J n D s : ℕ} (w : PhysicalQuery J n D s) :
    physicalAuxiliaryQueries w 0=w.fst.fst.fst := rfl

theorem physicalAuxiliaryQueries_ordinary {J n D s : ℕ} (w : PhysicalQuery J n D s) (j : Fin J) :
    physicalAuxiliaryQueries w j.succ=block J j.val w.snd.fst.fst := rfl

section MeasurableQuery
variable {J n D s : ℕ} [MeasurableSpace (PhysicalQuery J n D s)] [BorelSpace (PhysicalQuery J n D s)]

theorem physicalNetworkQueries_measurable : Measurable (physicalNetworkQueries (J:=J) (n:=n) (D:=D) (s:=s)) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro a
  let Y : PhysicalQuery J n D s →L[ℝ] HybridVariables (Blocks J (Block D)) (ChiExtension.Normals s) n D := jointSndLinear
  let T : HybridVariables (Blocks J (Block D)) (ChiExtension.Normals s) n D →L[ℝ]
      HybridTangent (Blocks J (Block D)) n D := jointFstLinear
  let V : HybridTangent (Blocks J (Block D)) n D →L[ℝ] Physical n D := jointSndLinear
  let L : PhysicalQuery J n D s →L[ℝ] Physical n D := V.comp (T.comp Y)
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : EndpointTransportMatrix.Index n => Block D) v).continuous.comp L.continuous
  exact h.measurable

theorem physicalAuxiliaryQueries_measurable : Measurable (physicalAuxiliaryQueries (J:=J) (n:=n) (D:=D) (s:=s)) := by
  apply measurable_pi_lambda
  intro a
  refine Fin.cases ?_ (fun j => ?_) a
  · let X : PhysicalQuery J n D s →L[ℝ] PhysicalOutput J D := jointFstLinear
    let B : PhysicalOutput J D →L[ℝ] Joint (Block D) (Blocks J (Block D)) := jointFstLinear
    let M : Joint (Block D) (Blocks J (Block D)) →L[ℝ] Block D := jointFstLinear
    let L : PhysicalQuery J n D s →L[ℝ] Block D := M.comp (B.comp X)
    exact L.continuous.measurable
  · let Y : PhysicalQuery J n D s →L[ℝ] HybridVariables (Blocks J (Block D)) (ChiExtension.Normals s) n D := jointSndLinear
    let T : HybridVariables (Blocks J (Block D)) (ChiExtension.Normals s) n D →L[ℝ]
        HybridTangent (Blocks J (Block D)) n D := jointFstLinear
    let V : HybridTangent (Blocks J (Block D)) n D →L[ℝ] Blocks J (Block D) := jointFstLinear
    let L : PhysicalQuery J n D s →L[ℝ] Blocks J (Block D) := V.comp (T.comp Y)
    have h := (block J j.val).continuous.comp L.continuous
    exact h.measurable
end MeasurableQuery

section MeasurableOutput
variable {J n D : ℕ} [MeasurableSpace (PhysicalOutput J D)] [BorelSpace (PhysicalOutput J D)]

theorem physicalNetworkOutput_measurable : Measurable (physicalNetworkOutput (J:=J) (n:=n) (D:=D)) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro a
  exact (jointSndLinear (A:=Joint (Block D) (Blocks J (Block D))) (B:=Block D)).continuous.measurable

theorem physicalAuxiliaryOutput_measurable : Measurable (physicalAuxiliaryOutput (J:=J) (D:=D)) := by
  let L : PhysicalOutput J D →L[ℝ] Block D := jointFstLinear.comp jointFstLinear
  exact L.continuous.measurable
end MeasurableOutput
end Bilevel.TransportHierarchy
