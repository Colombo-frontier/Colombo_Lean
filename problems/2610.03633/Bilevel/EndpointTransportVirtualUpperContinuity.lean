import Bilevel.EndpointTransportUpperPrefix
import Bilevel.EndpointTransportVirtualOuterContinuity
import Bilevel.ChiVirtualUpperContinuity

/-! Joint continuity of the complete physical upper scalar using only old
macro, ordinary, and target data. The new-source array is not consulted. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiOuter
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem physicalUpperOrdinaryData_continuous {m n D : ℕ} (M : Node E) (G : Geometry (Block D)) :
    Continuous (fun z : PhysicalPrefixData M G n × PhysicalBase E m n D =>
      ((z.1.1,z.1.2.1),baseOrdinaryCoordinates m n D z.2)) :=
  (continuous_fst.fst.prodMk continuous_fst.snd.fst).prodMk
    ((baseOrdinaryCoordinates (E:=E) m n D).continuous.comp continuous_snd)

theorem physicalUpperCarrierData_continuous {m n D : ℕ} (M : Node E) (G : Geometry (Block D)) :
    Continuous (fun z : PhysicalPrefixData M G n × PhysicalBase E m n D =>
      ((z.1.2.1,((0 : EndpointColumnData G n),z.1.2.2.2)),z.2.snd)) :=
  (continuous_fst.snd.fst.prodMk (continuous_const.prodMk continuous_fst.snd.snd.snd)).prodMk
    ((jointSndLinear (A:=E) (B:=HybridTangent (Blocks m (Block D)) n D)).continuous.comp continuous_snd)

theorem prefixPhysicalUpperBase_continuous {m n D : ℕ} (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (J : ℕ) (ρ R : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ) :
    Continuous (fun z : PhysicalPrefixData M G n × PhysicalBase E m n D =>
      prefixPhysicalUpperBase m M ν G J ρ R rM r z.1.1 z.1.2.1 z.1.2.2.2 z.2) := by
  have hm := (virtualMacroValue_continuous M ν rM).comp
    (physicalMacroData_continuous (J:=m) (n:=n) M G)
  have hr := (virtualOuterReleaseCorrection_continuous m M G rM r).comp
    (physicalUpperOrdinaryData_continuous (m:=m) (n:=n) M G)
  have hs : Continuous (fun z : PhysicalPrefixData M G n × PhysicalBase E m n D =>
      ∑ i : Fin (M.n+1),virtualOuterSelector M rM z.1.1 i z.2.fst*
        virtualPhysicalCarrier G r r z.1.2.1 (fun _ _ _ => 0) z.1.2.2.2 J 0 [i.val] 0 z.2.snd) := by
    apply continuous_finset_sum
    intro i _
    have hi := (virtualOuterSelector_continuous M rM i).comp
      (physicalMacroData_continuous (J:=m) (n:=n) M G)
    have hc := (virtualPhysicalCarrier_continuous (m:=m) (n:=n) G r r J 0 [i.val] 0).comp
      (physicalUpperCarrierData_continuous (m:=m) (n:=n) M G)
    exact hi.mul hc
  have hb := (baseRadial_contDiff (E:=E) (F:=Block D) m ρ R).continuous.comp
    ((baseOrdinaryCoordinates (E:=E) m n D).continuous.comp
      (continuous_snd : Continuous (Prod.snd : PhysicalPrefixData M G n × PhysicalBase E m n D → _)))
  exact hm.add ((hr.add hs).add hb)

def statePhysicalUpperBase {m n D : ℕ} (M : Node E) (ν : ℝ) (G : Geometry (Block D))
    (J : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ)
    (p : PhysicalPrefixState M G n) : PhysicalBase E m n D → ℝ :=
  prefixPhysicalUpperBase m M ν G J ρ R (rM p.1) (r p.1) p.2.1 p.2.2.1 p.2.2.2.2

theorem statePhysicalUpperBase_continuous {m n D : ℕ} (M : Node E) (ν : ℝ) (G : Geometry (Block D))
    (J : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) :
    Continuous (Function.uncurry (statePhysicalUpperBase (m:=m) (n:=n) M ν G J ρ R rM r)) := by
  have h : Continuous (fun p : ℕ × (PhysicalPrefixData M G n × PhysicalBase E m n D) =>
      prefixPhysicalUpperBase m M ν G J ρ R (rM p.1) (r p.1)
        p.2.1.1 p.2.1.2.1 p.2.1.2.2.2 p.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun q =>
      prefixPhysicalUpperBase_continuous M ν G J ρ R (rM q) (r q))
  have hp := h.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  exact hp

end Bilevel.EndpointTransportResponse
