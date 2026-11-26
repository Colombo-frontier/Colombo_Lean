import GradientHessian.CensoredLeafPhysicalOracle
import GradientHessian.FrontierOracleScalar
import GradientHessian.GeometricTerminalPlateaus
import GradientHessian.NodeFrontierBridge

/-! An actual censored first-height scalar. Child labels still share one
physical leaf coordinate. The scalar reads earlier children, the masked
current leaf, and precisely the disclosed outer-memory blocks. -/

noncomputable section
namespace GradientHessian.CensoredFirstHeight
open Classical InnerCoordinates JetLocality Filter
open scoped Topology

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

def lower : FirstHeight.SourceSpace Y E m →L[ℝ] Leaf.Space Y E (m+1) :=
  numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2)

def blockMap (i : Fin 8) : FirstHeight.SourceSpace Y E m →L[ℝ]
    EuclideanRegisters.Registers E (FirstHeight.depth (m+1)+2) :=
  Inner.taskProjection 8 (FirstHeight.depth (m+1)) i

def maskedSelf (d : FirstHeight.Data Y E m) (known : Fin 8 → Bool) (i : Fin 8)
    (Z : FirstHeight.SourceSpace Y E m) : ℝ :=
  Inner.block (if known i then d.outerDirections i else 0) (blockMap (Y := Y) (E := E) (m := m) i Z)

def active (d : FirstHeight.Data Y E m) (k : Fin 8) (mask : CensoredLeaf.Mask (m+1)) :
    FirstHeight.SourceSpace Y E m → ℝ :=
  CensoredLeaf.objective mask (d.A k) (d.b k,d.a k,d.innerDirections k) ∘ lower

def scalar (d : FirstHeight.Data Y E m) (k : Fin 8) (known : Fin 8 → Bool)
    (mask : CensoredLeaf.Mask (m+1)) : FirstHeight.SourceSpace Y E m → ℝ :=
  FrontierOracleScalar.scalar k (Leaf.publicQuadratic (m+1) ∘ lower) (FirstHeight.spacing m)
    (fun i => FirstHeight.children d i ∘ lower)
    (fun i => FirstHeight.childPorts d i ∘ lower) (maskedSelf d known)
    (fun i Z => Inner.input (d.outerDirections i) (blockMap (Y := Y) (E := E) (m := m) i Z))
    (fun i Z => Inner.ports d.outerDirections Z i) (active d k mask)

theorem lower_contDiff : ContDiff ℝ 3 (lower : FirstHeight.SourceSpace Y E m → Leaf.Space Y E (m+1)) :=
  (lower : FirstHeight.SourceSpace Y E m →L[ℝ] Leaf.Space Y E (m+1)).contDiff

theorem active_contDiff (d : FirstHeight.Data Y E m) (k : Fin 8) (mask : CensoredLeaf.Mask (m+1)) :
    ContDiff ℝ 3 (active d k mask) :=
  (CensoredLeaf.objective_contDiff (by omega) mask (d.A k) _).comp (lower_contDiff (Y := Y) (E := E) (m := m))

theorem maskedSelf_contDiff (d : FirstHeight.Data Y E m) (known : Fin 8 → Bool) (i : Fin 8) :
    ContDiff ℝ 3 (maskedSelf d known i) :=
  (Inner.block_contDiff _).comp (blockMap (Y := Y) (E := E) (m := m) i).contDiff

theorem scalar_contDiff (d : FirstHeight.Data Y E m) (k : Fin 8) (known : Fin 8 → Bool)
    (mask : CensoredLeaf.Mask (m+1)) : ContDiff ℝ 2 (scalar d k known mask) :=
  FrontierOracleScalar.scalar_contDiff k _ _ _ _ _ _ _ _
    (((Leaf.publicQuadratic_contDiff (m+1)).comp (lower_contDiff (Y := Y) (E := E) (m := m))).of_le (by decide))
    (fun i => ((FirstHeight.children_contDiff d i).comp (lower_contDiff (Y := Y) (E := E) (m := m))).of_le (by decide))
    (fun i => ((FirstHeight.childPorts_contDiff d i).comp (lower_contDiff (Y := Y) (E := E) (m := m))).of_le (by decide))
    (fun i => (maskedSelf_contDiff d known i).of_le (by decide))
    (fun i => ((Inner.input_contDiff (d.outerDirections i)).comp (blockMap (Y := Y) (E := E) (m := m) i).contDiff).of_le (by decide))
    (fun i => (Inner.ports_contDiff d.outerDirections i).of_le (by decide))
    ((active_contDiff d k mask).of_le (by decide))

theorem zero_block_public (U : EuclideanRegisters.Registers E (FirstHeight.depth (m+1)+2)) :
    Inner.block (0 : Fin (FirstHeight.depth (m+1)+2) → E) U=
      LatchChain.publicQuadratic (FirstHeight.depth (m+1)+1) (Inner.radius (FirstHeight.depth (m+1))) U := by
  apply MemoryMissJets.self_eq_public_of_zero_gates
  · exact fun j => (Inner.radius_pos _ j).ne'
  · intro j
    simp [LatchChain.u,LatchActivation.readout,Profiles.chi_zero (by norm_num : (0:ℝ)≤1/4)]

theorem maskedSelf_near (d : FirstHeight.Data Y E m) (known : Fin 8 → Bool) (i : Fin 8)
    (Z : FirstHeight.SourceSpace Y E m)
    (hmiss : known i=false → ∀ j,|LatchChain.u (Inner.radius (FirstHeight.depth (m+1)) j)
      (d.outerDirections i j) (blockMap (Y := Y) (E := E) (m := m) i Z j)|≤1/8) :
    (fun W => Inner.block (d.outerDirections i) (blockMap (Y := Y) (E := E) (m := m) i W)) =ᶠ[𝓝 Z] maskedSelf d known i := by
  cases hi : known i with
  | true =>
    apply Filter.Eventually.of_forall
    intro W
    simp only [maskedSelf,hi,if_true]
  | false =>
    have hn := MemoryMissJets.self_near_public (FirstHeight.depth (m+1)+1) (blockMap (Y := Y) (E := E) (m := m) i)
      (d.outerDirections i) (Inner.radius (FirstHeight.depth (m+1)))
      (fun j => (Inner.radius_pos _ j).ne') Z (hmiss hi)
    filter_upwards [hn] with W hW
    simpa only [maskedSelf,hi,Bool.false_eq_true,if_false] using hW.trans (zero_block_public _).symm

theorem richJet_eq (d : FirstHeight.Data Y E m) (k : Fin 8) (known : Fin 8 → Bool)
    (mask : CensoredLeaf.Mask (m+1)) (Z : FirstHeight.SourceSpace Y E m)
    (hparent : (fun W => Inner.ports d.outerDirections W k) =ᶠ[𝓝 Z] fun _ => 0)
    (hchild : FirstHeight.childPorts d k ∘ lower =ᶠ[𝓝 Z] fun _ => 0)
    (hself : ∀ i,known i=false → ∀ j,|LatchChain.u (Inner.radius (FirstHeight.depth (m+1)) j)
      (d.outerDirections i j) (blockMap (Y := Y) (E := E) (m := m) i Z j)|≤1/8)
    (hactive : richJet (FirstHeight.children d k ∘ lower) Z=richJet (active d k mask) Z) :
    richJet (FirstHeight.sourceNode d) Z=richJet (scalar d k known mask) Z := by
  rw [FirstHeight.sourceNode,NodeFrontierBridge.first_node_eq]
  exact FrontierOracleScalar.node_censored_richJet k _ _ _ _ _ _ _ _ _
    (((Leaf.publicQuadratic_contDiff (m+1)).comp (lower_contDiff (Y := Y) (E := E) (m := m))).of_le (by decide))
    (fun i => ((FirstHeight.children_contDiff d i).comp (lower_contDiff (Y := Y) (E := E) (m := m))).of_le (by decide))
    (fun i => ((FirstHeight.childPorts_contDiff d i).comp (lower_contDiff (Y := Y) (E := E) (m := m))).of_le (by decide))
    (fun i => (maskedSelf_contDiff d known i).of_le (by decide))
    (fun i => ((Inner.input_contDiff (d.outerDirections i)).comp (blockMap (Y := Y) (E := E) (m := m) i).contDiff).of_le (by decide))
    (fun i => (Inner.ports_contDiff d.outerDirections i).of_le (by decide))
    ((active_contDiff d k mask).of_le (by decide)) Z hparent hchild
    (fun i => maskedSelf_near d known i Z (hself i)) hactive

end GradientHessian.CensoredFirstHeight
