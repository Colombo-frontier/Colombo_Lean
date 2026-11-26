import GradientHessian.CensoredFirstHeight

/-! A finite recursive disclosure plan and its literal scalar on the shared
physical hierarchy. Geometry below consists only of numerical support and
memory misses. It contains no claimed simulated reply or jet equality. -/

noncomputable section
namespace GradientHessian.CensoredHierarchy
universe u
open Classical HigherHierarchy InnerCoordinates JetLocality Filter
open scoped Topology

def Plan (m : ℕ) : ℕ → Type
  | 0 => Fin 8 × (Fin 8 → Bool) × CensoredLeaf.Mask (m+1)
  | t+1 => Fin 8 × (Fin 8 → Bool) × Plan m t

def selectedLeaf (m : ℕ) : (t : ℕ) → Plan m t → LeafSlot t
  | 0,p => p.1
  | t+1,p => (p.1,selectedLeaf m t p.2.2)

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

structure BaseGeometry (d : FirstHeight.Data Y E m) (p : Plan m 0)
    (Z : FirstHeight.SourceSpace Y E m) : Prop where
  past_memory : ∀ i,i<p.2.2.current → p.2.2.memory i=true
  current_memory : p.2.2.readout=true → p.2.2.memory p.2.2.current=true
  inner_current : |LatchChain.u (Inner.radius Inner.absoluteDepth (Fin.last (Inner.absoluteDepth+1)))
    (d.innerDirections p.1 p.2.2.current (Fin.last (Inner.absoluteDepth+1)))
    (tasks Y E (m+1) (Inner.absoluteDepth+2) (CensoredFirstHeight.lower Z)
      p.2.2.current (Fin.last (Inner.absoluteDepth+1)))|≤1/8
  inner_last : |LatchChain.u (Inner.radius Inner.absoluteDepth (Fin.last (Inner.absoluteDepth+1)))
    (d.innerDirections p.1 (Fin.last m) (Fin.last (Inner.absoluteDepth+1)))
    (tasks Y E (m+1) (Inner.absoluteDepth+2) (CensoredFirstHeight.lower Z)
      (Fin.last m) (Fin.last (Inner.absoluteDepth+1)))|≤1/8
  inner_hidden : ∀ i,p.2.2.memory i=false → ∀ j,
    |LatchChain.u (Inner.radius Inner.absoluteDepth j) (d.innerDirections p.1 i j)
      (tasks Y E (m+1) (Inner.absoluteDepth+2) (CensoredFirstHeight.lower Z) i j)|≤1/8
  current_gate : p.2.2.readout=false → InverseGate.gateArg (d.a p.1 p.2.2.current)
    (numerical Y E (m+1) (Inner.absoluteDepth+2) (CensoredFirstHeight.lower Z))≤1/4
  outer_current : |LatchChain.u (Inner.radius (FirstHeight.depth (m+1)) (Fin.last (FirstHeight.depth (m+1)+1)))
    (d.outerDirections p.1 (Fin.last (FirstHeight.depth (m+1)+1)))
    (CensoredFirstHeight.blockMap (Y := Y) (E := E) (m := m) p.1 Z (Fin.last (FirstHeight.depth (m+1)+1)))|≤1/8
  outer_last : |LatchChain.u (Inner.radius (FirstHeight.depth (m+1)) (Fin.last (FirstHeight.depth (m+1)+1)))
    (d.outerDirections (Fin.last 7) (Fin.last (FirstHeight.depth (m+1)+1)))
    (CensoredFirstHeight.blockMap (Y := Y) (E := E) (m := m) (Fin.last 7) Z (Fin.last (FirstHeight.depth (m+1)+1)))|≤1/8
  outer_hidden : ∀ i,p.2.1 i=false → ∀ j,
    |LatchChain.u (Inner.radius (FirstHeight.depth (m+1)) j) (d.outerDirections i j)
      (CensoredFirstHeight.blockMap (Y := Y) (E := E) (m := m) i Z j)|≤1/8

def maskedSelf (K : ℝ) (t : ℕ) (d : Data Y E H m (t+1)) (known : Fin 8 → Bool)
    (i : Fin 8) (Z : Space Y E H m (t+1)) : ℝ :=
  if known i then Localized.potential (radius m K t) (width m t) (centers K d i)
    (parent (Space Y E H m t) (H t) Z i)
  else Localized.publicPotential (radius m K t) (parent (Space Y E H m t) (H t) Z i)

def scalar (K : ℝ) : (t : ℕ) → Plan m t → Data Y E H m t → Space Y E H m t → ℝ
  | 0,p,d => CensoredFirstHeight.scalar d p.1 p.2.1 p.2.2
  | t+1,p,d => FrontierOracleScalar.scalar p.1
      (baseline K t ∘ lower (Space Y E H m t) (H t)) (spacing m K t)
      (fun i => HigherHierarchy.scalar K t (d.children i) ∘ lower (Space Y E H m t) (H t))
      (fun i => outgoing K t (d.children i) ∘ lower (Space Y E H m t) (H t)) (maskedSelf K t d p.2.1)
      (fun i Z => nodeIncoming (radius m K t) (width m t) (centers K d) Z i)
      (fun i Z => nodePorts (width m t) (centers K d) Z i)
      (scalar K t p.2.2 (d.children p.1) ∘ lower (Space Y E H m t) (H t))

def Geometry (K : ℝ) : (t : ℕ) → Plan m t → Data Y E H m t → Space Y E H m t → Prop
  | 0,p,d,Z => BaseGeometry d p Z
  | t+1,p,d,Z =>
      3*width m t<‖parent (Space Y E H m t) (H t) Z p.1-centers K d p.1‖ ∧
      3*width m t<‖parent (Space Y E H m t) (H t) Z (Fin.last 7)-centers K d (Fin.last 7)‖ ∧
      (∀ i,p.2.1 i=false → 3*width m t<‖parent (Space Y E H m t) (H t) Z i-centers K d i‖) ∧
      Geometry K t p.2.2 (d.children p.1) (lower (Space Y E H m t) (H t) Z)

theorem maskedSelf_contDiff {K : ℝ} (hK : 0<K) (t : ℕ) (d : Data Y E H m (t+1))
    (known : Fin 8 → Bool) (i : Fin 8) : ContDiff ℝ 2 (maskedSelf K t d known i) := by
  unfold maskedSelf
  split_ifs
  · exact (((Localized.localized_contDiff (radius_pos m hK t) (width_pos m t) (centers K d i)).1).comp
      (parentAt (Space Y E H m t) (H t) i).contDiff).of_le (by decide)
  · exact (Localized.publicPotential_contDiff (radius_pos m hK t) 2).comp
      (parentAt (Space Y E H m t) (H t) i).contDiff

theorem scalar_contDiff {K : ℝ} (hK : 0<K) :
    (t : ℕ) → (p : Plan m t) → (d : Data Y E H m t) → ContDiff ℝ 2 (scalar K t p d)
  | 0,p,d => CensoredFirstHeight.scalar_contDiff d p.1 p.2.1 p.2.2
  | t+1,p,d => FrontierOracleScalar.scalar_contDiff p.1 _ _ _ _ _ _ _ _
      (((baseline_contDiff hK t).comp (lower (Space Y E H m t) (H t)).contDiff).of_le (by decide))
      (fun i => ((HigherHierarchy.scalar_contDiff hK t (d.children i)).comp
        (lower (Space Y E H m t) (H t)).contDiff).of_le (by decide))
      (fun i => ((outgoing_contDiff hK t (d.children i)).comp
        (lower (Space Y E H m t) (H t)).contDiff).of_le (by decide))
      (maskedSelf_contDiff hK t d p.2.1)
      (fun i => (nodeIncoming_contDiff (radius_pos m hK t) (width_pos m t) (centers K d) i).of_le (by decide))
      (fun i => (nodePorts_contDiff (radius_pos m hK t) (width_pos m t) (centers K d) i).of_le (by decide))
      ((scalar_contDiff hK t p.2.2 (d.children p.1)).comp (lower (Space Y E H m t) (H t)).contDiff)

theorem base_richJet_eq (p : Plan m 0) (d : FirstHeight.Data Y E m)
    (Z : FirstHeight.SourceSpace Y E m) (hg : BaseGeometry d p Z) :
    richJet (FirstHeight.sourceNode d) Z=richJet (CensoredFirstHeight.scalar d p.1 p.2.1 p.2.2) Z := by
  apply CensoredFirstHeight.richJet_eq d p.1 p.2.1 p.2.2 Z
  · exact MemoryMissJets.port_zero_near (FirstHeight.depth (m+1)+1)
      (CensoredFirstHeight.blockMap (Y := Y) (E := E) (m := m) p.1)
      (d.outerDirections p.1) (Inner.radius (FirstHeight.depth (m+1))) Z hg.outer_current
  · exact MemoryMissJets.port_zero_near (Inner.absoluteDepth+1)
      ((Inner.taskProjection (Y := Y) (E := E) (m+1) Inner.absoluteDepth (Fin.last m)).comp
        (CensoredFirstHeight.lower (Y := Y) (E := E) (m := m)))
      (d.innerDirections p.1 (Fin.last m)) (Inner.radius Inner.absoluteDepth) Z hg.inner_last
  · exact hg.outer_hidden
  · apply SecondJetPullback.richJet_comp_linear_eq (CensoredFirstHeight.lower (Y := Y) (E := E) (m := m))
      ((FirstHeight.children_contDiff d p.1).of_le (by decide))
      ((CensoredLeaf.objective_contDiff (Y := Y) (E := E) (by omega) p.2.2 (d.A p.1)
        (d.b p.1,d.a p.1,d.innerDirections p.1)).of_le (by decide))
    exact CensoredLeaf.full_leaf_richJet_eq (by omega) p.2.2 (d.A p.1)
      (d.b p.1,d.a p.1,d.innerDirections p.1) (CensoredFirstHeight.lower Z)
      hg.past_memory hg.current_memory
      (MemoryMissJets.port_zero_near (Inner.absoluteDepth+1)
        (Inner.taskProjection (Y := Y) (E := E) (m+1) Inner.absoluteDepth p.2.2.current)
        (d.innerDirections p.1 p.2.2.current) (Inner.radius Inner.absoluteDepth)
        (CensoredFirstHeight.lower Z) hg.inner_current) hg.inner_hidden hg.current_gate

theorem outgoing_zero_near (K : ℝ) (t : ℕ) (p : Plan m t) (d : Data Y E H m t)
    (Z : Space Y E H m t) (hg : Geometry K t p d Z) :
    outgoing K t d =ᶠ[𝓝 Z] fun _ => 0 := by
  cases t with
  | zero =>
    exact MemoryMissJets.port_zero_near (FirstHeight.depth (m+1)+1)
      (CensoredFirstHeight.blockMap (Y := Y) (E := E) (m := m) (Fin.last 7))
      (d.outerDirections (Fin.last 7)) (Inner.radius (FirstHeight.depth (m+1))) Z hg.outer_last
  | succ t =>
    exact LocalizedMissJets.port_zero_near (parentAt (Space Y E H m t) (H t) (Fin.last 7))
      (centers K d (Fin.last 7)) Z (width_pos m t) hg.2.1

theorem maskedSelf_near (K : ℝ) (t : ℕ) (d : Data Y E H m (t+1)) (known : Fin 8 → Bool)
    (Z : Space Y E H m (t+1)) (i : Fin 8)
    (hm : known i=false → 3*width m t<‖parent (Space Y E H m t) (H t) Z i-centers K d i‖) :
    (fun W => Localized.potential (radius m K t) (width m t) (centers K d i)
      (parent (Space Y E H m t) (H t) W i)) =ᶠ[𝓝 Z] maskedSelf K t d known i := by
  cases hi : known i with
  | true =>
    apply Filter.Eventually.of_forall
    intro W
    simp only [maskedSelf,hi,if_true]
  | false =>
    have hn := LocalizedMissJets.potential_eq_public_near (parentAt (Space Y E H m t) (H t) i)
      (radius m K t) (centers K d i) Z (width_pos m t) (hm hi)
    filter_upwards [hn] with W hW
    simpa only [maskedSelf,hi,Bool.false_eq_true,if_false] using hW

theorem richJet_eq {K : ℝ} (hK : 0<K) :
    (t : ℕ) → (p : Plan m t) → (d : Data Y E H m t) → (Z : Space Y E H m t) →
      Geometry K t p d Z → richJet (HigherHierarchy.scalar K t d) Z=richJet (scalar K t p d) Z
  | 0,p,d,Z,hg => base_richJet_eq p d Z hg
  | t+1,p,d,Z,hg => by
      rw [HigherHierarchy.scalar,NodeFrontierBridge.higher_node_eq]
      apply FrontierOracleScalar.node_censored_richJet p.1 _ _ _ _ _ _ _ _ _
        (((baseline_contDiff hK t).comp (lower (Space Y E H m t) (H t)).contDiff).of_le (by decide))
        (fun i => ((HigherHierarchy.scalar_contDiff hK t (d.children i)).comp
          (lower (Space Y E H m t) (H t)).contDiff).of_le (by decide))
        (fun i => ((outgoing_contDiff hK t (d.children i)).comp
          (lower (Space Y E H m t) (H t)).contDiff).of_le (by decide))
        (maskedSelf_contDiff hK t d p.2.1)
        (fun i => (nodeIncoming_contDiff (radius_pos m hK t) (width_pos m t) (centers K d) i).of_le (by decide))
        (fun i => (nodePorts_contDiff (radius_pos m hK t) (width_pos m t) (centers K d) i).of_le (by decide))
        ((scalar_contDiff hK t p.2.2 (d.children p.1)).comp (lower (Space Y E H m t) (H t)).contDiff) Z
      · exact LocalizedMissJets.port_zero_near (parentAt (Space Y E H m t) (H t) p.1)
          (centers K d p.1) Z (width_pos m t) hg.1
      · exact (outgoing_zero_near K t p.2.2 (d.children p.1)
          (lower (Space Y E H m t) (H t) Z) hg.2.2.2).comp_tendsto
          (lower (Space Y E H m t) (H t)).continuous.continuousAt.tendsto
      · exact fun i => maskedSelf_near K t d p.2.1 Z i (hg.2.2.1 i)
      · exact SecondJetPullback.richJet_comp_linear_eq (lower (Space Y E H m t) (H t))
          ((HigherHierarchy.scalar_contDiff hK t (d.children p.1)).of_le (by decide))
          (scalar_contDiff hK t p.2.2 (d.children p.1))
          (richJet_eq hK t p.2.2 (d.children p.1) (lower (Space Y E H m t) (H t) Z) hg.2.2.2)

end GradientHessian.CensoredHierarchy
