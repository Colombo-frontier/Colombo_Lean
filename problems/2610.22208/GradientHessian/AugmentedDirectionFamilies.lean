import GradientHessian.AugmentedHitContainment
import GradientHessian.DirectionFactorTests

/-! Actual center, old-memory and inner-memory repair hits are contained
in the finite external-data arrays. Every replay and test premise is
discharged by the literal raw factor and the controller's source action. -/

noncomputable section
namespace GradientHessian.AugmentedDirectionFamilies
open Classical HigherHierarchy HierarchyAddresses RawHierarchy
  FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
  RawDirection AugmentedPolicy AugmentedVisibleQueries
open DirectionPolicyReplay (Point centerStop oldStop)

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

def hitBy (t : ℕ) (blocked : Action t (4096*J^2) → Bool)
    (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t)
      (Ordinary d J E H t ell) (Rich d J E H t ell))
    (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) (x : Raw d n r J E H t × Seed) : Prop :=
  AugmentedPolicy.hitBy P B fallback t policy K blocked stop N fuel s₀ x

section Center
variable (h depth : ℕ) (w : Word depth) (i : Fin 8)
variable (policy : Machine.Policy (Seed × Packet d J E H (h+1+depth) ell) S (Point d J E H (h+1+depth))
  (Ordinary d J E H (h+1+depth) ell) (Rich d J E H (h+1+depth) ell))

def centerQuery (K : ℝ) (N fuel : ℕ) (s₀ : State (h+1+depth+1) (4096*J^2+1) ell)
    (x : RawCenterFactor.Rest d n r J E H h depth × Seed)
    (q : Fin (cap (J := J) (ell := ell) (h+1+depth) (CensoredDirection.addressedNode (h+1) depth w))) : H h :=
  localProjection (⟨h,by omega⟩ : Fin (h+1+depth)) i
    (query P B fallback (h+1+depth) (blockDirection (embed (h+1) depth w (.inr i))) (centerStop h depth w i)
      (RawCenterFactor.factor h depth w i) 0 policy (CensoredDirection.addressedNode (h+1) depth w) K N fuel s₀ x q)

theorem center_covered {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (h+1+depth+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell)
    (x : Raw d n r J E H (h+1+depth) × Seed)
    (hhit : hitBy P B fallback (h+1+depth) (blockDirection (embed (h+1) depth w (.inr i))) (centerStop h depth w i)
      policy K N fuel s₀ x) :
    ∃ q,‖centerQuery P B fallback h depth w i policy K N fuel s₀ ((RawCenterFactor.factor h depth w i x.1).2,x.2) q-
      radius (4096*J^2) K h • (RawCenterFactor.factor h depth w i x.1).1‖≤3*width (4096*J^2) h := by
  apply AugmentedVisibleQueries.hitBy_covered P B fallback (h+1+depth)
    (blockDirection (embed (h+1) depth w (.inr i))) (centerStop h depth w i)
    (RawCenterFactor.factor h depth w i) 0 policy (centerFactorAction h depth w i)
    (fun b hb => directionSlot_unique b _ _ (of_decide_eq_true hb) (centerFactorAction_slot h depth w i))
    (CensoredDirection.addressedNode (h+1) depth w)
    (fun v Z => ‖localProjection (⟨h,by omega⟩ : Fin (h+1+depth)) i Z-radius (4096*J^2) K h • v‖≤3*width (4096*J^2) h)
    K N fuel s₀ _ _ hs hell x hhit
  · intro raw seed steps hstop
    exact center_trajectory_eq P B fallback hK h depth w i raw _
      (by simp only [MeasurableEquiv.apply_symm_apply]) policy N s₀ hstop steps seed
  · intro raw s Z ht
    have hg := of_decide_eq_true ht
    have hh : h<h+1+depth := by omega
    change Visible (TaskState.retired s) (localNode (⟨h,hh⟩ : Fin (h+1+depth)) (centerPath h depth w)) ∧
      ¬GeometricDisclosure.NodeDisclosed s (localChild ⟨h,hh⟩ (centerPath h depth w) i) ∧
      ‖localProjection (⟨h,hh⟩ : Fin (h+1+depth)) i Z-
        localCenter K (assemble P B fallback (h+1+depth) raw) ⟨h,hh⟩ (centerPath h depth w) i‖≤3*width (4096*J^2) h at hg
    constructor
    · simpa only [centerFactorNode] using hg.1
    · simpa only [center_factor_test P B fallback] using hg.2.2

theorem centerQuery_measurable {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (h+1+depth+1) (4096*J^2+1) ell) (q) :
    Measurable (fun x => centerQuery (n := n) P B fallback h depth w i policy K N fuel s₀ x q) :=
  (localProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2)
    (⟨h,by omega⟩ : Fin (h+1+depth)) i).continuous.measurable.comp
      (query_measurable P B fallback (h+1+depth) (blockDirection (embed (h+1) depth w (.inr i))) (centerStop h depth w i)
        (RawCenterFactor.factor h depth w i) 0 policy (CensoredDirection.addressedNode (h+1) depth w) hK N fuel s₀ q)
end Center

section Old
variable (depth : ℕ) (w : Word depth) (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
variable (policy : Machine.Policy (Seed × Packet d J E H (0+depth) ell) S (Point d J E H (0+depth))
  (Ordinary d J E H (0+depth) ell) (Rich d J E H (0+depth) ell))

def oldQuery (K : ℝ) (N fuel : ℕ) (s₀ : State (0+depth+1) (4096*J^2+1) ell)
    (x : RawMemoryHierarchyFactor.OldRest d n r J E H depth × Seed)
    (q : Fin (cap (J := J) (ell := ell) (0+depth) (CensoredDirection.addressedNode 0 depth w))) : E :=
  oldRegisterProjection (0+depth) i j
    (query P B fallback (0+depth) (blockDirection (embed 0 depth w (.inl (i,j)))) (oldStop depth w i)
      (RawMemoryHierarchyFactor.oldFactor depth w i j) 0 policy (CensoredDirection.addressedNode 0 depth w) K N fuel s₀ x q)

theorem old_covered {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (0+depth+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell)
    (x : Raw d n r J E H (0+depth) × Seed)
    (hhit : hitBy P B fallback (0+depth) (blockDirection (embed 0 depth w (.inl (i,j)))) (oldStop depth w i) policy K N fuel s₀ x) :
    ∃ q,(1/8:ℝ) < |LatchChain.u (Inner.radius (FirstHeight.depth (4096*J^2+1)) j)
      (RawMemoryHierarchyFactor.oldFactor depth w i j x.1).1
      (oldQuery P B fallback depth w i j policy K N fuel s₀ ((RawMemoryHierarchyFactor.oldFactor depth w i j x.1).2,x.2) q)| := by
  apply AugmentedVisibleQueries.hitBy_covered P B fallback (0+depth)
    (blockDirection (embed 0 depth w (.inl (i,j)))) (oldStop depth w i)
    (RawMemoryHierarchyFactor.oldFactor depth w i j) 0 policy (oldFactorAction depth w i j)
    (fun b hb => directionSlot_unique b _ _ (of_decide_eq_true hb) (oldFactorAction_slot depth w i j))
    (CensoredDirection.addressedNode 0 depth w)
    (fun v Z => (1/8:ℝ) < |LatchChain.u (Inner.radius (FirstHeight.depth (4096*J^2+1)) j) v (oldRegisterProjection (0+depth) i j Z)|)
    K N fuel s₀ _ _ hs hell x hhit
  · intro raw seed steps hstop
    exact old_trajectory_eq P B fallback hK depth w i j raw _
      (by simp only [MeasurableEquiv.apply_symm_apply]) policy N s₀ hstop steps seed
  · intro raw s Z ht
    have hg := of_decide_eq_true ht
    change Visible (TaskState.retired s) (oldNode (oldPath depth w)) ∧
      ¬GeometricDisclosure.NodeDisclosed s (oldChild (oldPath depth w) i) ∧
      1/8 < |oldReadout (assemble P B fallback (0+depth) raw) (oldPath depth w) i j Z| at hg
    constructor
    · simpa only [oldFactorNode] using hg.1
    · simpa only [old_factor_test P B fallback] using hg.2.2

theorem oldQuery_measurable {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (0+depth+1) (4096*J^2+1) ell) (q) :
    Measurable (fun x => oldQuery (n := n) P B fallback depth w i j policy K N fuel s₀ x q) :=
  (oldRegisterProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2)
    (0+depth) i j).continuous.measurable.comp
      (query_measurable P B fallback (0+depth) (blockDirection (embed 0 depth w (.inl (i,j)))) (oldStop depth w i)
        (RawMemoryHierarchyFactor.oldFactor depth w i j) 0 policy (CensoredDirection.addressedNode 0 depth w) hK N fuel s₀ q)
end Old

section Inner
variable (depth : ℕ) (w : Word depth) (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
variable (policy : Machine.Policy (Seed × Packet d J E H (0+depth) ell) S (Point d J E H (0+depth))
  (Ordinary d J E H (0+depth) ell) (Rich d J E H (0+depth) ell))

def innerQuery (K : ℝ) (N fuel : ℕ) (s₀ : State (0+depth+1) (4096*J^2+1) ell)
    (x : RawMemoryHierarchyFactor.InnerRest d n r J E H depth × Seed)
    (q : Fin (cap (J := J) (ell := ell) (0+depth) (leafNode (leafEquiv (0+depth) (prependSlot 0 depth w i))))) : E :=
  innerRegisterProjection (0+depth) j k
    (query P B fallback (0+depth) (blockDirection (embed 0 depth w (.inr (i,j,k)))) (taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j)
      (RawMemoryHierarchyFactor.innerFactor depth w i j k) 0 policy (leafNode (leafEquiv (0+depth) (prependSlot 0 depth w i))) K N fuel s₀ x q)

theorem inner_covered {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (0+depth+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell)
    (x : Raw d n r J E H (0+depth) × Seed)
    (hhit : hitBy P B fallback (0+depth) (blockDirection (embed 0 depth w (.inr (i,j,k))))
      (taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j) policy K N fuel s₀ x) :
    ∃ q,(1/8:ℝ) < |LatchChain.u (Inner.radius Inner.absoluteDepth k) (RawMemoryHierarchyFactor.innerFactor depth w i j k x.1).1
      (innerQuery P B fallback depth w i j k policy K N fuel s₀ ((RawMemoryHierarchyFactor.innerFactor depth w i j k x.1).2,x.2) q)| := by
  apply AugmentedVisibleQueries.hitBy_covered P B fallback (0+depth)
    (blockDirection (embed 0 depth w (.inr (i,j,k))))
    (taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j)
    (RawMemoryHierarchyFactor.innerFactor depth w i j k) 0 policy (innerFactorAction depth w i j k)
    (fun b hb => directionSlot_unique b _ _ (of_decide_eq_true hb) (innerFactorAction_slot depth w i j k))
    (leafNode (leafEquiv (0+depth) (prependSlot 0 depth w i)))
    (fun v Z => (1/8:ℝ) < |LatchChain.u (Inner.radius Inner.absoluteDepth k) v (innerRegisterProjection (0+depth) j k Z)|)
    K N fuel s₀ _ _ hs hell x hhit
  · intro raw seed steps hstop
    exact inner_trajectory_eq P B fallback hK depth w i j k raw _
      (by simp only [MeasurableEquiv.apply_symm_apply]) policy N s₀ hstop steps seed
  · intro raw s Z ht
    have hg := of_decide_eq_true ht
    change TaskState.current s=some (leafEquiv (0+depth) (prependSlot 0 depth w i)) ∧
      ¬GeometricDisclosure.TaskDisclosed s (leafEquiv (0+depth) (prependSlot 0 depth w i)) j ∧
      1/8 < |innerReadout (assemble P B fallback (0+depth) raw) (leafEquiv (0+depth) (prependSlot 0 depth w i)) j k Z| at hg
    exact ⟨⟨_,hg.1,by intro a; rfl⟩,by simpa only [inner_factor_test P B fallback] using hg.2.2⟩

theorem innerQuery_measurable {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (0+depth+1) (4096*J^2+1) ell) (q) :
    Measurable (fun x => innerQuery (n := n) P B fallback depth w i j k policy K N fuel s₀ x q) :=
  (innerRegisterProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2)
    (0+depth) j k).continuous.measurable.comp
      (query_measurable P B fallback (0+depth) (blockDirection (embed 0 depth w (.inr (i,j,k))))
        (taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j)
        (RawMemoryHierarchyFactor.innerFactor depth w i j k) 0 policy (leafNode (leafEquiv (0+depth) (prependSlot 0 depth w i))) hK N fuel s₀ q)
end Inner

end GradientHessian.AugmentedDirectionFamilies


